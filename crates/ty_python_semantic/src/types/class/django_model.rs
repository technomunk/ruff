use ruff_db::{PythonFile, files::File, parsed::parsed_module, source::source_text};
use ruff_python_ast as ast;
use ruff_python_ast::name::Name;
use ty_module_resolver::{
    ImportingFile, KnownModule, Module, ModuleName, ResolverFile, file_to_module, list_modules,
    resolve_module,
};

use crate::{
    Db, FxIndexMap, FxIndexSet, Program, ProgramEnvironment,
    place::{imported_symbol, known_module_symbol},
    types::{
        CallableType, ClassLiteral, IntersectionType, KnownClass, Parameter, Parameters, Signature,
        Type, TypeQualifiers, TypedDictType, UnionType,
        class::StaticClassLiteral,
        member::class_member,
        typed_dict::{TypedDictSchema, functional_typed_dict_field},
    },
};
use ty_python_core::{
    ProgramFile, SemanticIndex, global_scope, scope::NodeWithScopeRef, semantic_index,
};

/// The category of a Django model field, used to determine the Python type
/// that accessing the field on a model instance should produce.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, salsa::SalsaValue, get_size2::GetSize)]
pub(super) enum DjangoFieldKind {
    // character / text
    Char,
    Binary,
    // numeric
    Integer,
    Float,
    Bool,
    Decimal,
    Auto,
    // date / time
    Date,
    DateTime,
    Time,
    // other scalars
    Uuid,
    Json,
    File,
    Image,
    // relational
    ForeignKey,
    OneToOne,
    ManyToMany,
    GenericForeignKey,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum DjangoLookupExpectedType<'db> {
    Expected(Type<'db>),
    Dynamic,
    UnknownField,
}

pub(crate) enum DjangoRelationLookup {
    Valid,
    NotRelation,
    UnknownField,
    Dynamic,
}

pub(crate) enum DjangoBulkFieldLookup {
    Valid,
    UnknownField,
    PrimaryKey,
    NonConcrete,
}

const MANAGER_METHODS_RETURNING_QUERYSET: &[&str] = &[
    "alias",
    "all",
    "annotate",
    "complex_filter",
    "defer",
    "difference",
    "distinct",
    "exclude",
    "extra",
    "filter",
    "intersection",
    "none",
    "only",
    "order_by",
    "prefetch_related",
    "reverse",
    "select_for_update",
    "select_related",
    "union",
    "using",
];

/// Returns `file` as seen by the program of `env`.
fn program_file<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    file: File,
) -> ProgramFile<'db> {
    env.program(db).program_file(db, file)
}

fn python_file<'db>(db: &'db dyn Db, env: &ProgramEnvironment<'db>, file: File) -> PythonFile<'db> {
    program_file(db, env, file).python_file(db)
}

fn resolver_file<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    file: File,
) -> ResolverFile<'db> {
    program_file(db, env, file).resolver_file(db)
}

fn as_importing_file<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    file: File,
) -> ImportingFile<'db> {
    ImportingFile::ResolverFile(resolver_file(db, env, file))
}

pub(crate) fn django_manager_method_returns_queryset(method_name: &str) -> bool {
    MANAGER_METHODS_RETURNING_QUERYSET.contains(&method_name)
}

fn is_django_settings_instance<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    ty: Type<'db>,
) -> bool {
    ty.nominal_class(db, env).is_some_and(|class| {
        class
            .iter_mro(db)
            .filter_map(super::super::class_base::ClassBase::into_class)
            .filter_map(|base| base.static_class_literal(db).map(|(base, _)| base))
            .any(|base| {
                matches!(base.name(db).as_str(), "LazySettings" | "Settings")
                    && file_to_module(db, resolver_file(db, env, base.file(db))).is_some_and(
                        |module| {
                            matches!(
                                module.name(db).as_str(),
                                "django.conf" | "django.conf.__init__"
                            )
                        },
                    )
            })
    })
}

fn module_name_ends_with_settings<'db>(db: &'db dyn Db, module: Module<'db>) -> bool {
    module.name(db).components().last() == Some("settings")
}

#[salsa::tracked(returns(deref), heap_size=ruff_memory_usage::heap_size)]
fn django_project_settings_modules<'db>(
    db: &'db dyn Db,
    program: Program<'db>,
    file: File,
) -> Box<[Module<'db>]> {
    let env = &ProgramEnvironment::from_program(program);
    if file_to_module(db, resolver_file(db, env, file)).is_none() {
        return Box::default();
    }

    list_modules(db, env.program(db).resolver_environment(db))
        .iter()
        .copied()
        .filter(|&module| {
            module_is_project_code(db, module)
                && (module_name_ends_with_settings(db, module)
                    || module_path_contains_component(db, module, "settings"))
        })
        .collect()
}

fn django_settings_module_member<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    module: Module<'db>,
    name: &str,
) -> Option<Type<'db>> {
    let file = module.file(db)?;
    class_member(db, global_scope(db, program_file(db, env, file)), name)
        .ignore_possibly_undefined()
}

fn django_settings_module_string_literal_member<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    module: Module<'db>,
    name: &str,
) -> Option<String> {
    let file = module.file(db)?;
    let module = parsed_module(db, python_file(db, env, file)).load(db);

    for stmt in module.suite() {
        let value = match stmt {
            ast::Stmt::Assign(assign) => {
                let [target] = assign.targets.as_slice() else {
                    continue;
                };
                let ast::Expr::Name(target_name) = target else {
                    continue;
                };
                if target_name.id.as_str() != name {
                    continue;
                }
                assign.value.as_ref()
            }
            ast::Stmt::AnnAssign(ann_assign) => {
                let ast::Expr::Name(target_name) = ann_assign.target.as_ref() else {
                    continue;
                };
                if target_name.id.as_str() != name {
                    continue;
                }
                let Some(value) = ann_assign.value.as_deref() else {
                    continue;
                };
                value
            }
            _ => continue,
        };

        if let ast::Expr::StringLiteral(string_lit) = value {
            return Some(string_lit.value.to_str().to_string());
        }
    }

    None
}

fn django_settings_modules_imported_by_file<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    file: File,
) -> Vec<Module<'db>> {
    let module = parsed_module(db, python_file(db, env, file)).load(db);
    let mut modules = Vec::new();

    for stmt in module.suite() {
        match stmt {
            ast::Stmt::Import(import) => {
                for alias in &import.names {
                    let Some(module_name) = ModuleName::new(alias.name.as_str()) else {
                        continue;
                    };
                    let Some(module) =
                        resolve_module(db, as_importing_file(db, env, file), &module_name)
                    else {
                        continue;
                    };
                    if module_name_ends_with_settings(db, module) && !modules.contains(&module) {
                        modules.push(module);
                    }
                }
            }
            ast::Stmt::ImportFrom(import_from) => {
                let Ok(module_name) = ModuleName::from_import_statement(
                    db,
                    as_importing_file(db, env, file),
                    import_from,
                ) else {
                    continue;
                };
                if module_name.components().last() == Some("settings")
                    && let Some(module) =
                        resolve_module(db, as_importing_file(db, env, file), &module_name)
                    && !modules.contains(&module)
                {
                    modules.push(module);
                }
            }
            _ => {}
        }
    }

    modules
}

pub(crate) fn django_settings_member_type<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    file: File,
    settings_ty: Type<'db>,
    name: &str,
) -> Option<Type<'db>> {
    if !is_django_settings_instance(db, env, settings_ty) {
        return None;
    }

    for module in django_settings_modules_imported_by_file(db, env, file) {
        if let Some(ty) = django_settings_module_member(db, env, module, name) {
            return Some(ty);
        }
    }

    for module in django_project_settings_modules(db, env.program(db), file)
        .iter()
        .copied()
    {
        if let Some(ty) = django_settings_module_member(db, env, module, name) {
            return Some(ty);
        }
    }

    let global_settings_module = resolve_module(
        db,
        as_importing_file(db, env, file),
        &ModuleName::new_static("django.conf.global_settings").unwrap(),
    )?;
    django_settings_module_member(db, env, global_settings_module, name)
}

pub(crate) fn is_django_querydict_instance<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    ty: Type<'db>,
) -> bool {
    ty.nominal_class(db, env).is_some_and(|class| {
        class
            .iter_mro(db)
            .filter_map(super::super::class_base::ClassBase::into_class)
            .filter_map(|base| base.static_class_literal(db).map(|(base, _)| base))
            .any(|base| {
                base.name(db).as_str() == "QueryDict"
                    && file_to_module(db, resolver_file(db, env, base.file(db))).is_some_and(
                        |module| {
                            matches!(
                                module.name(db).as_str(),
                                "django.http" | "django.http.request"
                            )
                        },
                    )
            })
    })
}

/// A single Django model field declaration with its resolved Python type information.
#[derive(Debug, Clone, PartialEq, Eq, Hash, salsa::SalsaValue, get_size2::GetSize)]
#[expect(
    clippy::struct_excessive_bools,
    reason = "each flag mirrors a distinct Django field attribute; collapsing them into enums \
              would obscure the 1:1 mapping to Django's field options"
)]
pub(super) struct DjangoFieldInfo<'db> {
    pub name: Name,
    pub file: File,
    pub class_name: String,
    pub kind: DjangoFieldKind,
    pub nullable: bool,
    pub primary_key: bool,
    pub has_choices: bool,
    pub value_type_override: Option<Type<'db>>,
    /// For relation fields, the resolved instance type of the target model.
    /// `None` for non-relational fields.
    pub related_model: Option<Type<'db>>,
    pub related_model_is_auth_user: bool,
    related_target: Option<DjangoRelationTarget>,
    pub related_name: Option<Name>,
    pub related_query_name: Option<Name>,
    pub to_field: Option<Name>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, salsa::SalsaValue, get_size2::GetSize)]
enum DjangoRelationTarget {
    AuthUser,
    SelfModel,
    Name(Name),
    Dotted {
        app_label: String,
        model_name: String,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, salsa::SalsaValue, get_size2::GetSize)]
struct DjangoReverseMemberInfo<'db> {
    target_model: StaticClassLiteral<'db>,
    name: Name,
    query_name: Name,
    source_model: StaticClassLiteral<'db>,
    source_file: File,
    kind: DjangoFieldKind,
}

#[expect(
    clippy::boxed_local,
    reason = "the signature must match the salsa cycle-recovery function's value type"
)]
fn django_reverse_members_cycle_recover<'db>(
    _db: &'db dyn Db,
    _cycle: &salsa::Cycle,
    previous: &[DjangoReverseMemberInfo<'db>],
    _current: Box<[DjangoReverseMemberInfo<'db>]>,
) -> Box<[DjangoReverseMemberInfo<'db>]> {
    let _ = previous;
    Box::default()
}

fn django_reverse_member_instance_type<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    reverse_member: &DjangoReverseMemberInfo<'db>,
) -> Option<Type<'db>> {
    match reverse_member.kind {
        DjangoFieldKind::OneToOne => Some(Type::instance(
            db,
            env,
            reverse_member
                .source_model
                .apply_optional_specialization(db, None),
        )),
        DjangoFieldKind::ForeignKey | DjangoFieldKind::ManyToMany => Some(
            synthesize_reverse_related_manager_instance(db, env, reverse_member.source_model),
        ),
        _ => None,
    }
}

/// Return an instance of the stdlib class `module.class_name`, falling back to `Unknown`
/// if the class cannot be resolved in typeshed.
pub(crate) fn resolve_stdlib_instance<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    module: KnownModule,
    class_name: &str,
) -> Type<'db> {
    known_module_symbol(db, env, module, class_name)
        .place
        .ignore_possibly_undefined()
        .and_then(|ty| ty.to_instance_approximation(db, env))
        .unwrap_or_else(Type::unknown)
}

/// Resolve a symbol from a third-party Django module if that module is available.
fn resolve_django_symbol<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    importing_file: File,
    module_name: &'static str,
    symbol: &str,
) -> Option<Type<'db>> {
    let module_name = ModuleName::new_static(module_name)?;
    let module = resolve_module(db, as_importing_file(db, env, importing_file), &module_name)?;
    imported_symbol(
        db,
        env,
        module.file(db).map(|file| program_file(db, env, file)),
        symbol,
        None,
    )
    .place
    .ignore_possibly_undefined()
}

fn specialize_class_instance<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    ty: Type<'db>,
    specialization: &[Type<'db>],
) -> Option<Type<'db>> {
    let Type::ClassLiteral(class) = ty else {
        return None;
    };

    Some(Type::instance(
        db,
        env,
        class.apply_specialization(db, |generic_context| {
            if generic_context.len(db) == specialization.len() {
                generic_context.specialize(db, specialization)
            } else {
                generic_context.unknown_specialization(db, None)
            }
        }),
    ))
}

fn synthesize_manager_instance<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    importing_file: File,
    model_instance: Type<'db>,
) -> Type<'db> {
    let Some(manager_class) =
        resolve_django_symbol(db, env, importing_file, "django.db.models", "Manager").or_else(
            || {
                resolve_django_symbol(
                    db,
                    env,
                    importing_file,
                    "django.db.models.manager",
                    "Manager",
                )
            },
        )
    else {
        return Type::unknown();
    };

    specialize_class_instance(db, env, manager_class, &[model_instance])
        .unwrap_or_else(Type::unknown)
}

fn synthesize_many_related_manager_instance<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    importing_file: File,
    model_instance: Type<'db>,
) -> Type<'db> {
    let Some(manager_class) = resolve_django_symbol(
        db,
        env,
        importing_file,
        "django.db.models.fields.related_descriptors",
        "ManyRelatedManager",
    ) else {
        return synthesize_manager_instance(db, env, importing_file, model_instance);
    };

    let related_manager =
        specialize_class_instance(db, env, manager_class, &[model_instance, Type::unknown()])
            .unwrap_or_else(Type::unknown);

    let Some(model_class) = static_class_from_instance(db, env, model_instance) else {
        return related_manager;
    };
    let Some(default_manager_protocol) =
        first_declared_manager_queryset_protocol(db, env, model_class)
    else {
        return related_manager;
    };

    IntersectionType::from_two_elements(db, env, related_manager, default_manager_protocol)
}

fn synthesize_reverse_related_manager_instance<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    source_model: StaticClassLiteral<'db>,
) -> Type<'db> {
    let source_instance = Type::instance(
        db,
        env,
        source_model.apply_optional_specialization(db, None),
    );
    let related_manager =
        synthesize_manager_instance(db, env, source_model.file(db), source_instance);

    let Some(default_manager_protocol) =
        first_declared_manager_queryset_protocol(db, env, source_model)
    else {
        return related_manager;
    };

    IntersectionType::from_two_elements(db, env, related_manager, default_manager_protocol)
}

pub(crate) fn static_class_from_instance<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    ty: Type<'db>,
) -> Option<StaticClassLiteral<'db>> {
    if let Type::Intersection(intersection) = ty {
        return intersection
            .positive(db)
            .iter()
            .find_map(|element| static_class_from_instance(db, env, *element));
    }

    let class = ty.nominal_class(db, env)?;
    let (class, _) = class.static_class_literal(db)?;
    Some(class)
}

fn django_relation_targets_model<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    source_model: StaticClassLiteral<'db>,
    field: &DjangoFieldInfo<'db>,
    target_model: StaticClassLiteral<'db>,
) -> bool {
    if field.related_model_is_auth_user {
        if let Some(auth_user_model) =
            django_auth_user_model_class(db, env.program(db), target_model.file(db))
        {
            return auth_user_model == target_model;
        }

        return target_model.name(db).as_str().eq_ignore_ascii_case("User");
    }

    field
        .related_model
        .and_then(|related_model| static_class_from_instance(db, env, related_model))
        == Some(target_model)
        || field.related_target.as_ref().is_some_and(|target| {
            django_relation_target_matches_model(db, env, source_model, target, target_model)
        })
}

fn target_model_for_relation_field<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    source_model: StaticClassLiteral<'db>,
    field: &DjangoFieldInfo<'db>,
) -> Option<StaticClassLiteral<'db>> {
    if field.related_model_is_auth_user {
        return django_auth_user_model_class(db, env.program(db), field.file);
    }

    if let Some(related_model) = field.related_model {
        return static_class_from_instance(db, env, related_model);
    }

    let target = field.related_target.as_ref()?;
    match target {
        DjangoRelationTarget::AuthUser => {
            django_auth_user_model_class(db, env.program(db), field.file)
        }
        DjangoRelationTarget::SelfModel => Some(source_model),
        DjangoRelationTarget::Name(name) => {
            let models_module = django_models_module_for_file(db, env, field.file)?;
            if let Some(model) = django_model_modules_in_models_module(db, models_module)
                .iter()
                .copied()
                .find_map(|module| {
                    if !module_defines_class_named(db, env.program(db), module, name.clone()) {
                        return None;
                    }
                    django_model_classes_in_module(db, env.program(db), module)
                        .iter()
                        .copied()
                        .find(|model| model.name(db) == name)
                })
            {
                return Some(model);
            }

            class_member(
                db,
                global_scope(db, program_file(db, env, field.file)),
                name.as_str(),
            )
            .ignore_possibly_undefined()
            .and_then(|ty| ty.to_class_type(db))
            .and_then(|class| class.static_class_literal(db).map(|(class, _)| class))
            .filter(|model| model.is_django_model(db))
        }
        DjangoRelationTarget::Dotted {
            app_label,
            model_name,
        } => django_model_named_in_project_app_label(
            db,
            env.program(db),
            field.file,
            Name::new(app_label),
            Name::new(model_name),
        ),
    }
}

fn lazy_target_model_for_relation_field<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    source_model: StaticClassLiteral<'db>,
    field: &DjangoFieldInfo<'db>,
) -> Option<StaticClassLiteral<'db>> {
    if let Some(related_model) = field.related_model {
        return static_class_from_instance(db, env, related_model);
    }

    match field.related_target.as_ref()? {
        DjangoRelationTarget::Name(name) => local_class_literal_by_name(db, env, field.file, name)
            .or_else(|| target_model_for_relation_field(db, env, source_model, field)),
        DjangoRelationTarget::Dotted { model_name, .. } => {
            local_class_literal_by_name(db, env, field.file, model_name)
        }
        _ => target_model_for_relation_field(db, env, source_model, field),
    }
}

fn django_relation_target_matches_model<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    source_model: StaticClassLiteral<'db>,
    target: &DjangoRelationTarget,
    target_model: StaticClassLiteral<'db>,
) -> bool {
    match target {
        DjangoRelationTarget::AuthUser => {
            if let Some(auth_user_model) =
                django_auth_user_model_class(db, env.program(db), target_model.file(db))
            {
                auth_user_model == target_model
            } else {
                target_model.name(db).as_str().eq_ignore_ascii_case("User")
            }
        }
        DjangoRelationTarget::SelfModel => source_model == target_model,
        DjangoRelationTarget::Name(name) => target_model.name(db) == name,
        DjangoRelationTarget::Dotted {
            app_label,
            model_name,
        } => {
            target_model
                .name(db)
                .as_str()
                .eq_ignore_ascii_case(model_name)
                && django_app_label_for_file(db, env, target_model.file(db))
                    .is_some_and(|target_app_label| target_app_label == *app_label)
        }
    }
}

fn is_django_manager_class<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    class: StaticClassLiteral<'db>,
) -> bool {
    if class.name(db).as_str() != "Manager" {
        return false;
    }

    file_to_module(db, resolver_file(db, env, class.file(db))).is_some_and(|module| {
        matches!(
            module.name(db).as_str(),
            "django.db.models" | "django.db.models.manager"
        )
    })
}

fn is_django_form_class<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    class: StaticClassLiteral<'db>,
) -> bool {
    matches!(
        class.name(db).as_str(),
        "BaseForm" | "Form" | "BaseModelForm" | "ModelForm"
    ) && file_to_module(db, resolver_file(db, env, class.file(db))).is_some_and(|module| {
        matches!(
            module.name(db).as_str(),
            "django.forms" | "django.forms.forms" | "django.forms.models"
        )
    })
}

fn is_django_form_field_instance<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    ty: Type<'db>,
) -> bool {
    ty.nominal_class(db, env).is_some_and(|class| {
        class
            .iter_mro(db)
            .filter_map(super::super::class_base::ClassBase::into_class)
            .filter_map(|base| base.static_class_literal(db).map(|(base, _)| base))
            .any(|base| {
                base.name(db).as_str() == "Field"
                    && file_to_module(db, resolver_file(db, env, base.file(db))).is_some_and(
                        |module| {
                            matches!(
                                module.name(db).as_str(),
                                "django.forms" | "django.forms.fields"
                            )
                        },
                    )
            })
    })
}

pub(crate) fn django_form_declared_field<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    class: StaticClassLiteral<'db>,
    field_name: &str,
) -> Option<Type<'db>> {
    if !class.iter_mro(db, None).any(|base| {
        base.into_class()
            .and_then(|class| class.static_class_literal(db))
            .is_some_and(|(class, _)| is_django_form_class(db, env, class))
    }) {
        return None;
    }

    for base in class.iter_mro(db, None) {
        let Some(base_class) = base.into_class() else {
            continue;
        };
        let Some((base_lit, _)) = base_class.static_class_literal(db) else {
            continue;
        };
        if is_django_form_class(db, env, base_lit) {
            break;
        }
        let Some(ty) =
            class_member(db, base_lit.body_scope(db), field_name).ignore_possibly_undefined()
        else {
            continue;
        };
        if is_django_form_field_instance(db, env, ty) {
            return Some(ty);
        }
    }

    None
}

fn is_manager_instance<'db>(db: &'db dyn Db, env: &ProgramEnvironment<'db>, ty: Type<'db>) -> bool {
    let Some(class) = ty.nominal_class(db, env) else {
        return false;
    };

    class
        .iter_mro(db)
        .filter_map(super::super::class_base::ClassBase::into_class)
        .filter_map(|base| base.static_class_literal(db).map(|(base, _)| base))
        .any(|base| is_django_manager_class(db, env, base))
}

#[salsa::tracked(returns(copy), cycle_initial=|_, _, _, _| false)]
fn is_django_queryset_like_class<'db>(
    db: &'db dyn Db,
    program: Program<'db>,
    class: StaticClassLiteral<'db>,
) -> bool {
    let env = &ProgramEnvironment::from_program(program);
    let class_name = class.name(db).as_str();
    if !matches!(
        class_name,
        "Manager" | "QuerySet" | "RelatedManager" | "ManyRelatedManager"
    ) {
        return false;
    }

    file_to_module(db, resolver_file(db, env, class.file(db))).is_some_and(|module| {
        matches!(
            module.name(db).as_str(),
            "django.db.models"
                | "django.db.models.manager"
                | "django.db.models.query"
                | "django.db.models.fields.related_descriptors"
        )
    })
}

pub(crate) fn is_django_queryset_instance<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    ty: Type<'db>,
) -> bool {
    if let Type::Intersection(intersection) = ty {
        return intersection
            .positive(db)
            .iter()
            .any(|element| is_django_queryset_instance(db, env, *element));
    }

    ty.nominal_class(db, env).is_some_and(|class| {
        class
            .iter_mro(db)
            .filter_map(super::super::class_base::ClassBase::into_class)
            .filter_map(|base| base.static_class_literal(db).map(|(base, _)| base))
            .any(|base| {
                base.name(db).as_str() == "QuerySet"
                    && file_to_module(db, resolver_file(db, env, base.file(db))).is_some_and(
                        |module| {
                            matches!(
                                module.name(db).as_str(),
                                "django.db.models" | "django.db.models.query"
                            )
                        },
                    )
            })
    })
}

pub(crate) fn is_django_queryset_or_manager_instance_by_name<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    ty: Type<'db>,
) -> bool {
    if let Type::Intersection(intersection) = ty {
        return intersection
            .positive(db)
            .iter()
            .any(|element| is_django_queryset_or_manager_instance_by_name(db, env, *element));
    }

    ty.nominal_class(db, env)
        .and_then(|class| class.static_class_literal(db).map(|(class, _)| class))
        .is_some_and(|class| {
            let class_name = class.name(db);
            let class_name = class_name.as_str().trim_start_matches('_');
            class_name.ends_with("QuerySet")
                || class_name.ends_with("Manager")
                || matches!(
                    class_name,
                    "QuerySet" | "Manager" | "RelatedManager" | "ManyRelatedManager"
                )
        })
}

#[salsa::tracked(returns(copy), cycle_initial=|_, _, _| false)]
fn is_django_queryset_or_manager_subclass<'db>(
    db: &'db dyn Db,
    class: StaticClassLiteral<'db>,
) -> bool {
    let class_name = class.name(db);
    let class_name = class_name.as_str().trim_start_matches('_');
    if class_name.ends_with("QuerySet") || class_name.ends_with("Manager") {
        return true;
    }

    class
        .iter_mro(db, None)
        .filter_map(super::super::class_base::ClassBase::into_class)
        .filter_map(|base| base.static_class_literal(db).map(|(base, _)| base))
        .any(|base| {
            matches!(
                base.name(db).as_str(),
                "Manager" | "QuerySet" | "RelatedManager" | "ManyRelatedManager"
            )
        })
}

fn decorator_name(decorator: &ast::Decorator) -> Option<&str> {
    let expression = match &decorator.expression {
        ast::Expr::Call(call) => &*call.func,
        expression => expression,
    };

    match expression {
        ast::Expr::Name(name) => Some(name.id.as_str()),
        ast::Expr::Attribute(attribute) => Some(attribute.attr.as_str()),
        _ => None,
    }
}

#[salsa::tracked(returns(copy), cycle_initial=|_, _, _, _| false)]
fn has_cacheops_hint_decorator<'db>(
    db: &'db dyn Db,
    program: Program<'db>,
    class: StaticClassLiteral<'db>,
) -> bool {
    let env = &ProgramEnvironment::from_program(program);
    let module = parsed_module(db, python_file(db, env, class.file(db))).load(db);
    let source = source_text(db, class.file(db));
    let has_ast_decorator = class
        .node(db, &module)
        .decorator_list
        .iter()
        .any(|decorator| {
            decorator_name(decorator) == Some("cacheops_hint")
                || source
                    .get(decorator.range.start().to_usize()..decorator.range.end().to_usize())
                    .is_some_and(|text| text.contains("cacheops_hint"))
        });

    has_ast_decorator
        || source.contains(&format!(
            "@cacheops_hint\nclass {}",
            class.name(db).as_str()
        ))
}

#[salsa::tracked(returns(copy), cycle_initial=|_, _, _, _| false)]
fn has_cacheops_hint_in_mro<'db>(
    db: &'db dyn Db,
    program: Program<'db>,
    class: StaticClassLiteral<'db>,
) -> bool {
    let env = &ProgramEnvironment::from_program(program);
    class
        .iter_mro(db, None)
        .filter_map(super::super::class_base::ClassBase::into_class)
        .filter_map(|base| base.static_class_literal(db).map(|(base, _)| base))
        .any(|base| has_cacheops_hint_decorator(db, env.program(db), base))
}

pub(super) fn synthesize_django_queryset_instance_member<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    class: StaticClassLiteral<'db>,
    name: &str,
) -> Option<Type<'db>> {
    if !matches!(name, "cache" | "invalidated_update" | "nocache")
        || !is_django_queryset_or_manager_subclass(db, class)
        || !has_cacheops_hint_in_mro(db, env.program(db), class)
    {
        return None;
    }

    let self_ty = Type::instance(db, env, class.apply_optional_specialization(db, None));
    cacheops_method_callable(db, env, name, self_ty).map(Type::Callable)
}

fn cacheops_method_callable<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    name: &str,
    self_ty: Type<'db>,
) -> Option<CallableType<'db>> {
    Some(match name {
        "invalidated_update" => CallableType::single(
            db,
            Signature::new(
                Parameters::standard([Parameter::keyword_variadic(Name::new_static("kwargs"))
                    .with_annotated_type(Type::any())]),
                KnownClass::Int.to_instance(db, env),
            ),
        ),
        "cache" => CallableType::single(
            db,
            Signature::new(
                Parameters::standard([
                    Parameter::positional_or_keyword(Name::new_static("ops"))
                        .with_annotated_type(Type::any())
                        .with_optional_default_type(Some(Type::none(db, env))),
                    Parameter::positional_or_keyword(Name::new_static("timeout"))
                        .with_annotated_type(UnionType::from_two_elements(
                            db,
                            env,
                            KnownClass::Int.to_instance(db, env),
                            Type::none(db, env),
                        ))
                        .with_optional_default_type(Some(Type::none(db, env))),
                    Parameter::positional_or_keyword(Name::new_static("lock"))
                        .with_annotated_type(UnionType::from_two_elements(
                            db,
                            env,
                            KnownClass::Bool.to_instance(db, env),
                            Type::none(db, env),
                        ))
                        .with_optional_default_type(Some(Type::none(db, env))),
                ]),
                self_ty,
            ),
        ),
        "nocache" => CallableType::single(db, Signature::new(Parameters::empty(), self_ty)),
        _ => return None,
    })
}

fn with_cacheops_queryset_protocol<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    queryset_class: StaticClassLiteral<'db>,
    queryset_instance: Type<'db>,
) -> Type<'db> {
    if !has_cacheops_hint_in_mro(db, env.program(db), queryset_class) {
        return queryset_instance;
    }

    let methods = ["cache", "invalidated_update", "nocache"].map(|name| {
        (
            name,
            cacheops_method_callable(db, env, name, queryset_instance)
                .expect("cacheops method names should be recognized"),
        )
    });
    let protocol = Type::protocol_with_methods(db, env, methods);
    IntersectionType::from_two_elements(db, env, queryset_instance, protocol)
}

fn model_instance_from_exact_django_queryset_like<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    ty: Type<'db>,
) -> Option<Type<'db>> {
    let class = ty.nominal_class(db, env)?;
    let (class_lit, _) = class.static_class_literal(db)?;
    let class_name = class_lit.name(db);
    let class_name = class_name.as_str().trim_start_matches('_');
    if !class_name.ends_with("QuerySet")
        && !class_name.ends_with("Manager")
        && !matches!(
            class_name,
            "QuerySet" | "Manager" | "RelatedManager" | "ManyRelatedManager"
        )
    {
        return None;
    }
    if !is_django_queryset_like_class(db, env.program(db), class_lit)
        && !is_django_queryset_or_manager_subclass(db, class_lit)
    {
        return django_queryset_model_from_declared_manager(db, env.program(db), class_lit)
            .or_else(|| django_model_from_declared_manager_class(db, env.program(db), class_lit));
    }

    let model_instance = ty
        .class_specialization(db, env)
        .and_then(|(_, specialization)| specialization.types(db).first().copied());
    model_instance
        .filter(|model_instance| {
            static_class_from_instance(db, env, *model_instance)
                .is_some_and(|model| model.is_django_model(db))
        })
        .or_else(|| django_queryset_model_from_declared_manager(db, env.program(db), class_lit))
        .or_else(|| django_model_from_declared_manager_class(db, env.program(db), class_lit))
}

fn type_contains_static_class<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    ty: Type<'db>,
    expected: StaticClassLiteral<'db>,
) -> bool {
    match ty {
        Type::Intersection(intersection) => intersection
            .positive(db)
            .iter()
            .any(|element| type_contains_static_class(db, env, *element, expected)),
        _ => {
            ty.nominal_class(db, env)
                .and_then(|class| class.static_class_literal(db).map(|(class, _)| class))
                == Some(expected)
        }
    }
}

#[salsa::tracked(returns(copy), cycle_initial=|_, _, _, _| None)]
fn django_model_from_declared_manager_class<'db>(
    db: &'db dyn Db,
    program: Program<'db>,
    manager_class: StaticClassLiteral<'db>,
) -> Option<Type<'db>> {
    let env = &ProgramEnvironment::from_program(program);
    let module = file_to_module(db, resolver_file(db, env, manager_class.file(db)))?;
    if let Some(model_name) = manager_class
        .name(db)
        .as_str()
        .strip_prefix("_")
        .unwrap_or(manager_class.name(db).as_str())
        .strip_suffix("Manager")
        && let Some(model) =
            local_class_literal_by_name(db, env, manager_class.file(db), model_name)
        && model.is_django_model(db)
    {
        return Some(Type::instance(db, env, model.default_specialization(db)));
    }

    for model in django_model_classes_in_module(db, env.program(db), module)
        .iter()
        .copied()
    {
        let Some(manager) = first_declared_manager(db, env.program(db), model) else {
            continue;
        };
        if type_contains_static_class(db, env, manager, manager_class) {
            return Some(Type::instance(db, env, model.default_specialization(db)));
        }
    }

    None
}

#[salsa::tracked(returns(copy), cycle_initial=|_, _, _, _| None)]
fn django_queryset_model_from_declared_manager<'db>(
    db: &'db dyn Db,
    program: Program<'db>,
    queryset_class: StaticClassLiteral<'db>,
) -> Option<Type<'db>> {
    let env = &ProgramEnvironment::from_program(program);
    let module = file_to_module(db, resolver_file(db, env, queryset_class.file(db)))?;
    for model in django_model_classes_in_module(db, env.program(db), module)
        .iter()
        .copied()
    {
        if first_declared_manager_queryset_class(db, env.program(db), model) == Some(queryset_class)
        {
            return Some(Type::instance(db, env, model.default_specialization(db)));
        }
    }

    None
}

pub(crate) fn model_instance_from_django_queryset_like<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    ty: Type<'db>,
) -> Option<Type<'db>> {
    match ty {
        Type::Intersection(intersection) => {
            let positive = intersection.positive(db);
            let base_model = positive
                .iter()
                .find_map(|element| model_instance_from_django_queryset_like(db, env, *element))?;
            // `QuerySet.annotate(...)` records its extra columns as an annotation protocol that it
            // intersects onto the queryset type. When the queryset is a concrete subclass whose
            // model is baked into an invariant type argument, that annotation can't be threaded
            // through the model's type parameter, so fold it back into the extracted model here.
            let model = positive
                .iter()
                .filter(|element| is_django_annotation_protocol(db, **element))
                .fold(base_model, |model, protocol| {
                    IntersectionType::from_two_elements(db, env, model, *protocol)
                });
            Some(model)
        }
        _ => model_instance_from_exact_django_queryset_like(db, env, ty),
    }
}

/// Returns `true` if `ty` is a synthesized "annotation" protocol: a protocol instance whose
/// members are all data (non-method) members, as produced for the extra columns introduced by
/// `QuerySet.annotate(...)`. Method protocols (such as those synthesized for
/// `Manager.from_queryset`) are deliberately excluded.
fn is_django_annotation_protocol<'db>(db: &'db dyn Db, ty: Type<'db>) -> bool {
    let Type::ProtocolInstance(protocol) = ty else {
        return false;
    };
    let mut members = protocol.interface(db).members(db);
    let count = members.len();
    count > 0 && members.all(|member| !member.is_method())
}

pub(crate) fn django_queryset_with_row_type<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    queryset_ty: Type<'db>,
    row_ty: Type<'db>,
) -> Option<Type<'db>> {
    let model_ty = queryset_ty
        .class_specialization(db, env)?
        .1
        .types(db)
        .first()
        .copied()?;
    django_queryset_with_model_and_row_type(db, env, queryset_ty, model_ty, row_ty)
}

pub(crate) fn django_queryset_with_model_and_row_type<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    queryset_ty: Type<'db>,
    model_ty: Type<'db>,
    row_ty: Type<'db>,
) -> Option<Type<'db>> {
    let class = queryset_ty.nominal_class(db, env)?;
    let (class_lit, _) = class.static_class_literal(db)?;
    if !is_django_queryset_like_class(db, env.program(db), class_lit) {
        return None;
    }

    Some(Type::instance(
        db,
        env,
        class_lit.apply_specialization(db, |generic_context| match generic_context.len(db) {
            0 => generic_context.unknown_specialization(db, None),
            1 => generic_context.specialize(db, &[model_ty]),
            2 => generic_context.specialize(db, &[model_ty, row_ty]),
            len => {
                let mut specialization = vec![Type::unknown(); len];
                specialization[0] = model_ty;
                specialization[1] = row_ty;
                generic_context.specialize(db, &specialization)
            }
        }),
    ))
}

pub(crate) fn django_queryset_base_instance_with_model_and_row_type<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    file: File,
    model_ty: Type<'db>,
    row_ty: Type<'db>,
) -> Option<Type<'db>> {
    let queryset_class = resolve_django_symbol(db, env, file, "django.db.models.query", "QuerySet")
        .or_else(|| resolve_django_symbol(db, env, file, "django.db.models", "QuerySet"))?;
    let Type::ClassLiteral(ClassLiteral::Static(queryset_class)) = queryset_class else {
        return None;
    };

    Some(Type::instance(
        db,
        env,
        queryset_class.apply_specialization(db, |generic_context| match generic_context.len(db) {
            0 => generic_context.unknown_specialization(db, None),
            1 => generic_context.specialize(db, &[model_ty]),
            2 => generic_context.specialize(db, &[model_ty, row_ty]),
            len => {
                let mut specialization = vec![Type::unknown(); len];
                specialization[0] = model_ty;
                specialization[1] = row_ty;
                generic_context.specialize(db, &specialization)
            }
        }),
    ))
}

pub(crate) fn django_values_list_all_fields_row_type<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    model_instance: Type<'db>,
    flat: bool,
) -> Option<Type<'db>> {
    if flat {
        let model_class = static_class_from_instance(db, env, model_instance)?;
        if !model_class.is_django_model(db) {
            return None;
        }
        let fields = collect_all_django_fields(db, env.program(db), model_class);
        return Some(resolve_pk_lookup_type(db, env, fields));
    }

    let row_types = django_values_list_all_fields_columns(db, env, model_instance)?
        .into_iter()
        .map(|(_, ty)| ty);
    Some(Type::heterogeneous_tuple(db, env, row_types))
}

pub(crate) fn django_values_list_all_fields_columns<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    model_instance: Type<'db>,
) -> Option<Vec<(Name, Type<'db>)>> {
    let model_class = static_class_from_instance(db, env, model_instance)?;
    if !model_class.is_django_model(db) {
        return None;
    }

    let fields = collect_all_django_fields(db, env.program(db), model_class);
    let mut columns = Vec::with_capacity(fields.len() + 1);
    if !fields.iter().any(|field| field.primary_key) {
        columns.push((Name::new("id"), resolve_pk_lookup_type(db, env, fields)));
    }
    columns.extend(
        fields
            .iter()
            .filter(|field| !matches!(field.kind, DjangoFieldKind::ManyToMany))
            .map(|field| (field.name.clone(), field.lookup_exact_type(db, env))),
    );

    Some(columns)
}

pub(crate) fn django_values_all_fields_row_type<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    model_instance: Type<'db>,
) -> Option<Type<'db>> {
    let items = django_values_list_all_fields_columns(db, env, model_instance)?
        .into_iter()
        .map(|(name, ty)| {
            (
                name,
                functional_typed_dict_field(ty, TypeQualifiers::empty(), true),
            )
        })
        .collect::<TypedDictSchema>();

    Some(Type::TypedDict(TypedDictType::from_schema_items(db, items)))
}

pub(crate) fn django_model_init_positional_field_names<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    model_instance: Type<'db>,
) -> Option<Vec<Name>> {
    let model_class = static_class_from_instance(db, env, model_instance)?;
    if !model_class.is_django_model(db) {
        return None;
    }

    Some(
        collect_all_django_fields(db, env.program(db), model_class)
            .iter()
            .filter(|field| !matches!(field.kind, DjangoFieldKind::ManyToMany))
            .map(|field| field.name.clone())
            .collect(),
    )
}

pub(crate) fn django_meta_get_field_return_type<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    file: File,
    model_owner_ty: Type<'db>,
    field_name: &str,
) -> Option<Type<'db>> {
    match django_meta_field(db, env, model_owner_ty, field_name)? {
        DjangoMetaField::Field(field) => {
            if let Some(field_instance) =
                django_field_class_instance_type(db, env, file, field.class_name.as_str())
            {
                return Some(field_instance);
            }
        }
        DjangoMetaField::ReverseRelation => {
            return resolve_django_symbol(
                db,
                env,
                file,
                "django.db.models.fields.reverse_related",
                "ForeignObjectRel",
            )
            .and_then(|ty| ty.to_instance_approximation(db, env));
        }
    }

    let field_ty = resolve_django_symbol(db, env, file, "django.db.models.fields", "Field")
        .or_else(|| resolve_django_symbol(db, env, file, "django.db.models", "Field"))?;
    specialize_class_instance(db, env, field_ty, &[Type::unknown(), Type::unknown()])
        .or_else(|| field_ty.to_instance_approximation(db, env))
}

fn django_field_class_instance_type<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    file: File,
    class_name: &str,
) -> Option<Type<'db>> {
    resolve_class_in_scope(db, env, file, class_name)
        .map(|class| class_literal_to_instance(db, env, class))
        .or_else(|| {
            let module_names = match class_name {
                "ForeignKey" | "ForeignObject" | "OneToOneField" | "ManyToManyField" => {
                    &["django.db.models", "django.db.models.fields.related"][..]
                }
                "GenericForeignKey" => &["django.contrib.contenttypes.fields"][..],
                _ => &["django.db.models", "django.db.models.fields"][..],
            };
            module_names.iter().find_map(|module_name| {
                resolve_django_symbol(db, env, file, module_name, class_name)
                    .and_then(|ty| ty.to_instance_approximation(db, env))
            })
        })
}

pub(crate) fn django_meta_has_field<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    model_owner_ty: Type<'db>,
    field_name: &str,
) -> bool {
    django_meta_field(db, env, model_owner_ty, field_name).is_some()
}

fn django_meta_field<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    model_owner_ty: Type<'db>,
    field_name: &str,
) -> Option<DjangoMetaField<'db>> {
    let model_class = match model_owner_ty {
        Type::ClassLiteral(ClassLiteral::Static(class)) => class,
        _ => static_class_from_instance(db, env, model_owner_ty)?,
    };
    if !model_class.is_django_model(db) {
        return None;
    }

    let fields = collect_all_django_fields(db, env.program(db), model_class);
    fields
        .iter()
        .find(|field| field.name.as_str() == field_name)
        .cloned()
        .map(|field| DjangoMetaField::Field(Box::new(field)))
        .or_else(|| {
            (field_name == "id" && !fields.iter().any(|field| field.primary_key)).then(|| {
                DjangoMetaField::Field(Box::new(DjangoFieldInfo {
                    name: Name::new_static("id"),
                    file: model_class.file(db),
                    class_name: "AutoField".to_string(),
                    kind: DjangoFieldKind::Auto,
                    nullable: false,
                    primary_key: true,
                    has_choices: false,
                    value_type_override: None,
                    related_model: None,
                    related_model_is_auth_user: false,
                    related_target: None,
                    related_name: None,
                    related_query_name: None,
                    to_field: None,
                }))
            })
        })
        .or_else(|| {
            let field_name = field_name.strip_suffix("_id")?;
            fields
                .iter()
                .find(|field| {
                    field.name.as_str() == field_name
                        && matches!(
                            field.kind,
                            DjangoFieldKind::ForeignKey | DjangoFieldKind::OneToOne
                        )
                })
                .cloned()
                .map(|field| DjangoMetaField::Field(Box::new(field)))
        })
        .or_else(|| {
            django_reverse_member_by_name(db, env, model_class, field_name)
                .map(|_| DjangoMetaField::ReverseRelation)
        })
}

enum DjangoMetaField<'db> {
    Field(Box<DjangoFieldInfo<'db>>),
    ReverseRelation,
}

fn django_reverse_member_by_name<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    target_model: StaticClassLiteral<'db>,
    field_name: &str,
) -> Option<DjangoReverseMemberInfo<'db>> {
    let name = Name::new(field_name);
    if let Some(top_level_package) =
        django_top_level_package_for_file(db, env, target_model.file(db))
    {
        if let Some(reverse_member) = django_reverse_members_named_in_top_level_package(
            db,
            env.program(db),
            top_level_package,
            name.clone(),
        )
        .iter()
        .find(|reverse_member| reverse_member.target_model == target_model)
        .cloned()
        {
            return Some(reverse_member);
        }

        if let Some(reverse_member) = django_reverse_members_named_in_project_search_path(
            db,
            env.program(db),
            top_level_package,
            name.clone(),
        )
        .iter()
        .find(|reverse_member| reverse_member.target_model == target_model)
        .cloned()
        {
            return Some(reverse_member);
        }
    }

    if let Some(models_module) = django_models_module_for_file(db, env, target_model.file(db))
        && let Some(reverse_member) =
            django_reverse_members_named_in_models_module(db, env, models_module, &name)
                .iter()
                .find(|reverse_member| reverse_member.target_model == target_model)
                .cloned()
    {
        return Some(reverse_member);
    }

    let file = target_model.file(db);
    for source_model in django_model_classes_in_module(
        db,
        env.program(db),
        file_to_module(db, resolver_file(db, env, file))?,
    )
    .iter()
    .copied()
    {
        if source_model == target_model {
            continue;
        }
        for field in source_model.django_model_relation_fields(db) {
            if !matches!(
                field.kind,
                DjangoFieldKind::ForeignKey
                    | DjangoFieldKind::OneToOne
                    | DjangoFieldKind::ManyToMany
            ) {
                continue;
            }
            if django_relation_targets_model(db, env, source_model, field, target_model)
                && reverse_related_name(db, env, source_model, field) == Some(name.clone())
            {
                let Some(query_name) = reverse_related_query_name(db, env, source_model, field)
                else {
                    continue;
                };
                return Some(DjangoReverseMemberInfo {
                    target_model,
                    name,
                    query_name,
                    source_model,
                    source_file: file,
                    kind: field.kind,
                });
            }
        }
    }

    None
}

pub(super) fn specialize_declared_django_manager_member<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    class: StaticClassLiteral<'db>,
    ty: Type<'db>,
) -> Option<Type<'db>> {
    if class.is_known(db, KnownClass::DjangoModel)
        || !class.is_django_model(db)
        || !is_manager_instance(db, env, ty)
    {
        return None;
    }

    let (manager_class, _) = ty.nominal_class(db, env)?.static_class_literal(db)?;
    let model_instance = Type::instance(db, env, class.apply_optional_specialization(db, None));

    if manager_class.generic_context(db).is_some() {
        return Some(Type::instance(
            db,
            env,
            manager_class.apply_specialization(db, |generic_context| {
                if generic_context.len(db) == 1 {
                    generic_context.specialize(db, &[model_instance])
                } else {
                    generic_context.unknown_specialization(db, None)
                }
            }),
        ));
    }

    let specialized_base_manager =
        synthesize_manager_instance(db, env, class.file(db), model_instance);
    Some(IntersectionType::from_two_elements(
        db,
        env,
        ty,
        specialized_base_manager,
    ))
}

pub(super) fn specialize_declared_django_manager_class_member<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    class: StaticClassLiteral<'db>,
    name: &str,
    ty: Type<'db>,
) -> Option<Type<'db>> {
    if name.starts_with("__") && name.ends_with("__") {
        return None;
    }

    let file = class.file(db);
    if let Some(module) = file_to_module(db, resolver_file(db, env, file))
        && !module_is_project_code(db, module)
        && !module_may_define_django_models(db, env.program(db), module)
    {
        return None;
    }

    let module = parsed_module(db, python_file(db, env, file)).load(db);
    let class_stmt = class.node(db, &module);

    let value_expr = class_stmt.body.iter().find_map(|stmt| {
        let (target_name, value_expr) = extract_assignment(stmt)?;
        (target_name.as_str() == name).then_some(value_expr)
    });

    let value_expr = value_expr?;

    let queryset_methods_protocol = declared_manager_queryset_protocol(db, env, class, value_expr)?;

    let manager_ty = specialize_declared_django_manager_member(db, env, class, ty);
    let manager_ty = manager_ty.unwrap_or_else(|| {
        let model_instance = Type::instance(db, env, class.apply_optional_specialization(db, None));
        synthesize_manager_instance(db, env, file, model_instance)
    });
    let specialized_ty =
        IntersectionType::from_two_elements(db, env, manager_ty, queryset_methods_protocol);

    (specialized_ty != manager_ty).then_some(specialized_ty)
}

#[salsa::tracked(returns(copy), cycle_initial=|_, _, _, _, _| None)]
fn first_declared_manager_in_class_body<'db>(
    db: &'db dyn Db,
    program: Program<'db>,
    owner_class: StaticClassLiteral<'db>,
    declaring_class: StaticClassLiteral<'db>,
) -> Option<Type<'db>> {
    let env = &ProgramEnvironment::from_program(program);
    let file = declaring_class.file(db);
    let module = parsed_module(db, python_file(db, env, file)).load(db);
    let class_stmt = declaring_class.node(db, &module);

    for stmt in &class_stmt.body {
        let Some((target_name, value_expr)) = extract_assignment(stmt) else {
            continue;
        };
        if let ast::Expr::Call(call_expr) = value_expr {
            let field_class_name = match call_expr.func.as_ref() {
                ast::Expr::Name(name) => name.id.as_str(),
                ast::Expr::Attribute(attr) => attr.attr.as_str(),
                _ => continue,
            };
            if field_class_to_kind(field_class_name).is_some() {
                continue;
            }
        }

        let ty = class_member(db, declaring_class.body_scope(db), target_name.as_str())
            .ignore_possibly_undefined()
            .unwrap_or_else(Type::unknown);
        if is_manager_instance(db, env, ty) {
            let manager_ty =
                specialize_declared_django_manager_member(db, env, owner_class, ty).unwrap_or(ty);
            return Some(declared_manager_queryset_intersection(
                db,
                env,
                owner_class,
                manager_ty,
                value_expr,
            ));
        }

        if manager_assignment_queryset_class(db, env, declaring_class.file(db), value_expr)
            .is_some()
        {
            let model_instance =
                Type::instance(db, env, owner_class.apply_optional_specialization(db, None));
            let manager_ty =
                synthesize_manager_instance(db, env, declaring_class.file(db), model_instance);
            return Some(declared_manager_queryset_intersection(
                db,
                env,
                owner_class,
                manager_ty,
                value_expr,
            ));
        }
    }

    None
}

#[salsa::tracked(returns(copy), cycle_initial=|_, _, _, _| None)]
fn first_declared_manager<'db>(
    db: &'db dyn Db,
    program: Program<'db>,
    class: StaticClassLiteral<'db>,
) -> Option<Type<'db>> {
    let env = &ProgramEnvironment::from_program(program);
    for base in class.iter_mro(db, None) {
        let Some(base_class) = base.into_class() else {
            continue;
        };
        let Some((base_lit, _)) = base_class.static_class_literal(db) else {
            continue;
        };
        if base_lit.is_known(db, KnownClass::DjangoModel) || !base_lit.is_django_model(db) {
            continue;
        }
        if let Some(manager) =
            first_declared_manager_in_class_body(db, env.program(db), class, base_lit)
        {
            return Some(manager);
        }
    }

    None
}

fn meta_string_option<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    class: StaticClassLiteral<'db>,
    option_name: &str,
) -> Option<Name> {
    let file = class.file(db);
    let module = parsed_module(db, python_file(db, env, file)).load(db);
    let class_stmt = class.node(db, &module);

    for stmt in &class_stmt.body {
        let ast::Stmt::ClassDef(meta_class) = stmt else {
            continue;
        };
        if meta_class.name.as_str() != "Meta" {
            continue;
        }

        for stmt in &meta_class.body {
            let value = match stmt {
                ast::Stmt::Assign(assign) => {
                    let [target] = assign.targets.as_slice() else {
                        continue;
                    };
                    let ast::Expr::Name(name) = target else {
                        continue;
                    };
                    if name.id.as_str() != option_name {
                        continue;
                    }
                    assign.value.as_ref()
                }
                ast::Stmt::AnnAssign(ann_assign) => {
                    let ast::Expr::Name(name) = ann_assign.target.as_ref() else {
                        continue;
                    };
                    if name.id.as_str() != option_name {
                        continue;
                    }
                    let Some(value) = ann_assign.value.as_deref() else {
                        continue;
                    };
                    value
                }
                _ => continue,
            };

            if let ast::Expr::StringLiteral(string_lit) = value {
                return Some(Name::new(string_lit.value.to_str()));
            }
        }
    }

    None
}

#[salsa::tracked(returns(copy), cycle_initial=|_, _, _, _| false)]
fn django_model_is_abstract<'db>(
    db: &'db dyn Db,
    program: Program<'db>,
    class: StaticClassLiteral<'db>,
) -> bool {
    let env = &ProgramEnvironment::from_program(program);
    let file = class.file(db);
    let module = parsed_module(db, python_file(db, env, file)).load(db);
    let class_stmt = class.node(db, &module);

    for stmt in &class_stmt.body {
        let ast::Stmt::ClassDef(meta_class) = stmt else {
            continue;
        };
        if meta_class.name.as_str() != "Meta" {
            continue;
        }

        for stmt in &meta_class.body {
            let value = match stmt {
                ast::Stmt::Assign(assign) => {
                    let [target] = assign.targets.as_slice() else {
                        continue;
                    };
                    let ast::Expr::Name(name) = target else {
                        continue;
                    };
                    if name.id.as_str() != "abstract" {
                        continue;
                    }
                    assign.value.as_ref()
                }
                ast::Stmt::AnnAssign(ann_assign) => {
                    let ast::Expr::Name(name) = ann_assign.target.as_ref() else {
                        continue;
                    };
                    if name.id.as_str() != "abstract" {
                        continue;
                    }
                    let Some(value) = ann_assign.value.as_deref() else {
                        continue;
                    };
                    value
                }
                _ => continue,
            };

            return matches!(
                value,
                ast::Expr::BooleanLiteral(ast::ExprBooleanLiteral { value: true, .. })
            );
        }
    }

    false
}

fn named_manager<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    class: StaticClassLiteral<'db>,
    name: &str,
) -> Option<Type<'db>> {
    let ty = class_member(db, class.body_scope(db), name).ignore_possibly_undefined()?;
    is_manager_instance(db, env, ty)
        .then(|| specialize_declared_django_manager_member(db, env, class, ty).unwrap_or(ty))
}

fn from_queryset_class<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    file: File,
    call_expr: &ast::ExprCall,
) -> Option<StaticClassLiteral<'db>> {
    let ast::Expr::Attribute(attr) = call_expr.func.as_ref() else {
        return None;
    };
    if attr.attr.as_str() != "from_queryset" {
        return None;
    }
    let ast::Expr::Name(queryset_name) = call_expr.arguments.args.first()? else {
        return None;
    };

    resolve_class_in_scope(db, env, file, queryset_name.id.as_str())
}

fn from_queryset_manager_class<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    file: File,
    call_expr: &ast::ExprCall,
) -> Option<StaticClassLiteral<'db>> {
    let ast::Expr::Attribute(attr) = call_expr.func.as_ref() else {
        return None;
    };
    if attr.attr.as_str() != "from_queryset" {
        return None;
    }

    match attr.value.as_ref() {
        ast::Expr::Name(name) => resolve_class_in_scope(db, env, file, name.id.as_str()),
        ast::Expr::Attribute(attr) => resolve_class_in_scope(db, env, file, attr.attr.as_str()),
        _ => None,
    }
}

fn as_manager_queryset_class<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    file: File,
    call_expr: &ast::ExprCall,
) -> Option<StaticClassLiteral<'db>> {
    let ast::Expr::Attribute(attr) = call_expr.func.as_ref() else {
        return None;
    };
    if attr.attr.as_str() != "as_manager" {
        return None;
    }

    match attr.value.as_ref() {
        ast::Expr::Name(name) => resolve_class_in_scope(db, env, file, name.id.as_str()),
        ast::Expr::Attribute(attr) => resolve_class_in_scope(db, env, file, attr.attr.as_str()),
        _ => None,
    }
}

fn manager_factory_queryset_class<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    file: File,
    factory_name: &str,
) -> Option<StaticClassLiteral<'db>> {
    let module = parsed_module(db, python_file(db, env, file)).load(db);

    for stmt in module.suite() {
        let ast::Stmt::Assign(assign) = stmt else {
            continue;
        };
        let [target] = assign.targets.as_slice() else {
            continue;
        };
        let ast::Expr::Name(name) = target else {
            continue;
        };
        if name.id.as_str() != factory_name {
            continue;
        }
        let ast::Expr::Call(call_expr) = assign.value.as_ref() else {
            continue;
        };

        return from_queryset_class(db, env, file, call_expr)
            .or_else(|| as_manager_queryset_class(db, env, file, call_expr));
    }

    None
}

fn manager_factory_manager_class<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    file: File,
    factory_name: &str,
) -> Option<StaticClassLiteral<'db>> {
    let module = parsed_module(db, python_file(db, env, file)).load(db);

    for stmt in module.suite() {
        let ast::Stmt::Assign(assign) = stmt else {
            continue;
        };
        let [target] = assign.targets.as_slice() else {
            continue;
        };
        let ast::Expr::Name(name) = target else {
            continue;
        };
        if name.id.as_str() != factory_name {
            continue;
        }
        let ast::Expr::Call(call_expr) = assign.value.as_ref() else {
            continue;
        };

        return from_queryset_manager_class(db, env, file, call_expr);
    }

    None
}

fn manager_assignment_queryset_class<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    file: File,
    value_expr: &ast::Expr,
) -> Option<StaticClassLiteral<'db>> {
    match value_expr {
        ast::Expr::Name(name) => manager_factory_queryset_class(db, env, file, name.id.as_str()),
        ast::Expr::Call(call_expr) => match call_expr.func.as_ref() {
            ast::Expr::Name(name) => {
                manager_factory_queryset_class(db, env, file, name.id.as_str())
            }
            ast::Expr::Call(inner_call) => from_queryset_class(db, env, file, inner_call),
            ast::Expr::Attribute(_) => as_manager_queryset_class(db, env, file, call_expr),
            _ => None,
        },
        _ => None,
    }
}

fn manager_assignment_manager_class<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    file: File,
    value_expr: &ast::Expr,
) -> Option<StaticClassLiteral<'db>> {
    match value_expr {
        ast::Expr::Name(name) => manager_factory_manager_class(db, env, file, name.id.as_str()),
        ast::Expr::Call(call_expr) => match call_expr.func.as_ref() {
            ast::Expr::Name(name) => manager_factory_manager_class(db, env, file, name.id.as_str()),
            ast::Expr::Call(inner_call) => from_queryset_manager_class(db, env, file, inner_call),
            _ => None,
        },
        _ => None,
    }
}

pub(crate) fn django_manager_factory_base_type<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    file: File,
    base_node: &ast::Expr,
) -> Option<Type<'db>> {
    let ast::Expr::Name(name) = base_node else {
        return None;
    };

    manager_factory_manager_class(db, env, file, name.id.as_str()).map(Type::from)
}

fn queryset_instance_for_manager_model<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    queryset_class: StaticClassLiteral<'db>,
    _owner_class: StaticClassLiteral<'db>,
) -> Type<'db> {
    // Use the declared queryset class directly. If it is a concrete subclass such as
    // `BookQuerySet(QuerySet[Book])`, the inherited base already carries the model binding.
    let queryset_instance = Type::instance(
        db,
        env,
        queryset_class.apply_optional_specialization(db, None),
    );
    with_cacheops_queryset_protocol(db, env, queryset_class, queryset_instance)
}

#[salsa::tracked(returns(copy), cycle_initial=|_, _, _, _, _| None)]
#[allow(clippy::needless_pass_by_value)]
fn manager_queryset_class_for_declared_member_in_class<'db>(
    db: &'db dyn Db,
    program: Program<'db>,
    declaring_class: StaticClassLiteral<'db>,
    manager_name: Name,
) -> Option<StaticClassLiteral<'db>> {
    let env = &ProgramEnvironment::from_program(program);
    let file = declaring_class.file(db);
    let module = parsed_module(db, python_file(db, env, file)).load(db);
    let class_stmt = declaring_class.node(db, &module);

    let value_expr = class_stmt.body.iter().find_map(|stmt| {
        let (target_name, value_expr) = extract_assignment(stmt)?;
        (target_name == manager_name).then_some(value_expr)
    })?;

    manager_assignment_queryset_class(db, env, file, value_expr)
}

fn manager_queryset_class_for_declared_member<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    owner_class: StaticClassLiteral<'db>,
    manager_name: &str,
) -> Option<StaticClassLiteral<'db>> {
    for base in owner_class.iter_mro(db, None) {
        let Some(base_class) = base.into_class() else {
            continue;
        };
        let Some((base_lit, _)) = base_class.static_class_literal(db) else {
            continue;
        };
        if base_lit.is_known(db, KnownClass::DjangoModel) || !base_lit.is_django_model(db) {
            continue;
        }
        if let Some(queryset_class) = manager_queryset_class_for_declared_member_in_class(
            db,
            env.program(db),
            base_lit,
            Name::new(manager_name),
        ) {
            return Some(queryset_class);
        }
    }

    None
}

#[salsa::tracked(returns(copy), cycle_initial=|_, _, _, _| None)]
fn first_declared_manager_queryset_class<'db>(
    db: &'db dyn Db,
    program: Program<'db>,
    owner_class: StaticClassLiteral<'db>,
) -> Option<StaticClassLiteral<'db>> {
    let env = &ProgramEnvironment::from_program(program);
    let file = owner_class.file(db);
    let module = parsed_module(db, python_file(db, env, file)).load(db);
    let class_stmt = owner_class.node(db, &module);

    class_stmt.body.iter().find_map(|stmt| {
        let (target_name, _) = extract_assignment(stmt)?;
        manager_queryset_class_for_declared_member_in_class(
            db,
            env.program(db),
            owner_class,
            target_name,
        )
    })
}

pub(crate) fn django_queryset_instance_for_model_manager<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    owner_class: StaticClassLiteral<'db>,
    manager_name: &str,
) -> Option<Type<'db>> {
    let queryset_class = if manager_name == "_default_manager" {
        meta_string_option(db, env, owner_class, "default_manager_name")
            .as_deref()
            .and_then(|name| manager_queryset_class_for_declared_member(db, env, owner_class, name))
            .or_else(|| first_declared_manager_queryset_class(db, env.program(db), owner_class))?
    } else {
        manager_queryset_class_for_declared_member(db, env, owner_class, manager_name)?
    };

    Some(queryset_instance_for_manager_model(
        db,
        env,
        queryset_class,
        owner_class,
    ))
}

pub(crate) fn django_queryset_instance_for_reverse_manager<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    target_model: StaticClassLiteral<'db>,
    member_name: &str,
) -> Option<Type<'db>> {
    let reverse_member_name = Name::new(member_name);

    if let Some(top_level_package) =
        django_top_level_package_for_file(db, env, target_model.file(db))
    {
        for reverse_member in django_reverse_members_named_in_top_level_package(
            db,
            env.program(db),
            top_level_package,
            reverse_member_name.clone(),
        ) {
            if reverse_member.target_model == target_model
                && matches!(
                    reverse_member.kind,
                    DjangoFieldKind::ForeignKey | DjangoFieldKind::ManyToMany
                )
            {
                return django_queryset_instance_for_model_manager(
                    db,
                    env,
                    reverse_member.source_model,
                    "_default_manager",
                );
            }
        }
    }

    if let Some(models_module) = django_models_module_for_file(db, env, target_model.file(db)) {
        for reverse_member in &django_reverse_members_named_in_models_module(
            db,
            env,
            models_module,
            &reverse_member_name,
        ) {
            if reverse_member.target_model == target_model
                && matches!(
                    reverse_member.kind,
                    DjangoFieldKind::ForeignKey | DjangoFieldKind::ManyToMany
                )
            {
                return django_queryset_instance_for_model_manager(
                    db,
                    env,
                    reverse_member.source_model,
                    "_default_manager",
                );
            }
        }
    }

    let file = target_model.file(db);
    for source_model in django_model_classes_in_module(
        db,
        env.program(db),
        file_to_module(db, resolver_file(db, env, file))?,
    )
    .iter()
    .copied()
    {
        if source_model == target_model {
            continue;
        }
        for field in source_model.django_model_relation_fields(db) {
            if !matches!(
                field.kind,
                DjangoFieldKind::ForeignKey | DjangoFieldKind::ManyToMany
            ) {
                continue;
            }
            if django_relation_targets_model(db, env, source_model, field, target_model)
                && reverse_related_name(db, env, source_model, field)
                    == Some(reverse_member_name.clone())
            {
                return django_queryset_instance_for_model_manager(
                    db,
                    env,
                    source_model,
                    "_default_manager",
                );
            }
        }
    }

    None
}

fn add_public_class_body_methods<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    class: StaticClassLiteral<'db>,
    methods: &mut Vec<(String, CallableType<'db>)>,
) {
    let file = class.file(db);
    let module = parsed_module(db, python_file(db, env, file)).load(db);
    let class_stmt = class.node(db, &module);

    for stmt in &class_stmt.body {
        let ast::Stmt::FunctionDef(function_def) = stmt else {
            continue;
        };
        let method_name = function_def.name.as_str();
        if method_name.starts_with('_') || methods.iter().any(|(name, _)| name == method_name) {
            continue;
        }
        let Some(Type::FunctionLiteral(function)) =
            class_member(db, class.body_scope(db), method_name).ignore_possibly_undefined()
        else {
            continue;
        };
        let callable = function.into_callable_type(db);
        methods.push((
            method_name.to_string(),
            callable.bind_self(db, env, Type::unknown(), Type::unknown()),
        ));
    }
}

fn is_django_base_queryset_class<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    class: StaticClassLiteral<'db>,
) -> bool {
    class.name(db).as_str() == "QuerySet"
        && file_to_module(db, resolver_file(db, env, class.file(db))).is_some_and(|module| {
            matches!(
                module.name(db).as_str(),
                "django.db.models" | "django.db.models.query"
            )
        })
}

pub(crate) fn is_django_queryset_class<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    class: StaticClassLiteral<'db>,
) -> bool {
    class.iter_mro(db, None).any(|base| {
        base.into_class()
            .and_then(|class_type| class_type.static_class_literal(db).map(|(class, _)| class))
            .is_some_and(|base| is_django_base_queryset_class(db, env, base))
    })
}

fn add_public_queryset_mro_methods<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    queryset_class: StaticClassLiteral<'db>,
    methods: &mut Vec<(String, CallableType<'db>)>,
) {
    for base in queryset_class.iter_mro(db, None) {
        let Some(base_class) = base.into_class() else {
            continue;
        };
        let Some((base_lit, _)) = base_class.static_class_literal(db) else {
            continue;
        };
        if is_django_base_queryset_class(db, env, base_lit) {
            break;
        }
        add_public_class_body_methods(db, env, base_lit, methods);
    }
}

fn declared_manager_queryset_intersection<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    owner_class: StaticClassLiteral<'db>,
    manager_ty: Type<'db>,
    value_expr: &ast::Expr,
) -> Type<'db> {
    let Some(queryset_methods_protocol) =
        declared_manager_queryset_protocol(db, env, owner_class, value_expr)
    else {
        return manager_ty;
    };

    IntersectionType::from_two_elements(db, env, manager_ty, queryset_methods_protocol)
}

fn declared_manager_queryset_protocol<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    owner_class: StaticClassLiteral<'db>,
    value_expr: &ast::Expr,
) -> Option<Type<'db>> {
    let file = owner_class.file(db);
    let manager_class = manager_assignment_manager_class(db, env, file, value_expr);

    let queryset_class = manager_assignment_queryset_class(db, env, file, value_expr)?;

    let mut methods: Vec<(String, CallableType<'db>)> = Vec::new();
    add_public_queryset_mro_methods(db, env, queryset_class, &mut methods);
    if let Some(manager_class) = manager_class
        && !is_django_manager_class(db, env, manager_class)
    {
        add_public_class_body_methods(db, env, manager_class, &mut methods);
    }

    let queryset_instance =
        queryset_instance_for_manager_model(db, env, queryset_class, owner_class);
    if has_cacheops_hint_in_mro(db, env.program(db), queryset_class) {
        for method_name in ["cache", "invalidated_update", "nocache"] {
            if methods.iter().any(|(name, _)| name == method_name) {
                continue;
            }
            methods.push((
                method_name.to_string(),
                cacheops_method_callable(db, env, method_name, queryset_instance)
                    .expect("cacheops method names should be recognized"),
            ));
        }
    }
    for method_name in MANAGER_METHODS_RETURNING_QUERYSET {
        if methods.iter().any(|(name, _)| name == method_name) {
            continue;
        }
        methods.push((
            (*method_name).to_string(),
            CallableType::single(
                db,
                Signature::new(Parameters::gradual_form(), queryset_instance),
            ),
        ));
    }

    if methods.is_empty() {
        return None;
    }

    Some(Type::protocol_with_methods(
        db,
        env,
        methods
            .iter()
            .map(|(name, callable)| (name.as_str(), *callable)),
    ))
}

fn first_declared_manager_queryset_protocol<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    class: StaticClassLiteral<'db>,
) -> Option<Type<'db>> {
    for base in class.iter_mro(db, None) {
        let Some(base_class) = base.into_class() else {
            continue;
        };
        let Some((base_lit, _)) = base_class.static_class_literal(db) else {
            continue;
        };
        if base_lit.is_known(db, KnownClass::DjangoModel) || !base_lit.is_django_model(db) {
            continue;
        }

        let file = base_lit.file(db);
        let module = parsed_module(db, python_file(db, env, file)).load(db);
        let class_stmt = base_lit.node(db, &module);

        for stmt in &class_stmt.body {
            let Some((_, value_expr)) = extract_assignment(stmt) else {
                continue;
            };
            if let ast::Expr::Call(call_expr) = value_expr {
                let field_class_name = match call_expr.func.as_ref() {
                    ast::Expr::Name(name) => name.id.as_str(),
                    ast::Expr::Attribute(attr) => attr.attr.as_str(),
                    _ => "",
                };
                if field_class_to_kind(field_class_name).is_some() {
                    continue;
                }
            }

            let declares_manager =
                manager_assignment_queryset_class(db, env, file, value_expr).is_some();
            if !declares_manager {
                continue;
            }

            return declared_manager_queryset_protocol(db, env, class, value_expr);
        }
    }

    None
}

pub(super) fn synthesize_inherited_django_manager_member<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    class: StaticClassLiteral<'db>,
    name: &str,
) -> Option<Type<'db>> {
    if class.is_known(db, KnownClass::DjangoModel) || !class.is_django_model(db) {
        return None;
    }

    for base in class.iter_mro(db, None).skip(1) {
        let Some(base_class) = base.into_class() else {
            continue;
        };
        let Some((base_lit, _)) = base_class.static_class_literal(db) else {
            continue;
        };
        if base_lit.is_known(db, KnownClass::DjangoModel) || !base_lit.is_django_model(db) {
            continue;
        }

        let file = base_lit.file(db);
        let module = parsed_module(db, python_file(db, env, file)).load(db);
        let class_stmt = base_lit.node(db, &module);
        let Some(value_expr) = class_stmt.body.iter().find_map(|stmt| {
            let (target_name, value_expr) = extract_assignment(stmt)?;
            (target_name.as_str() == name).then_some(value_expr)
        }) else {
            continue;
        };

        let Some(ty) = class_member(db, base_lit.body_scope(db), name).ignore_possibly_undefined()
        else {
            continue;
        };
        if is_manager_instance(db, env, ty) {
            let manager_ty =
                specialize_declared_django_manager_member(db, env, class, ty).unwrap_or(ty);
            return Some(declared_manager_queryset_intersection(
                db, env, class, manager_ty, value_expr,
            ));
        }
    }

    None
}

fn reverse_related_name<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    source_class: StaticClassLiteral<'db>,
    field: &DjangoFieldInfo,
) -> Option<Name> {
    reverse_related_name_from_parts(
        db,
        env,
        source_class,
        field.kind,
        field.related_name.as_ref(),
    )
}

fn reverse_related_name_from_parts<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    source_class: StaticClassLiteral<'db>,
    kind: DjangoFieldKind,
    related_name: Option<&Name>,
) -> Option<Name> {
    if let Some(related_name) = related_name {
        if related_name.as_str() == "+" {
            return None;
        }
        let source_name = source_class.name(db).as_str().to_ascii_lowercase();
        let app_label =
            django_app_label_for_file(db, env, source_class.file(db)).unwrap_or_default();
        return Some(Name::new(
            related_name
                .as_str()
                .replace("%(class)s", &source_name)
                .replace("%(model_name)s", &source_name)
                .replace("%(app_label)s", &app_label),
        ));
    }

    let source_name = source_class.name(db).as_str().to_ascii_lowercase();
    Some(Name::new(match kind {
        DjangoFieldKind::ForeignKey | DjangoFieldKind::ManyToMany => format!("{source_name}_set"),
        DjangoFieldKind::OneToOne => source_name,
        _ => return None,
    }))
}

fn reverse_related_query_name<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    source_class: StaticClassLiteral<'db>,
    field: &DjangoFieldInfo,
) -> Option<Name> {
    reverse_related_query_name_from_parts(
        db,
        env,
        source_class,
        field.related_query_name.as_ref(),
        field.related_name.as_ref(),
    )
}

fn reverse_related_query_name_from_parts<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    source_class: StaticClassLiteral<'db>,
    related_query_name: Option<&Name>,
    related_name: Option<&Name>,
) -> Option<Name> {
    let source_name = source_class.name(db).as_str().to_ascii_lowercase();
    let app_label = django_app_label_for_file(db, env, source_class.file(db)).unwrap_or_default();
    let name = related_query_name.or(related_name);
    if let Some(name) = name {
        if name.as_str() == "+" {
            return None;
        }
        return Some(Name::new(
            name.as_str()
                .replace("%(class)s", &source_name)
                .replace("%(model_name)s", &source_name)
                .replace("%(app_label)s", &app_label),
        ));
    }

    Some(Name::new(source_name))
}

fn django_app_label_for_file<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    file: File,
) -> Option<String> {
    let module = file_to_module(db, resolver_file(db, env, file))?;
    let mut previous = None;
    for component in module.name(db).components() {
        if component == "models" {
            return previous.map(str::to_string);
        }
        previous = Some(component);
    }
    None
}

fn django_models_module_for_file<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    file: File,
) -> Option<Module<'db>> {
    let module = file_to_module(db, resolver_file(db, env, file))?;
    let components: Vec<_> = module.name(db).components().collect();
    let models_index = components
        .iter()
        .position(|component| *component == "models")?;
    let models_module_name =
        ModuleName::from_components(components[..=models_index].iter().copied())?;
    resolve_module(db, as_importing_file(db, env, file), &models_module_name)
}

fn django_top_level_package_for_file<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    file: File,
) -> Option<Module<'db>> {
    let module = file_to_module(db, resolver_file(db, env, file))?;
    let top_level_name = module.name(db).components().next()?;
    let top_level_name = ModuleName::new(top_level_name)?;
    resolve_module(db, as_importing_file(db, env, file), &top_level_name)
}

fn module_is_under_top_level<'db>(
    db: &'db dyn Db,
    module: Module<'db>,
    top_level_module: Module<'db>,
) -> bool {
    let Some(module_top_level_name) = module.name(db).components().next() else {
        return false;
    };
    let Some(top_level_name) = top_level_module.name(db).components().next() else {
        return false;
    };
    module_top_level_name == top_level_name
}

fn module_is_top_level<'db>(db: &'db dyn Db, module: Module<'db>) -> bool {
    module.name(db).components().count() == 1
}

fn module_is_project_code<'db>(db: &'db dyn Db, module: Module<'db>) -> bool {
    module.search_path(db).is_some_and(|search_path| {
        !search_path.is_standard_library() && !search_path.is_site_packages()
    })
}

fn module_is_under_module<'db>(db: &'db dyn Db, module: Module<'db>, parent: Module<'db>) -> bool {
    let module_name = module.name(db).as_str();
    let parent_name = parent.name(db).as_str();
    module_name == parent_name
        || module_name
            .strip_prefix(parent_name)
            .is_some_and(|suffix| suffix.starts_with('.'))
}

fn module_name_last_component<'db>(db: &'db dyn Db, module: Module<'db>) -> Option<&'db str> {
    module.name(db).components().next_back()
}

fn collect_django_model_modules<'db>(
    db: &'db dyn Db,
    module: Module<'db>,
    modules: &mut Vec<Module<'db>>,
) {
    if modules.contains(&module) {
        return;
    }
    modules.push(module);

    for &submodule in module.all_submodules(db) {
        collect_django_model_modules(db, submodule, modules);
    }
}

fn collect_django_model_modules_under<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    module: Module<'db>,
    modules: &mut Vec<Module<'db>>,
) {
    if module_name_last_component(db, module) == Some("models") {
        collect_django_model_modules(db, module, modules);
        return;
    }

    if module.file(db).is_none() {
        for &listed_module in list_modules(db, env.program(db).resolver_environment(db)) {
            if listed_module == module || !module_is_under_module(db, listed_module, module) {
                continue;
            }
            if module_name_last_component(db, listed_module) == Some("models") {
                collect_django_model_modules(db, listed_module, modules);
            }
        }
        return;
    }

    for &submodule in module.all_submodules(db) {
        collect_django_model_modules_under(db, env, submodule, modules);
    }
}

fn collect_django_project_model_modules_under<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    module: Module<'db>,
    modules: &mut Vec<Module<'db>>,
) {
    if module_name_last_component(db, module) == Some("models") {
        if module.file(db).is_none()
            || !module.all_submodules(db).is_empty()
            || module_may_define_django_models(db, env.program(db), module)
        {
            collect_django_model_modules(db, module, modules);
        }
        return;
    }

    if module.file(db).is_none() {
        for &listed_module in list_modules(db, env.program(db).resolver_environment(db)) {
            if listed_module == module || !module_is_under_module(db, listed_module, module) {
                continue;
            }
            if module_name_last_component(db, listed_module) == Some("models") {
                collect_django_project_model_modules_under(db, env, listed_module, modules);
            }
        }
        return;
    }

    for &submodule in module.all_submodules(db) {
        collect_django_project_model_modules_under(db, env, submodule, modules);
    }
}

fn collect_django_project_model_modules<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    anchor_module: Module<'db>,
    modules: &mut Vec<Module<'db>>,
) {
    let Some(anchor_search_path) = anchor_module.search_path(db) else {
        return;
    };

    for &module in list_modules(db, env.program(db).resolver_environment(db)) {
        if module.search_path(db) != Some(anchor_search_path) {
            continue;
        }
        if !module_is_top_level(db, module) {
            continue;
        }
        if module_is_under_top_level(db, module, anchor_module) {
            continue;
        }
        collect_django_project_model_modules_under(db, env, module, modules);
    }
}

#[salsa::tracked(
    returns(deref),
    cycle_initial=|_, _, _| Box::default(),
    heap_size=ruff_memory_usage::heap_size
)]
fn django_model_modules_in_models_module<'db>(
    db: &'db dyn Db,
    models_module: Module<'db>,
) -> Box<[Module<'db>]> {
    let mut modules = Vec::new();
    collect_django_model_modules(db, models_module, &mut modules);
    modules.into_boxed_slice()
}

#[salsa::tracked(
    returns(deref),
    cycle_initial=|_, _, _, _| Box::default(),
    heap_size=ruff_memory_usage::heap_size
)]
fn django_model_modules_under_top_level_package<'db>(
    db: &'db dyn Db,
    program: Program<'db>,
    top_level_module: Module<'db>,
) -> Box<[Module<'db>]> {
    let env = &ProgramEnvironment::from_program(program);
    let mut modules = Vec::new();
    collect_django_model_modules_under(db, env, top_level_module, &mut modules);
    modules.into_boxed_slice()
}

#[salsa::tracked(
    returns(deref),
    cycle_initial=|_, _, _, _| Box::default(),
    heap_size=ruff_memory_usage::heap_size
)]
fn django_project_model_modules_for_anchor<'db>(
    db: &'db dyn Db,
    program: Program<'db>,
    anchor_module: Module<'db>,
) -> Box<[Module<'db>]> {
    let env = &ProgramEnvironment::from_program(program);
    let mut modules = Vec::new();
    collect_django_project_model_modules(db, env, anchor_module, &mut modules);
    modules.into_boxed_slice()
}

#[salsa::tracked(
    returns(deref),
    cycle_initial=|_, _, _, _| Box::default(),
    heap_size=ruff_memory_usage::heap_size
)]
fn django_model_modules_in_search_path<'db>(
    db: &'db dyn Db,
    program: Program<'db>,
    anchor_module: Module<'db>,
) -> Box<[Module<'db>]> {
    let env = &ProgramEnvironment::from_program(program);
    let Some(anchor_search_path) = anchor_module.search_path(db) else {
        return Box::default();
    };

    let mut modules = Vec::new();
    for &module in list_modules(db, env.program(db).resolver_environment(db)) {
        if module.search_path(db) == Some(anchor_search_path) && module_is_top_level(db, module) {
            modules.extend_from_slice(django_model_modules_under_top_level_package(
                db,
                env.program(db),
                module,
            ));
        }
    }
    modules.into_boxed_slice()
}

fn push_django_model_module<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    module: Module<'db>,
    modules: &mut Vec<Module<'db>>,
) {
    let mut new_modules = Vec::new();
    if module_name_last_component(db, module) == Some("models") {
        if module.file(db).is_none()
            || !module.all_submodules(db).is_empty()
            || module_may_define_django_models(db, env.program(db), module)
        {
            collect_django_model_modules(db, module, &mut new_modules);
        }
    } else if module_may_define_django_models(db, env.program(db), module)
        && !django_model_classes_in_module(db, env.program(db), module).is_empty()
    {
        new_modules.push(module);
    }

    for module in new_modules {
        if !modules.contains(&module) {
            modules.push(module);
        }
    }
}

fn push_imported_django_model_module<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    module: Module<'db>,
    modules: &mut Vec<Module<'db>>,
    skip_project_code: bool,
) {
    if skip_project_code && module_is_project_code(db, module) {
        return;
    }
    push_django_model_module(db, env, module, modules);
}

#[salsa::tracked(returns(copy), cycle_initial=|_, _, _, _| false)]
fn module_may_define_django_models<'db>(
    db: &'db dyn Db,
    program: Program<'db>,
    module: Module<'db>,
) -> bool {
    let env = &ProgramEnvironment::from_program(program);
    let Some(file) = module.file(db) else {
        return false;
    };

    let module = parsed_module(db, python_file(db, env, file)).load(db);
    module.suite().iter().any(|stmt| {
        let ast::Stmt::ClassDef(class_def) = stmt else {
            return false;
        };

        class_def.bases().iter().any(class_base_may_be_django_model)
            || class_def.body.iter().any(|stmt| {
                extract_field_assignment(stmt).is_some_and(|(_, call_expr)| {
                    match call_expr.func.as_ref() {
                        ast::Expr::Name(name) => field_class_to_kind(name.id.as_str()).is_some(),
                        ast::Expr::Attribute(attr) => {
                            field_class_to_kind(attr.attr.as_str()).is_some()
                        }
                        _ => false,
                    }
                })
            })
    })
}

fn class_base_may_be_django_model(base: &ast::Expr) -> bool {
    let name = match base {
        ast::Expr::Name(name) => name.id.as_str(),
        ast::Expr::Attribute(attr) => attr.attr.as_str(),
        ast::Expr::Subscript(subscript) => return class_base_may_be_django_model(&subscript.value),
        _ => return false,
    };

    matches!(
        name,
        "Model" | "MPTTModel" | "AbstractUser" | "AbstractBaseUser"
    )
}

#[salsa::tracked(
    returns(deref),
    cycle_initial=|_, _, _, _| Box::default(),
    heap_size=ruff_memory_usage::heap_size
)]
fn django_model_modules_imported_by_file<'db>(
    db: &'db dyn Db,
    program: Program<'db>,
    file: File,
) -> Box<[Module<'db>]> {
    let env = &ProgramEnvironment::from_program(program);
    collect_django_model_modules_imported_by_file(db, env, file, false).into_boxed_slice()
}

#[salsa::tracked(
    returns(deref),
    cycle_initial=|_, _, _, _| Box::default(),
    heap_size=ruff_memory_usage::heap_size
)]
fn third_party_django_model_modules_imported_by_file<'db>(
    db: &'db dyn Db,
    program: Program<'db>,
    file: File,
) -> Box<[Module<'db>]> {
    let env = &ProgramEnvironment::from_program(program);
    collect_django_model_modules_imported_by_file(db, env, file, true).into_boxed_slice()
}

fn collect_django_model_modules_imported_by_file<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    file: File,
    skip_project_code: bool,
) -> Vec<Module<'db>> {
    let module = parsed_module(db, python_file(db, env, file)).load(db);
    let mut modules = Vec::new();

    for stmt in module.suite() {
        match stmt {
            ast::Stmt::Import(import) => {
                for alias in &import.names {
                    let Some(module_name) = ModuleName::new(alias.name.as_str()) else {
                        continue;
                    };
                    if let Some(module) =
                        resolve_module(db, as_importing_file(db, env, file), &module_name)
                    {
                        push_imported_django_model_module(
                            db,
                            env,
                            module,
                            &mut modules,
                            skip_project_code,
                        );
                    }

                    let Some(models_module_name) =
                        ModuleName::new(&format!("{}.models", alias.name.as_str()))
                    else {
                        continue;
                    };
                    if let Some(module) =
                        resolve_module(db, as_importing_file(db, env, file), &models_module_name)
                    {
                        push_imported_django_model_module(
                            db,
                            env,
                            module,
                            &mut modules,
                            skip_project_code,
                        );
                    }
                }
            }
            ast::Stmt::ImportFrom(import_from) => {
                let Ok(module_name) = ModuleName::from_import_statement(
                    db,
                    as_importing_file(db, env, file),
                    import_from,
                ) else {
                    continue;
                };
                if let Some(module) =
                    resolve_module(db, as_importing_file(db, env, file), &module_name)
                {
                    push_imported_django_model_module(
                        db,
                        env,
                        module,
                        &mut modules,
                        skip_project_code,
                    );
                }

                for alias in &import_from.names {
                    let Some(imported_module_name) =
                        ModuleName::new(&format!("{module_name}.{}", alias.name.as_str()))
                    else {
                        continue;
                    };
                    if let Some(module) =
                        resolve_module(db, as_importing_file(db, env, file), &imported_module_name)
                    {
                        push_imported_django_model_module(
                            db,
                            env,
                            module,
                            &mut modules,
                            skip_project_code,
                        );
                    }
                }
            }
            _ => {}
        }
    }

    modules
}

#[salsa::tracked(
    returns(deref),
    cycle_initial=|_, _, _, _| Box::default(),
    heap_size=ruff_memory_usage::heap_size
)]
fn django_model_classes_in_module<'db>(
    db: &'db dyn Db,
    program: Program<'db>,
    module: Module<'db>,
) -> Box<[StaticClassLiteral<'db>]> {
    let env = &ProgramEnvironment::from_program(program);
    let Some(file) = module.file(db) else {
        return Box::default();
    };

    let index = semantic_index(db, program_file(db, env, file));
    let module = parsed_module(db, python_file(db, env, file)).load(db);
    module
        .suite()
        .iter()
        .filter_map(|stmt| {
            let ast::Stmt::ClassDef(class_def) = stmt else {
                return None;
            };
            if class_def.bases().is_empty()
                && !class_def
                    .body
                    .iter()
                    .any(|stmt| extract_field_assignment(stmt).is_some())
            {
                return None;
            }

            let class = static_class_literal_from_class_def(db, env, file, index, class_def);
            (!class.is_known(db, KnownClass::DjangoModel) && class.is_django_model(db))
                .then_some(class)
        })
        .collect()
}

fn static_class_literal_from_class_def<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    file: File,
    index: &SemanticIndex<'db>,
    class_def: &ast::StmtClassDef,
) -> StaticClassLiteral<'db> {
    StaticClassLiteral::new(
        db,
        class_def.name.id.clone(),
        index
            .node_scope(NodeWithScopeRef::Class(class_def))
            .to_scope_id(db, program_file(db, env, file)),
        None,
        None,
        false,
        None,
        None,
        false,
        !class_def.decorator_list.is_empty(),
        class_def.type_params.is_some(),
        !class_def.bases().is_empty(),
        class_def
            .arguments
            .as_deref()
            .is_some_and(|arguments| arguments.find_keyword("metaclass").is_some()),
    )
}

fn local_class_literal_by_name<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    file: File,
    name: &str,
) -> Option<StaticClassLiteral<'db>> {
    let module = parsed_module(db, python_file(db, env, file)).load(db);
    let index = semantic_index(db, program_file(db, env, file));

    module.suite().iter().find_map(|stmt| {
        let ast::Stmt::ClassDef(class_def) = stmt else {
            return None;
        };
        (class_def.name.as_str() == name)
            .then(|| static_class_literal_from_class_def(db, env, file, index, class_def))
    })
}

#[salsa::tracked(returns(copy), cycle_initial=|_, _, _, _, _| false)]
#[allow(clippy::needless_pass_by_value)]
fn module_defines_class_named<'db>(
    db: &'db dyn Db,
    program: Program<'db>,
    module: Module<'db>,
    name: Name,
) -> bool {
    let env = &ProgramEnvironment::from_program(program);
    let Some(file) = module.file(db) else {
        return false;
    };

    let source = source_text(db, file);
    if !source_may_define_class_named(&source, name.as_str()) {
        return false;
    }

    parsed_module(db, python_file(db, env, file))
        .load(db)
        .suite()
        .iter()
        .any(|stmt| matches!(stmt, ast::Stmt::ClassDef(class_def) if class_def.name.as_str() == name.as_str()))
}

fn source_may_define_class_named(source: &str, name: &str) -> bool {
    source.lines().any(|line| {
        let Some(rest) = line.trim_start().strip_prefix("class") else {
            return false;
        };
        if !rest
            .chars()
            .next()
            .is_some_and(|char| char.is_ascii_whitespace())
        {
            return false;
        }
        let Some(suffix) = rest.trim_start().strip_prefix(name) else {
            return false;
        };
        suffix
            .trim_start()
            .chars()
            .next()
            .is_some_and(|char| matches!(char, '(' | ':' | '['))
    })
}

fn expand_reverse_related_name<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    source_name: &str,
    source_file: File,
    related_name: &Name,
) -> Option<Name> {
    if related_name.as_str() == "+" {
        return None;
    }

    let source_name = source_name.to_ascii_lowercase();
    let app_label = django_app_label_for_file(db, env, source_file).unwrap_or_default();
    Some(Name::new(
        related_name
            .as_str()
            .replace("%(class)s", &source_name)
            .replace("%(model_name)s", &source_name)
            .replace("%(app_label)s", &app_label),
    ))
}

#[salsa::tracked(
    returns(deref),
    cycle_initial=|_, _, _, _| Box::default(),
    heap_size=ruff_memory_usage::heap_size
)]
fn possible_reverse_names_in_module<'db>(
    db: &'db dyn Db,
    program: Program<'db>,
    module: Module<'db>,
) -> Box<[Name]> {
    let env = &ProgramEnvironment::from_program(program);
    let Some(file) = module.file(db) else {
        return Box::default();
    };

    let module = parsed_module(db, python_file(db, env, file)).load(db);
    let mut names = FxIndexSet::default();
    let mut app_label = None;
    for stmt in module.suite() {
        let ast::Stmt::ClassDef(class_def) = stmt else {
            continue;
        };
        let source_name = class_def.name.as_str();
        let source_name_lower = source_name.to_ascii_lowercase();

        // Abstract base models commonly use `related_name="%(app_label)s"`.
        // The final reverse accessor is determined by each concrete subclass's
        // app label, even when the field is inherited from another module. We
        // only add this fallback for classes with custom bases so plain
        // `models.Model` declarations do not make the app label a possible
        // reverse name for every model module.
        if class_def
            .bases()
            .iter()
            .any(|base| !class_base_may_be_django_model(base))
        {
            let app_label = app_label
                .get_or_insert_with(|| django_app_label_for_file(db, env, file).map(Name::new));
            let Some(app_label) = app_label else {
                continue;
            };
            names.insert(app_label.clone());
        }

        for stmt in &class_def.body {
            let Some((_, call_expr)) = extract_field_assignment(stmt) else {
                continue;
            };
            if let Some(related_name) = string_keyword(call_expr, "related_name") {
                if let Some(name) =
                    expand_reverse_related_name(db, env, source_name, file, &related_name)
                {
                    names.insert(name);
                }
                continue;
            }

            let kind = match call_expr.func.as_ref() {
                ast::Expr::Name(name) => field_class_to_kind(name.id.as_str()),
                ast::Expr::Attribute(attr) => field_class_to_kind(attr.attr.as_str()),
                _ => None,
            };
            match kind {
                Some(DjangoFieldKind::ForeignKey | DjangoFieldKind::ManyToMany) => {
                    names.insert(Name::new(format!("{source_name_lower}_set")));
                }
                Some(DjangoFieldKind::OneToOne) => {
                    names.insert(Name::new(source_name_lower.clone()));
                }
                Some(_) => {}
                None if has_relation_target_argument(call_expr) => {
                    // Custom relation fields can behave either like one-to-one or to-many
                    // relations. Keep this syntactic filter conservative so custom fields do not
                    // need to be hardcoded here.
                    names.insert(Name::new(source_name_lower.clone()));
                    names.insert(Name::new(format!("{source_name_lower}_set")));
                }
                None => {}
            }
        }
    }

    names.into_iter().collect()
}

fn possible_reverse_name_in_module<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    module: Module<'db>,
    name: &Name,
) -> bool {
    possible_reverse_names_in_module(db, env.program(db), module)
        .iter()
        .any(|possible_name| possible_name == name)
}

#[salsa::tracked(
    returns(deref),
    cycle_initial=|_, _, _, _| Box::default(),
    heap_size=ruff_memory_usage::heap_size
)]
fn possible_reverse_query_names_in_module<'db>(
    db: &'db dyn Db,
    program: Program<'db>,
    module: Module<'db>,
) -> Box<[Name]> {
    let env = &ProgramEnvironment::from_program(program);
    let Some(file) = module.file(db) else {
        return Box::default();
    };

    let module = parsed_module(db, python_file(db, env, file)).load(db);
    let mut names = FxIndexSet::default();
    let mut app_label = None;
    for stmt in module.suite() {
        let ast::Stmt::ClassDef(class_def) = stmt else {
            continue;
        };
        let source_name = class_def.name.as_str();
        let source_name_lower = source_name.to_ascii_lowercase();

        if class_def
            .bases()
            .iter()
            .any(|base| !class_base_may_be_django_model(base))
        {
            let app_label = app_label
                .get_or_insert_with(|| django_app_label_for_file(db, env, file).map(Name::new));
            let Some(app_label) = app_label else {
                continue;
            };
            names.insert(app_label.clone());
        }

        for stmt in &class_def.body {
            let Some((_, call_expr)) = extract_field_assignment(stmt) else {
                continue;
            };

            if let Some(query_name) = string_keyword(call_expr, "related_query_name") {
                if let Some(name) =
                    expand_reverse_related_name(db, env, source_name, file, &query_name)
                {
                    names.insert(name);
                }
                continue;
            }
            if let Some(related_name) = string_keyword(call_expr, "related_name") {
                if let Some(name) =
                    expand_reverse_related_name(db, env, source_name, file, &related_name)
                {
                    names.insert(name);
                }
                continue;
            }

            let kind = match call_expr.func.as_ref() {
                ast::Expr::Name(name) => field_class_to_kind(name.id.as_str()),
                ast::Expr::Attribute(attr) => field_class_to_kind(attr.attr.as_str()),
                _ => None,
            };
            match kind {
                Some(
                    DjangoFieldKind::ForeignKey
                    | DjangoFieldKind::OneToOne
                    | DjangoFieldKind::ManyToMany,
                )
                | None
                    if has_relation_target_argument(call_expr) =>
                {
                    names.insert(Name::new(source_name_lower.clone()));
                }
                _ => {}
            }
        }
    }

    names.into_iter().collect()
}

fn possible_reverse_query_name_in_module<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    module: Module<'db>,
    name: &Name,
) -> bool {
    possible_reverse_query_names_in_module(db, env.program(db), module)
        .iter()
        .any(|possible_name| possible_name == name)
}

#[salsa::tracked(
    returns(deref),
    cycle_initial=|_, _, _, _| Box::default(),
    heap_size=ruff_memory_usage::heap_size
)]
fn django_possible_reverse_names_in_models_module<'db>(
    db: &'db dyn Db,
    program: Program<'db>,
    models_module: Module<'db>,
) -> Box<[Name]> {
    let env = &ProgramEnvironment::from_program(program);
    let mut names = FxIndexSet::default();
    for &module in django_model_modules_in_models_module(db, models_module) {
        names.extend(
            possible_reverse_names_in_module(db, env.program(db), module)
                .iter()
                .cloned(),
        );
    }

    names.into_iter().collect()
}

#[salsa::tracked(
    returns(deref),
    cycle_initial=|_, _, _, _| Box::default(),
    heap_size=ruff_memory_usage::heap_size
)]
fn django_possible_reverse_names_in_top_level_package<'db>(
    db: &'db dyn Db,
    program: Program<'db>,
    top_level_module: Module<'db>,
) -> Box<[Name]> {
    let env = &ProgramEnvironment::from_program(program);
    let mut names = FxIndexSet::default();
    for &models_module in
        django_model_modules_under_top_level_package(db, env.program(db), top_level_module)
    {
        names.extend(
            django_possible_reverse_names_in_models_module(db, env.program(db), models_module)
                .iter()
                .cloned(),
        );
    }

    names.into_iter().collect()
}

#[salsa::tracked(returns(copy), cycle_initial=|_, _, _, _, _| false)]
#[allow(clippy::needless_pass_by_value)]
fn django_possible_reverse_name_in_top_level_package<'db>(
    db: &'db dyn Db,
    program: Program<'db>,
    top_level_module: Module<'db>,
    name: Name,
) -> bool {
    let env = &ProgramEnvironment::from_program(program);
    for &models_module in
        django_model_modules_under_top_level_package(db, env.program(db), top_level_module)
    {
        if django_possible_reverse_names_in_models_module(db, env.program(db), models_module)
            .iter()
            .any(|possible_name| possible_name == &name)
        {
            return true;
        }
    }

    false
}

#[salsa::tracked(
    returns(deref),
    cycle_initial=|_, _, _, _| Box::default(),
    heap_size=ruff_memory_usage::heap_size
)]
fn django_possible_reverse_names_in_project_search_path<'db>(
    db: &'db dyn Db,
    program: Program<'db>,
    anchor_module: Module<'db>,
) -> Box<[Name]> {
    let env = &ProgramEnvironment::from_program(program);
    let mut names = FxIndexSet::default();
    for &models_module in
        django_project_model_modules_for_anchor(db, env.program(db), anchor_module)
    {
        names.extend(
            django_possible_reverse_names_in_models_module(db, env.program(db), models_module)
                .iter()
                .cloned(),
        );
    }

    names.into_iter().collect()
}

#[salsa::tracked(returns(copy), cycle_initial=|_, _, _, _, _| false)]
#[allow(clippy::needless_pass_by_value)]
fn django_possible_reverse_name_in_project_search_path<'db>(
    db: &'db dyn Db,
    program: Program<'db>,
    anchor_module: Module<'db>,
    name: Name,
) -> bool {
    let env = &ProgramEnvironment::from_program(program);
    for &models_module in
        django_project_model_modules_for_anchor(db, env.program(db), anchor_module)
    {
        if django_possible_reverse_names_in_models_module(db, env.program(db), models_module)
            .iter()
            .any(|possible_name| possible_name == &name)
        {
            return true;
        }
    }

    false
}

#[salsa::tracked(returns(copy), cycle_initial=|_, _, _| false)]
fn django_models_module_may_have_type_checking_cycle<'db>(
    db: &'db dyn Db,
    models_module: Module<'db>,
) -> bool {
    django_model_modules_in_models_module(db, models_module)
        .iter()
        .copied()
        .any(|module| {
            module
                .file(db)
                .is_some_and(|file| source_text(db, file).contains("TYPE_CHECKING"))
        })
}

#[salsa::tracked(returns(copy), cycle_initial=|_, _, _, _| false)]
fn django_project_search_path_may_have_type_checking_cycle<'db>(
    db: &'db dyn Db,
    program: Program<'db>,
    anchor_module: Module<'db>,
) -> bool {
    let env = &ProgramEnvironment::from_program(program);
    django_project_model_modules_for_anchor(db, env.program(db), anchor_module)
        .iter()
        .copied()
        .any(|models_module| django_models_module_may_have_type_checking_cycle(db, models_module))
}

#[salsa::tracked(
    returns(deref),
    cycle_initial=|_, _, _, _| Box::default(),
    cycle_fn=|db, cycle, previous, current, _, _| django_reverse_members_cycle_recover(db, cycle, previous, current),
    heap_size=ruff_memory_usage::heap_size
)]
fn django_reverse_members_in_models_module<'db>(
    db: &'db dyn Db,
    program: Program<'db>,
    models_module: Module<'db>,
) -> Box<[DjangoReverseMemberInfo<'db>]> {
    let env = &ProgramEnvironment::from_program(program);
    let mut reverse_members = Vec::new();
    for &module in django_model_modules_in_models_module(db, models_module) {
        let Some(source_file) = module.file(db) else {
            continue;
        };

        for source_model in django_model_classes_in_module(db, env.program(db), module)
            .iter()
            .copied()
        {
            for field in collect_all_django_relation_fields(db, env.program(db), source_model) {
                if !matches!(
                    field.kind,
                    DjangoFieldKind::ForeignKey
                        | DjangoFieldKind::OneToOne
                        | DjangoFieldKind::ManyToMany
                ) {
                    continue;
                }

                let target_model = target_model_for_relation_field(db, env, source_model, field);
                let Some(target_model) = target_model else {
                    continue;
                };
                let Some(name) = reverse_related_name(db, env, source_model, field) else {
                    continue;
                };
                let Some(query_name) = reverse_related_query_name(db, env, source_model, field)
                else {
                    continue;
                };

                reverse_members.push(DjangoReverseMemberInfo {
                    target_model,
                    name,
                    query_name,
                    source_model,
                    source_file,
                    kind: field.kind,
                });
            }
        }
    }

    reverse_members.into_boxed_slice()
}

fn django_reverse_members_named_in_models_module<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    models_module: Module<'db>,
    name: &Name,
) -> Vec<DjangoReverseMemberInfo<'db>> {
    let mut reverse_members = Vec::new();
    for &module in django_model_modules_in_models_module(db, models_module) {
        if !possible_reverse_name_in_module(db, env, module, name) {
            continue;
        }

        let Some(source_file) = module.file(db) else {
            continue;
        };

        for source_model in django_model_classes_in_module(db, env.program(db), module)
            .iter()
            .copied()
        {
            for field in collect_all_django_relation_fields(db, env.program(db), source_model) {
                if !matches!(
                    field.kind,
                    DjangoFieldKind::ForeignKey
                        | DjangoFieldKind::OneToOne
                        | DjangoFieldKind::ManyToMany
                ) {
                    continue;
                }
                if reverse_related_name(db, env, source_model, field) != Some(name.clone()) {
                    continue;
                }

                let target_model = target_model_for_relation_field(db, env, source_model, field);
                let Some(target_model) = target_model else {
                    continue;
                };
                let Some(query_name) = reverse_related_query_name(db, env, source_model, field)
                else {
                    continue;
                };

                reverse_members.push(DjangoReverseMemberInfo {
                    target_model,
                    name: name.clone(),
                    query_name,
                    source_model,
                    source_file,
                    kind: field.kind,
                });
            }
        }
    }

    reverse_members
}

#[salsa::tracked(
    returns(deref),
    cycle_initial=|_, _, _, _, _| Box::default(),
    cycle_fn=|db, cycle, previous, current, _, _, _| django_reverse_members_cycle_recover(db, cycle, previous, current),
    heap_size=ruff_memory_usage::heap_size
)]
#[allow(clippy::needless_pass_by_value)]
fn django_reverse_members_query_named_in_models_module<'db>(
    db: &'db dyn Db,
    program: Program<'db>,
    models_module: Module<'db>,
    query_name: Name,
) -> Box<[DjangoReverseMemberInfo<'db>]> {
    let env = &ProgramEnvironment::from_program(program);
    let mut reverse_members = Vec::new();
    for &module in django_model_modules_in_models_module(db, models_module) {
        if !possible_reverse_query_name_in_module(db, env, module, &query_name) {
            continue;
        }

        let Some(source_file) = module.file(db) else {
            continue;
        };

        for source_model in django_model_classes_in_module(db, env.program(db), module)
            .iter()
            .copied()
        {
            for field in collect_all_django_relation_fields(db, env.program(db), source_model) {
                if !matches!(
                    field.kind,
                    DjangoFieldKind::ForeignKey
                        | DjangoFieldKind::OneToOne
                        | DjangoFieldKind::ManyToMany
                ) {
                    continue;
                }
                if reverse_related_query_name(db, env, source_model, field)
                    != Some(query_name.clone())
                {
                    continue;
                }

                let target_model = target_model_for_relation_field(db, env, source_model, field);
                let Some(target_model) = target_model else {
                    continue;
                };
                let Some(name) = reverse_related_name(db, env, source_model, field) else {
                    continue;
                };

                reverse_members.push(DjangoReverseMemberInfo {
                    target_model,
                    name,
                    query_name: query_name.clone(),
                    source_model,
                    source_file,
                    kind: field.kind,
                });
            }
        }
    }

    reverse_members.into_boxed_slice()
}

#[salsa::tracked(
    returns(deref),
    cycle_initial=|_, _, _, _| Box::default(),
    cycle_fn=|db, cycle, previous, current, _, _| django_reverse_members_cycle_recover(db, cycle, previous, current),
    heap_size=ruff_memory_usage::heap_size
)]
fn django_reverse_members_in_top_level_package<'db>(
    db: &'db dyn Db,
    program: Program<'db>,
    top_level_module: Module<'db>,
) -> Box<[DjangoReverseMemberInfo<'db>]> {
    let env = &ProgramEnvironment::from_program(program);
    let mut reverse_members = Vec::new();
    for &models_module in
        django_model_modules_under_top_level_package(db, env.program(db), top_level_module)
    {
        reverse_members.extend_from_slice(django_reverse_members_in_models_module(
            db,
            env.program(db),
            models_module,
        ));
    }

    reverse_members.into_boxed_slice()
}

#[salsa::tracked(
    returns(deref),
    cycle_initial=|_, _, _, _, _| Box::default(),
    cycle_fn=|db, cycle, previous, current, _, _, _| django_reverse_members_cycle_recover(db, cycle, previous, current),
    heap_size=ruff_memory_usage::heap_size
)]
#[allow(clippy::needless_pass_by_value)]
fn django_reverse_members_named_in_top_level_package<'db>(
    db: &'db dyn Db,
    program: Program<'db>,
    top_level_module: Module<'db>,
    name: Name,
) -> Box<[DjangoReverseMemberInfo<'db>]> {
    let env = &ProgramEnvironment::from_program(program);
    let mut reverse_members = Vec::new();
    for &models_module in
        django_model_modules_under_top_level_package(db, env.program(db), top_level_module)
    {
        if !django_possible_reverse_names_in_models_module(db, env.program(db), models_module)
            .iter()
            .any(|possible_name| possible_name == &name)
        {
            continue;
        }
        reverse_members.extend(django_reverse_members_named_in_models_module(
            db,
            env,
            models_module,
            &name,
        ));
    }

    reverse_members.into_boxed_slice()
}

#[salsa::tracked(
    returns(deref),
    cycle_initial=|_, _, _, _, _| Box::default(),
    cycle_fn=|db, cycle, previous, current, _, _, _| django_reverse_members_cycle_recover(db, cycle, previous, current),
    heap_size=ruff_memory_usage::heap_size
)]
#[allow(clippy::needless_pass_by_value)]
fn django_reverse_members_query_named_in_top_level_package<'db>(
    db: &'db dyn Db,
    program: Program<'db>,
    top_level_module: Module<'db>,
    query_name: Name,
) -> Box<[DjangoReverseMemberInfo<'db>]> {
    let env = &ProgramEnvironment::from_program(program);
    let mut reverse_members = Vec::new();
    for &models_module in
        django_model_modules_under_top_level_package(db, env.program(db), top_level_module)
    {
        reverse_members.extend_from_slice(django_reverse_members_query_named_in_models_module(
            db,
            env.program(db),
            models_module,
            query_name.clone(),
        ));
    }

    reverse_members.into_boxed_slice()
}

#[salsa::tracked(
    returns(deref),
    cycle_initial=|_, _, _, _| Box::default(),
    cycle_fn=|db, cycle, previous, current, _, _| django_reverse_members_cycle_recover(db, cycle, previous, current),
    heap_size=ruff_memory_usage::heap_size
)]
fn django_reverse_members_in_project_search_path<'db>(
    db: &'db dyn Db,
    program: Program<'db>,
    anchor_module: Module<'db>,
) -> Box<[DjangoReverseMemberInfo<'db>]> {
    let env = &ProgramEnvironment::from_program(program);
    let mut reverse_members = Vec::new();
    for &models_module in
        django_project_model_modules_for_anchor(db, env.program(db), anchor_module)
    {
        reverse_members.extend_from_slice(django_reverse_members_in_models_module(
            db,
            env.program(db),
            models_module,
        ));
    }

    reverse_members.into_boxed_slice()
}

#[salsa::tracked(
    returns(deref),
    cycle_initial=|_, _, _, _, _| Box::default(),
    cycle_fn=|db, cycle, previous, current, _, _, _| django_reverse_members_cycle_recover(db, cycle, previous, current),
    heap_size=ruff_memory_usage::heap_size
)]
#[allow(clippy::needless_pass_by_value)]
fn django_reverse_members_named_in_project_search_path<'db>(
    db: &'db dyn Db,
    program: Program<'db>,
    anchor_module: Module<'db>,
    name: Name,
) -> Box<[DjangoReverseMemberInfo<'db>]> {
    let env = &ProgramEnvironment::from_program(program);
    let mut reverse_members = Vec::new();
    for &models_module in
        django_project_model_modules_for_anchor(db, env.program(db), anchor_module)
    {
        if !django_possible_reverse_names_in_models_module(db, env.program(db), models_module)
            .iter()
            .any(|possible_name| possible_name == &name)
        {
            continue;
        }
        reverse_members.extend(django_reverse_members_named_in_models_module(
            db,
            env,
            models_module,
            &name,
        ));
    }

    reverse_members.into_boxed_slice()
}

#[salsa::tracked(
    returns(deref),
    cycle_initial=|_, _, _, _, _| Box::default(),
    cycle_fn=|db, cycle, previous, current, _, _, _| django_reverse_members_cycle_recover(db, cycle, previous, current),
    heap_size=ruff_memory_usage::heap_size
)]
#[allow(clippy::needless_pass_by_value)]
fn django_reverse_members_query_named_in_project_search_path<'db>(
    db: &'db dyn Db,
    program: Program<'db>,
    anchor_module: Module<'db>,
    query_name: Name,
) -> Box<[DjangoReverseMemberInfo<'db>]> {
    let env = &ProgramEnvironment::from_program(program);
    let mut reverse_members = Vec::new();
    for &models_module in
        django_project_model_modules_for_anchor(db, env.program(db), anchor_module)
    {
        reverse_members.extend_from_slice(django_reverse_members_query_named_in_models_module(
            db,
            env.program(db),
            models_module,
            query_name.clone(),
        ));
    }

    reverse_members.into_boxed_slice()
}

#[salsa::tracked(returns(copy), cycle_initial=|_, _, _, _, _| None)]
#[allow(clippy::needless_pass_by_value)]
fn django_model_named_in_top_level_package<'db>(
    db: &'db dyn Db,
    program: Program<'db>,
    top_level_module: Module<'db>,
    name: Name,
) -> Option<StaticClassLiteral<'db>> {
    let env = &ProgramEnvironment::from_program(program);
    let mut matching_model = None;
    for &module in
        django_model_modules_under_top_level_package(db, env.program(db), top_level_module)
    {
        if !module_defines_class_named(db, env.program(db), module, name.clone()) {
            continue;
        }
        for model in django_model_classes_in_module(db, env.program(db), module)
            .iter()
            .copied()
        {
            if model.name(db) == &name {
                if matching_model.is_some() {
                    return None;
                }
                matching_model = Some(model);
            }
        }
    }

    matching_model
}

fn module_path_contains_component<'db>(
    db: &'db dyn Db,
    module: Module<'db>,
    component: &str,
) -> bool {
    module
        .name(db)
        .components()
        .any(|module_component| module_component == component)
}

#[salsa::tracked(returns(copy), cycle_initial=|_, _, _, _, _, _| None)]
#[allow(clippy::needless_pass_by_value)]
fn django_model_named_in_project_app_label<'db>(
    db: &'db dyn Db,
    program: Program<'db>,
    file: File,
    app_label: Name,
    model_name: Name,
) -> Option<StaticClassLiteral<'db>> {
    let env = &ProgramEnvironment::from_program(program);
    let anchor_module = django_top_level_package_for_file(db, env, file)?;

    let mut matching_model = None;
    for &module in django_model_modules_in_search_path(db, env.program(db), anchor_module) {
        if !module_path_contains_component(db, module, app_label.as_str()) {
            continue;
        }
        if !module_defines_class_named(db, env.program(db), module, model_name.clone()) {
            continue;
        }
        for model in django_model_classes_in_module(db, env.program(db), module)
            .iter()
            .copied()
        {
            if model
                .name(db)
                .as_str()
                .eq_ignore_ascii_case(model_name.as_str())
            {
                if matching_model.is_some() {
                    return None;
                }
                matching_model = Some(model);
            }
        }
    }

    matching_model
}

#[salsa::tracked(returns(copy), cycle_initial=|_, _, _, _, _| None)]
#[allow(clippy::needless_pass_by_value)]
fn django_model_named_in_project<'db>(
    db: &'db dyn Db,
    program: Program<'db>,
    file: File,
    model_name: Name,
) -> Option<StaticClassLiteral<'db>> {
    let env = &ProgramEnvironment::from_program(program);
    let anchor_module = django_top_level_package_for_file(db, env, file)?;

    let mut matching_model = None;
    for &module in django_model_modules_in_search_path(db, env.program(db), anchor_module) {
        if !module_defines_class_named(db, env.program(db), module, model_name.clone()) {
            continue;
        }
        for model in django_model_classes_in_module(db, env.program(db), module)
            .iter()
            .copied()
        {
            if model
                .name(db)
                .as_str()
                .eq_ignore_ascii_case(model_name.as_str())
            {
                if matching_model.is_some() {
                    return None;
                }
                matching_model = Some(model);
            }
        }
    }

    matching_model
}

impl<'db> DjangoFieldInfo<'db> {
    /// Return the Python value type for this field when accessed on a model instance.
    pub(super) fn instance_type(
        &self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
    ) -> Type<'db> {
        let base = if let Some(value_type) = self.value_type_override {
            value_type
        } else {
            match self.kind {
                DjangoFieldKind::Char => KnownClass::Str.to_instance(db, env),
                DjangoFieldKind::Integer | DjangoFieldKind::Auto => {
                    KnownClass::Int.to_instance(db, env)
                }
                DjangoFieldKind::Float => KnownClass::Float.to_instance(db, env),
                DjangoFieldKind::Bool => KnownClass::Bool.to_instance(db, env),
                DjangoFieldKind::Date => {
                    resolve_stdlib_instance(db, env, KnownModule::Datetime, "date")
                }
                DjangoFieldKind::DateTime => {
                    resolve_stdlib_instance(db, env, KnownModule::Datetime, "datetime")
                }
                DjangoFieldKind::Time => {
                    resolve_stdlib_instance(db, env, KnownModule::Datetime, "time")
                }
                DjangoFieldKind::Decimal => {
                    resolve_stdlib_instance(db, env, KnownModule::Decimal, "Decimal")
                }
                DjangoFieldKind::Uuid => {
                    resolve_stdlib_instance(db, env, KnownModule::Uuid, "UUID")
                }
                DjangoFieldKind::Binary => KnownClass::Bytes.to_instance(db, env),
                DjangoFieldKind::File => resolve_django_symbol(
                    db,
                    env,
                    self.file,
                    "django.db.models.fields.files",
                    "FieldFile",
                )
                .and_then(|ty| ty.to_instance_approximation(db, env))
                .unwrap_or_else(Type::unknown),
                DjangoFieldKind::Image => resolve_django_symbol(
                    db,
                    env,
                    self.file,
                    "django.db.models.fields.files",
                    "ImageFieldFile",
                )
                .and_then(|ty| ty.to_instance_approximation(db, env))
                .unwrap_or_else(Type::unknown),
                DjangoFieldKind::Json | DjangoFieldKind::GenericForeignKey => Type::unknown(),
                DjangoFieldKind::ForeignKey | DjangoFieldKind::OneToOne => {
                    self.related_model.unwrap_or_else(Type::unknown)
                }
                DjangoFieldKind::ManyToMany => {
                    let Some(related_model) = self.related_model else {
                        return Type::unknown();
                    };
                    synthesize_many_related_manager_instance(db, env, self.file, related_model)
                }
            }
        };

        if self.nullable {
            UnionType::from_two_elements(db, env, base, Type::none(db, env))
        } else {
            base
        }
    }

    fn instance_type_for_model(
        &self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        model_class: StaticClassLiteral<'db>,
    ) -> Type<'db> {
        if self.related_model.is_some() {
            return self.instance_type(db, env);
        }

        if self.related_target.is_none() {
            return self.instance_type(db, env);
        }

        let Some(related_model) = lazy_target_model_for_relation_field(db, env, model_class, self)
        else {
            return self.instance_type(db, env);
        };

        let related_instance = Type::instance(
            db,
            env,
            related_model.apply_optional_specialization(db, None),
        );
        let base = match self.kind {
            DjangoFieldKind::ForeignKey | DjangoFieldKind::OneToOne => related_instance,
            DjangoFieldKind::ManyToMany => {
                synthesize_many_related_manager_instance(db, env, self.file, related_instance)
            }
            _ => return self.instance_type(db, env),
        };

        if self.nullable {
            UnionType::from_two_elements(db, env, base, Type::none(db, env))
        } else {
            base
        }
    }

    fn lookup_exact_type(&self, db: &'db dyn Db, env: &ProgramEnvironment<'db>) -> Type<'db> {
        let base = match self.kind {
            DjangoFieldKind::Integer | DjangoFieldKind::Auto => UnionType::from_two_elements(
                db,
                env,
                KnownClass::Str.to_instance(db, env),
                KnownClass::Int.to_instance(db, env),
            ),
            DjangoFieldKind::Float => KnownClass::Float.to_instance(db, env),
            DjangoFieldKind::Decimal => UnionType::from_elements(
                db,
                env,
                [
                    KnownClass::Str.to_instance(db, env),
                    KnownClass::Int.to_instance(db, env),
                    resolve_stdlib_instance(db, env, KnownModule::Decimal, "Decimal"),
                ],
            ),
            DjangoFieldKind::Date => UnionType::from_two_elements(
                db,
                env,
                KnownClass::Str.to_instance(db, env),
                resolve_stdlib_instance(db, env, KnownModule::Datetime, "date"),
            ),
            DjangoFieldKind::DateTime => UnionType::from_two_elements(
                db,
                env,
                KnownClass::Str.to_instance(db, env),
                resolve_stdlib_instance(db, env, KnownModule::Datetime, "datetime"),
            ),
            DjangoFieldKind::Uuid => UnionType::from_two_elements(
                db,
                env,
                KnownClass::Str.to_instance(db, env),
                resolve_stdlib_instance(db, env, KnownModule::Uuid, "UUID"),
            ),
            DjangoFieldKind::File | DjangoFieldKind::Image => UnionType::from_two_elements(
                db,
                env,
                KnownClass::Str.to_instance(db, env),
                self.instance_type(db, env),
            ),
            DjangoFieldKind::ForeignKey | DjangoFieldKind::OneToOne => {
                let relation_type = self.related_model.unwrap_or_else(Type::unknown);
                if let Some(id_type) = relation_id_type(db, env, self) {
                    UnionType::from_elements(db, env, [relation_type, id_type, Type::none(db, env)])
                } else {
                    UnionType::from_two_elements(db, env, relation_type, Type::none(db, env))
                }
            }
            _ => self.instance_type(db, env),
        };
        let base = if let Some(value_type) = self.value_type_override {
            UnionType::from_two_elements(db, env, base, value_type)
        } else {
            base
        };

        if self.nullable {
            UnionType::from_two_elements(db, env, base, Type::none(db, env))
        } else {
            base
        }
    }
}

/// Map a Django field class name (e.g. `"CharField"`) to its [`DjangoFieldKind`].
fn field_class_to_kind(name: &str) -> Option<DjangoFieldKind> {
    Some(match name {
        "CharField"
        | "TextField"
        | "SlugField"
        | "URLField"
        | "EmailField"
        | "GenericIPAddressField"
        | "IPAddressField"
        | "FilePathField" => DjangoFieldKind::Char,

        "FileField" => DjangoFieldKind::File,
        "ImageField" => DjangoFieldKind::Image,

        "IntegerField"
        | "SmallIntegerField"
        | "BigIntegerField"
        | "PositiveIntegerField"
        | "PositiveSmallIntegerField"
        | "PositiveBigIntegerField" => DjangoFieldKind::Integer,

        "FloatField" => DjangoFieldKind::Float,
        "BooleanField" | "NullBooleanField" => DjangoFieldKind::Bool,
        "DateField" => DjangoFieldKind::Date,
        "DateTimeField" => DjangoFieldKind::DateTime,
        "TimeField" => DjangoFieldKind::Time,
        "DecimalField" => DjangoFieldKind::Decimal,
        "UUIDField" => DjangoFieldKind::Uuid,
        "JSONField" => DjangoFieldKind::Json,
        "BinaryField" => DjangoFieldKind::Binary,
        "AutoField" | "BigAutoField" | "SmallAutoField" => DjangoFieldKind::Auto,
        "ForeignKey" | "ForeignObject" => DjangoFieldKind::ForeignKey,
        "OneToOneField" => DjangoFieldKind::OneToOne,
        "ManyToManyField" => DjangoFieldKind::ManyToMany,
        "GenericForeignKey" => DjangoFieldKind::GenericForeignKey,
        _ => return None,
    })
}

fn class_name_could_be_custom_django_field(name: &str) -> bool {
    !name.ends_with("Manager") && !name.ends_with("QuerySet")
}

/// Walk the MRO of `class_name` to find a recognized Django field base class.
fn resolve_custom_field_kind<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    file: File,
    class_name: &str,
) -> Option<DjangoFieldKind> {
    let scope = global_scope(db, program_file(db, env, file));
    let ty = class_member(db, scope, class_name).ignore_possibly_undefined()?;
    let Type::ClassLiteral(ClassLiteral::Static(lit)) = ty else {
        return None;
    };

    for base in lit.iter_mro(db, None) {
        if let Some(class_type) = base.into_class()
            && let Some((base_lit, _)) = class_type.static_class_literal(db)
            && let Some(kind) = field_class_to_kind(base_lit.name(db).as_str())
        {
            return Some(kind);
        }
    }

    None
}

fn resolve_dotted_model_reference<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    file: File,
    value: &str,
) -> Type<'db> {
    let Some((app_label, model_name)) = value.rsplit_once('.') else {
        return Type::unknown();
    };

    if let Some(model) = django_model_named_in_project_app_label(
        db,
        env.program(db),
        file,
        Name::new(app_label),
        Name::new(model_name),
    ) {
        return Type::instance(db, env, model.apply_optional_specialization(db, None));
    }

    let mut module_names = vec![app_label.to_string(), format!("{app_label}.models")];
    if let Some(top_level_module) = django_top_level_package_for_file(db, env, file)
        && let Some(top_level_name) = top_level_module.name(db).components().next()
    {
        module_names.push(format!("{top_level_name}.{app_label}"));
        module_names.push(format!("{top_level_name}.{app_label}.models"));
    }

    for module_name in module_names {
        let Some(module_name) = ModuleName::new(&module_name) else {
            continue;
        };
        let Some(module) = resolve_module(db, as_importing_file(db, env, file), &module_name)
        else {
            continue;
        };
        if let Some(model) = imported_symbol(
            db,
            env,
            module.file(db).map(|file| program_file(db, env, file)),
            model_name,
            None,
        )
        .place
        .ignore_possibly_undefined()
        .and_then(|ty| ty.to_instance_approximation(db, env))
        {
            return model;
        }
    }

    Type::unknown()
}

pub(crate) fn resolve_auth_user_model_reference<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    file: File,
) -> Type<'db> {
    django_auth_user_model_class(db, env.program(db), file)
        .map(|user_model| {
            Type::instance(db, env, user_model.apply_optional_specialization(db, None))
        })
        .unwrap_or_else(Type::unknown)
}

fn django_settings_string_member<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    file: File,
    name: &str,
) -> Option<String> {
    for module in django_settings_modules_imported_by_file(db, env, file) {
        if let Some(value) = django_settings_module_string_literal_member(db, env, module, name) {
            return Some(value);
        }
        if let Some(value) = django_settings_module_member(db, env, module, name)
            .and_then(Type::as_string_literal)
            .map(|literal| literal.value(db).to_string())
        {
            return Some(value);
        }
    }

    for module in django_project_settings_modules(db, env.program(db), file)
        .iter()
        .copied()
    {
        if let Some(value) = django_settings_module_string_literal_member(db, env, module, name) {
            return Some(value);
        }
        if let Some(value) = django_settings_module_member(db, env, module, name)
            .and_then(Type::as_string_literal)
            .map(|literal| literal.value(db).to_string())
        {
            return Some(value);
        }
    }

    None
}

#[salsa::tracked(returns(copy), cycle_initial=|_, _, _, _| None)]
fn django_auth_user_model_class<'db>(
    db: &'db dyn Db,
    program: Program<'db>,
    file: File,
) -> Option<StaticClassLiteral<'db>> {
    let env = &ProgramEnvironment::from_program(program);
    if let Some(auth_user_model) = django_settings_string_member(db, env, file, "AUTH_USER_MODEL") {
        let resolved_model = resolve_dotted_model_reference(db, env, file, &auth_user_model);
        let resolved_class = static_class_from_instance(db, env, resolved_model);
        if let Some(user_model) = resolved_class {
            return Some(user_model);
        }
    }

    if let Some(top_level_module) = django_top_level_package_for_file(db, env, file)
        && let Some(user_model) = django_model_named_in_top_level_package(
            db,
            env.program(db),
            top_level_module,
            Name::new_static("User"),
        )
    {
        return Some(user_model);
    }

    django_model_named_in_project(db, env.program(db), file, Name::new_static("User"))
}

fn is_auth_user_model_reference(expr: &ast::Expr) -> bool {
    match expr {
        ast::Expr::Attribute(attr) => {
            attr.attr.as_str() == "AUTH_USER_MODEL"
                && matches!(
                    attr.value.as_ref(),
                    ast::Expr::Name(name) if name.id.as_str() == "settings"
                )
        }
        ast::Expr::Call(call) => {
            matches!(
                call.func.as_ref(),
                ast::Expr::Name(name) if name.id.as_str() == "getattr"
            ) && matches!(
                &call.arguments.args[..],
                [
                    ast::Expr::Name(settings),
                    ast::Expr::StringLiteral(setting_name),
                    ..
                ] if settings.id.as_str() == "settings"
                    && setting_name.value.to_str() == "AUTH_USER_MODEL"
            )
        }
        _ => false,
    }
}

fn is_mptt_model_class<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    class: StaticClassLiteral<'db>,
) -> bool {
    class.iter_mro(db, None).any(|base| {
        let Some(class_type) = base.into_class() else {
            return false;
        };
        let Some((base_lit, _)) = class_type.static_class_literal(db) else {
            return false;
        };

        base_lit.name(db).as_str() == "MPTTModel"
            && file_to_module(db, resolver_file(db, env, base_lit.file(db)))
                .is_some_and(|module| module.name(db).as_str() == "mptt.models")
    })
}

fn mptt_model_instance_member<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    class: StaticClassLiteral<'db>,
    name: &str,
) -> Option<Type<'db>> {
    if !matches!(name, "level" | "lft" | "rght" | "tree_id") || !is_mptt_model_class(db, env, class)
    {
        return None;
    }

    Some(KnownClass::Int.to_instance(db, env))
}

/// Resolve the target model for a `ForeignKey` or `OneToOneField`.
///
/// Handles `ForeignKey(Author)`, `ForeignKey(to=Author)`, `ForeignKey("Author")`,
/// and `ForeignKey("self")`. Returns `Unknown` for targets that cannot be statically
/// resolved.
fn resolve_related_model<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    file: File,
    self_class: StaticClassLiteral<'db>,
    call_expr: &ast::ExprCall,
) -> Type<'db> {
    let scope = global_scope(db, program_file(db, env, file));
    let resolve_name = |name: &str| -> Type<'db> {
        class_member(db, scope, name)
            .ignore_possibly_undefined()
            .and_then(|ty| ty.to_instance_approximation(db, env))
            .unwrap_or_else(Type::unknown)
    };

    // The `to=` keyword takes precedence, matching Django's argument resolution order.
    let to_kwarg = call_expr
        .arguments
        .keywords
        .iter()
        .find_map(|kw| (kw.arg.as_deref() == Some("to")).then_some(&kw.value));
    let target_expr = to_kwarg.or_else(|| call_expr.arguments.args.first());

    match target_expr {
        Some(ast::Expr::Name(name_expr)) => resolve_name(name_expr.id.as_str()),
        Some(expr) if is_auth_user_model_reference(expr) => {
            resolve_auth_user_model_reference(db, env, file)
        }
        Some(ast::Expr::StringLiteral(string_lit)) => {
            let value = string_lit.value.to_str();
            if value == "self" {
                Type::instance(db, env, self_class.apply_optional_specialization(db, None))
            } else if value.contains('.') {
                resolve_dotted_model_reference(db, env, file, value)
            } else {
                resolve_name(value)
            }
        }
        _ => Type::unknown(),
    }
}

/// Collect all Django field declarations across the class hierarchy.
///
/// Iterates the MRO in ancestor-first order so that child fields with the same
/// name override parent fields.
#[salsa::tracked(
    returns(deref),
    cycle_initial=|_, _, _, _| Box::default(),
    heap_size=ruff_memory_usage::heap_size
)]
fn collect_all_django_fields<'db>(
    db: &'db dyn Db,
    program: Program<'db>,
    class: StaticClassLiteral<'db>,
) -> Box<[DjangoFieldInfo<'db>]> {
    let env = &ProgramEnvironment::from_program(program);
    let mut fields: FxIndexMap<Name, DjangoFieldInfo<'db>> = FxIndexMap::default();

    for base in class.iter_mro(db, None).rev() {
        let Some(class_type) = base.into_class() else {
            continue;
        };
        let Some((base_lit, _)) = class_type.static_class_literal(db) else {
            continue;
        };
        if base_lit.is_known(db, KnownClass::DjangoModel) || !base_lit.is_django_model(db) {
            continue;
        }
        for field in base_lit.django_model_fields(db) {
            fields.insert(field.name.clone(), field.clone());
        }
        if !django_model_is_effectively_abstract_for_parent_link(db, env.program(db), base_lit) {
            for &parent in direct_concrete_django_model_bases(db, env.program(db), base_lit) {
                let field = django_model_parent_link_field(db, env, base_lit, parent);
                fields.insert(field.name.clone(), field);
            }
        }
    }

    fields.into_values().collect::<Vec<_>>().into_boxed_slice()
}

fn direct_base_name(expr: &ast::Expr) -> Option<&str> {
    match expr {
        ast::Expr::Name(name) => Some(name.id.as_str()),
        ast::Expr::Attribute(attribute) => Some(attribute.attr.as_str()),
        ast::Expr::Subscript(subscript) => direct_base_name(&subscript.value),
        _ => None,
    }
}

fn direct_base_class<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    file: File,
    expr: &ast::Expr,
) -> Option<StaticClassLiteral<'db>> {
    match expr {
        ast::Expr::Name(name) => resolve_class_in_scope(db, env, file, name.id.as_str()),
        ast::Expr::Attribute(attribute) => imported_symbol(
            db,
            env,
            Some(program_file(db, env, file)),
            attribute.attr.as_str(),
            None,
        )
        .place
        .ignore_possibly_undefined()
        .and_then(|ty| ty.to_class_type(db))
        .and_then(|class| class.static_class_literal(db).map(|(class, _)| class)),
        ast::Expr::Subscript(subscript) => direct_base_class(db, env, file, &subscript.value),
        _ => None,
    }
}

#[salsa::tracked(
    returns(deref),
    cycle_initial=|_, _, _, _| Box::default(),
    heap_size=ruff_memory_usage::heap_size
)]
fn direct_concrete_django_model_bases<'db>(
    db: &'db dyn Db,
    program: Program<'db>,
    class: StaticClassLiteral<'db>,
) -> Box<[StaticClassLiteral<'db>]> {
    let env = &ProgramEnvironment::from_program(program);
    let file = class.file(db);
    let module = parsed_module(db, python_file(db, env, file)).load(db);
    let class_stmt = class.node(db, &module);
    let Some(arguments) = class_stmt.arguments.as_deref() else {
        return Box::default();
    };

    let direct_base_names: FxIndexSet<Name> = arguments
        .args
        .iter()
        .filter_map(direct_base_name)
        .map(Name::new)
        .collect();
    let direct_base_classes: FxIndexSet<StaticClassLiteral<'db>> = arguments
        .args
        .iter()
        .filter_map(|base| direct_base_class(db, env, file, base))
        .collect();
    if direct_base_names.is_empty() && direct_base_classes.is_empty() {
        return Box::default();
    }

    class
        .iter_mro(db, None)
        .filter_map(super::super::class_base::ClassBase::into_class)
        .filter_map(|base| base.static_class_literal(db).map(|(base, _)| base))
        .filter(|base| *base != class)
        .filter(|base| {
            (direct_base_classes.contains(base) || direct_base_names.contains(base.name(db)))
                && !base.is_known(db, KnownClass::DjangoModel)
                && base.is_django_model(db)
                && !django_model_is_effectively_abstract_for_parent_link(db, env.program(db), *base)
        })
        .collect::<Vec<_>>()
        .into_boxed_slice()
}

#[salsa::tracked(returns(copy), cycle_initial=|_, _, _, _| false)]
fn django_model_is_effectively_abstract_for_parent_link<'db>(
    db: &'db dyn Db,
    program: Program<'db>,
    class: StaticClassLiteral<'db>,
) -> bool {
    let env = &ProgramEnvironment::from_program(program);
    django_model_is_abstract(db, env.program(db), class)
        || class.name(db).as_str().starts_with("Abstract")
}

fn django_model_parent_link_field<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    class: StaticClassLiteral<'db>,
    parent: StaticClassLiteral<'db>,
) -> DjangoFieldInfo<'db> {
    let parent_name = parent.name(db).as_str().to_ascii_lowercase();
    DjangoFieldInfo {
        name: Name::new(format!("{parent_name}_ptr")),
        file: class.file(db),
        class_name: "OneToOneField".to_string(),
        kind: DjangoFieldKind::OneToOne,
        nullable: false,
        primary_key: true,
        has_choices: false,
        value_type_override: None,
        related_model: Some(Type::instance(db, env, parent.default_specialization(db))),
        related_model_is_auth_user: false,
        related_target: Some(DjangoRelationTarget::Name(parent.name(db).clone())),
        related_name: None,
        related_query_name: None,
        to_field: None,
    }
}

#[salsa::tracked(
    returns(deref),
    cycle_initial=|_, _, _, _| Box::default(),
    heap_size=ruff_memory_usage::heap_size
)]
fn collect_all_django_relation_fields<'db>(
    db: &'db dyn Db,
    program: Program<'db>,
    class: StaticClassLiteral<'db>,
) -> Box<[DjangoFieldInfo<'db>]> {
    let env = &ProgramEnvironment::from_program(program);
    let mut fields: FxIndexMap<Name, DjangoFieldInfo<'db>> = FxIndexMap::default();

    for base in class.iter_mro(db, None).rev() {
        let Some(class_type) = base.into_class() else {
            continue;
        };
        let Some((base_lit, _)) = class_type.static_class_literal(db) else {
            continue;
        };
        if base_lit.is_known(db, KnownClass::DjangoModel) || !base_lit.is_django_model(db) {
            continue;
        }
        for field in base_lit.django_model_relation_fields(db) {
            fields.insert(field.name.clone(), field.clone());
        }
        if !django_model_is_effectively_abstract_for_parent_link(db, env.program(db), base_lit) {
            for &parent in direct_concrete_django_model_bases(db, env.program(db), base_lit) {
                let field = django_model_parent_link_field(db, env, base_lit, parent);
                fields.insert(field.name.clone(), field);
            }
        }
    }

    fields.into_values().collect::<Vec<_>>().into_boxed_slice()
}

/// Return the type of `pk`: the field with `primary_key=True`, falling back to
/// any `AutoField`, falling back to `int`. Nullability is always stripped.
fn resolve_pk_type<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    fields: &[DjangoFieldInfo<'db>],
) -> Type<'db> {
    fields
        .iter()
        .find(|f| f.primary_key)
        .or_else(|| {
            fields
                .iter()
                .find(|f| matches!(f.kind, DjangoFieldKind::Auto))
        })
        .map(|f| {
            DjangoFieldInfo {
                nullable: false,
                ..f.clone()
            }
            .instance_type(db, env)
        })
        .unwrap_or_else(|| KnownClass::Int.to_instance(db, env))
}

fn resolve_pk_lookup_type<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    fields: &[DjangoFieldInfo<'db>],
) -> Type<'db> {
    fields
        .iter()
        .find(|f| f.primary_key)
        .or_else(|| {
            fields
                .iter()
                .find(|f| matches!(f.kind, DjangoFieldKind::Auto))
        })
        .map(|f| {
            DjangoFieldInfo {
                nullable: false,
                ..f.clone()
            }
            .lookup_exact_type(db, env)
        })
        .unwrap_or_else(|| {
            UnionType::from_two_elements(
                db,
                env,
                KnownClass::Str.to_instance(db, env),
                KnownClass::Int.to_instance(db, env),
            )
        })
}

fn relation_id_type<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    field: &DjangoFieldInfo<'db>,
) -> Option<Type<'db>> {
    if !matches!(
        field.kind,
        DjangoFieldKind::ForeignKey | DjangoFieldKind::OneToOne
    ) {
        return None;
    }

    let related_model = field.related_model?;
    let Some(related_class) = static_class_from_instance(db, env, related_model) else {
        return Some(Type::unknown());
    };

    let related_fields = collect_all_django_fields(db, env.program(db), related_class);
    let id_type = field
        .to_field
        .as_ref()
        .and_then(|to_field| {
            related_fields
                .iter()
                .find(|related_field| related_field.name == *to_field)
        })
        .map(|target_field| {
            DjangoFieldInfo {
                nullable: false,
                ..target_field.clone()
            }
            .instance_type(db, env)
        })
        .unwrap_or_else(|| resolve_pk_type(db, env, related_fields));

    Some(if field.nullable {
        UnionType::from_two_elements(db, env, id_type, Type::none(db, env))
    } else {
        id_type
    })
}

fn relation_id_type_for_model<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    model_class: StaticClassLiteral<'db>,
    field: &DjangoFieldInfo<'db>,
) -> Option<Type<'db>> {
    if !matches!(
        field.kind,
        DjangoFieldKind::ForeignKey | DjangoFieldKind::OneToOne
    ) {
        return None;
    }

    let Some(related_class) = lazy_target_model_for_relation_field(db, env, model_class, field)
    else {
        let id_type = UnionType::from_two_elements(
            db,
            env,
            KnownClass::Str.to_instance(db, env),
            KnownClass::Int.to_instance(db, env),
        );
        return Some(if field.nullable {
            UnionType::from_two_elements(db, env, id_type, Type::none(db, env))
        } else {
            id_type
        });
    };

    let related_fields = collect_all_django_fields(db, env.program(db), related_class);
    let id_type = field
        .to_field
        .as_ref()
        .and_then(|to_field| {
            related_fields
                .iter()
                .find(|related_field| related_field.name == *to_field)
        })
        .map(|target_field| {
            DjangoFieldInfo {
                nullable: false,
                ..target_field.clone()
            }
            .instance_type_for_model(db, env, related_class)
        })
        .unwrap_or_else(|| resolve_pk_type(db, env, related_fields));

    Some(if field.nullable {
        UnionType::from_two_elements(db, env, id_type, Type::none(db, env))
    } else {
        id_type
    })
}

fn relation_id_lookup_type_for_model<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    model_class: StaticClassLiteral<'db>,
    field: &DjangoFieldInfo<'db>,
) -> Option<Type<'db>> {
    if !matches!(
        field.kind,
        DjangoFieldKind::ForeignKey | DjangoFieldKind::OneToOne
    ) {
        return None;
    }

    let Some(related_class) = lazy_target_model_for_relation_field(db, env, model_class, field)
    else {
        let id_type = UnionType::from_two_elements(
            db,
            env,
            KnownClass::Str.to_instance(db, env),
            KnownClass::Int.to_instance(db, env),
        );
        return Some(UnionType::from_two_elements(
            db,
            env,
            id_type,
            Type::none(db, env),
        ));
    };

    let related_fields = collect_all_django_fields(db, env.program(db), related_class);
    let id_type = field
        .to_field
        .as_ref()
        .and_then(|to_field| {
            related_fields
                .iter()
                .find(|related_field| related_field.name == *to_field)
        })
        .map(|target_field| {
            DjangoFieldInfo {
                nullable: false,
                ..target_field.clone()
            }
            .lookup_exact_type(db, env)
        })
        .unwrap_or_else(|| resolve_pk_lookup_type(db, env, related_fields));

    Some(UnionType::from_two_elements(
        db,
        env,
        id_type,
        Type::none(db, env),
    ))
}

fn many_to_many_lookup_type<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    model_class: StaticClassLiteral<'db>,
    field: &DjangoFieldInfo<'db>,
) -> Option<Type<'db>> {
    if !matches!(field.kind, DjangoFieldKind::ManyToMany) {
        return None;
    }

    let related_class = lazy_target_model_for_relation_field(db, env, model_class, field)?;
    let related_model = Type::instance(
        db,
        env,
        related_class.apply_optional_specialization(db, None),
    );
    let related_pk_type = resolve_pk_lookup_type(
        db,
        env,
        collect_all_django_fields(db, env.program(db), related_class),
    );
    Some(UnionType::from_elements(
        db,
        env,
        [related_model, related_pk_type, Type::none(db, env)],
    ))
}

fn relation_lookup_id_field_name(name: &str) -> Option<&str> {
    name.strip_suffix("_id")
        .or_else(|| name.strip_suffix("_pk"))
}

pub(crate) fn django_lookup_suffix_type<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    suffix: &str,
    base_type: Type<'db>,
) -> DjangoLookupExpectedType<'db> {
    django_lookup_suffix_type_if_known(db, env, suffix, base_type)
        .unwrap_or(DjangoLookupExpectedType::Dynamic)
}

fn django_lookup_suffix_type_if_known<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    suffix: &str,
    base_type: Type<'db>,
) -> Option<DjangoLookupExpectedType<'db>> {
    match suffix {
        "exact" | "iexact" | "lt" | "lte" | "gt" | "gte" | "contains" | "icontains"
        | "startswith" | "istartswith" | "endswith" | "iendswith" | "year" | "iso_year"
        | "month" | "day" | "week" | "week_day" | "iso_week_day" | "quarter" | "hour"
        | "minute" | "second" => Some(DjangoLookupExpectedType::Expected(base_type)),
        "isnull" => Some(DjangoLookupExpectedType::Expected(
            KnownClass::Bool.to_instance(db, env),
        )),
        // These lookups expect containers, pairs, query expressions, or backend-specific
        // values. Keep them permissive until ty has a richer Django lookup model.
        "in" | "range" | "regex" | "iregex" => Some(DjangoLookupExpectedType::Dynamic),
        _ => None,
    }
}

fn django_model_lookup_path_type<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    class: StaticClassLiteral<'db>,
    path: &[&str],
) -> DjangoLookupExpectedType<'db> {
    let Some((head, tail)) = path.split_first() else {
        return DjangoLookupExpectedType::Dynamic;
    };

    let all_fields = collect_all_django_fields(db, env.program(db), class);
    let (field_type, related_class) = match *head {
        "pk" => (resolve_pk_lookup_type(db, env, all_fields), None),
        "id" => {
            let ty = all_fields
                .iter()
                .find(|field| field.name.as_str() == "id")
                .map(|field| field.lookup_exact_type(db, env))
                .unwrap_or_else(|| resolve_pk_lookup_type(db, env, all_fields));
            (ty, None)
        }
        name => {
            if let Some(field_name) = relation_lookup_id_field_name(name)
                && let Some(field) = all_fields
                    .iter()
                    .find(|field| field.name.as_str() == field_name)
                && let Some(id_type) = relation_id_lookup_type_for_model(db, env, class, field)
            {
                (id_type, None)
            } else {
                let Some(field) = all_fields.iter().find(|field| field.name.as_str() == name)
                else {
                    if let Some(mptt_field_type) = mptt_model_instance_member(db, env, class, name)
                    {
                        return if tail.is_empty() {
                            DjangoLookupExpectedType::Expected(mptt_field_type)
                        } else {
                            django_lookup_suffix_type(db, env, tail[0], mptt_field_type)
                        };
                    }

                    let Some(source_model) =
                        django_reverse_query_source_model(db, env, class, name, false)
                    else {
                        return DjangoLookupExpectedType::UnknownField;
                    };
                    let source_instance = Type::instance(
                        db,
                        env,
                        source_model.apply_optional_specialization(db, None),
                    );
                    return if tail.is_empty() {
                        DjangoLookupExpectedType::Expected(source_instance)
                    } else if let Some(suffix_ty) =
                        django_lookup_suffix_type_if_known(db, env, tail[0], source_instance)
                    {
                        suffix_ty
                    } else {
                        django_model_lookup_path_type(db, env, source_model, tail)
                    };
                };

                let mut ty = field.lookup_exact_type(db, env);
                if matches!(
                    field.kind,
                    DjangoFieldKind::ForeignKey | DjangoFieldKind::OneToOne
                ) && let Some(id_type) = relation_id_lookup_type_for_model(db, env, class, field)
                {
                    ty = UnionType::from_two_elements(db, env, ty, id_type);
                } else if let Some(many_to_many_type) =
                    many_to_many_lookup_type(db, env, class, field)
                {
                    ty = many_to_many_type;
                }
                let related_class = matches!(
                    field.kind,
                    DjangoFieldKind::ForeignKey
                        | DjangoFieldKind::OneToOne
                        | DjangoFieldKind::ManyToMany
                )
                .then(|| lazy_target_model_for_relation_field(db, env, class, field))
                .flatten();
                (ty, related_class)
            }
        }
    };

    if tail.is_empty() {
        return DjangoLookupExpectedType::Expected(field_type);
    }

    let Some(related_class) = related_class else {
        return django_lookup_suffix_type(db, env, tail[0], field_type);
    };
    if let [suffix] = tail
        && let Some(suffix_ty) = django_lookup_suffix_type_if_known(db, env, suffix, field_type)
    {
        return suffix_ty;
    }

    django_model_lookup_path_type(db, env, related_class, tail)
}

pub(crate) fn django_lookup_expected_type<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    model_instance: Type<'db>,
    lookup: &str,
) -> DjangoLookupExpectedType<'db> {
    let Some(model_class) = static_class_from_instance(db, env, model_instance) else {
        return DjangoLookupExpectedType::Dynamic;
    };
    if !model_class.is_django_model(db) {
        return DjangoLookupExpectedType::Dynamic;
    }

    let parts: Vec<_> = lookup.split("__").collect();
    django_model_lookup_path_type(db, env, model_class, &parts)
}

fn django_reverse_query_source_model<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    target_model: StaticClassLiteral<'db>,
    member_name: &str,
    require_unique: bool,
) -> Option<StaticClassLiteral<'db>> {
    let reverse_member_name = Name::new(member_name);

    let reverse_member_matches = |reverse_member: &DjangoReverseMemberInfo<'db>| {
        reverse_member.target_model == target_model
            && (!require_unique || matches!(reverse_member.kind, DjangoFieldKind::OneToOne))
    };

    if let Some(top_level_package) =
        django_top_level_package_for_file(db, env, target_model.file(db))
    {
        for reverse_member in django_reverse_members_query_named_in_top_level_package(
            db,
            env.program(db),
            top_level_package,
            reverse_member_name.clone(),
        ) {
            if reverse_member_matches(reverse_member) {
                return Some(reverse_member.source_model);
            }
        }

        for reverse_member in django_reverse_members_query_named_in_project_search_path(
            db,
            env.program(db),
            top_level_package,
            reverse_member_name.clone(),
        ) {
            if reverse_member_matches(reverse_member) {
                return Some(reverse_member.source_model);
            }
        }
    }

    if let Some(models_module) = django_models_module_for_file(db, env, target_model.file(db)) {
        for reverse_member in django_reverse_members_query_named_in_models_module(
            db,
            env.program(db),
            models_module,
            reverse_member_name.clone(),
        ) {
            if reverse_member_matches(reverse_member) {
                return Some(reverse_member.source_model);
            }
        }
    }

    let file = target_model.file(db);
    for source_model in django_model_classes_in_module(
        db,
        env.program(db),
        file_to_module(db, resolver_file(db, env, file))?,
    )
    .iter()
    .copied()
    {
        if source_model == target_model {
            continue;
        }
        for field in collect_all_django_relation_fields(db, env.program(db), source_model) {
            if !matches!(
                field.kind,
                DjangoFieldKind::ForeignKey
                    | DjangoFieldKind::OneToOne
                    | DjangoFieldKind::ManyToMany
            ) || (require_unique && !matches!(field.kind, DjangoFieldKind::OneToOne))
            {
                continue;
            }
            if django_relation_targets_model(db, env, source_model, field, target_model)
                && reverse_related_query_name(db, env, source_model, field)
                    == Some(reverse_member_name.clone())
            {
                return Some(source_model);
            }
        }
    }

    None
}

fn django_model_select_related_path<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    class: StaticClassLiteral<'db>,
    path: &[&str],
) -> DjangoRelationLookup {
    let Some((head, tail)) = path.split_first() else {
        return DjangoRelationLookup::Dynamic;
    };

    let all_fields = collect_all_django_fields(db, env.program(db), class);
    let Some(field) = all_fields.iter().find(|field| field.name.as_str() == *head) else {
        let Some(source_model) = django_reverse_query_source_model(db, env, class, head, true)
        else {
            return DjangoRelationLookup::UnknownField;
        };
        return if tail.is_empty() {
            DjangoRelationLookup::Valid
        } else {
            django_model_select_related_path(db, env, source_model, tail)
        };
    };

    if !matches!(
        field.kind,
        DjangoFieldKind::ForeignKey | DjangoFieldKind::OneToOne
    ) {
        return DjangoRelationLookup::NotRelation;
    }

    if tail.is_empty() {
        return DjangoRelationLookup::Valid;
    }

    let Some(related_model) = field.related_model else {
        return DjangoRelationLookup::Dynamic;
    };
    let Some(related_class) = static_class_from_instance(db, env, related_model) else {
        return DjangoRelationLookup::Dynamic;
    };

    django_model_select_related_path(db, env, related_class, tail)
}

pub(crate) fn django_select_related_lookup<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    model_instance: Type<'db>,
    lookup: &str,
) -> DjangoRelationLookup {
    let Some(model_class) = static_class_from_instance(db, env, model_instance) else {
        return DjangoRelationLookup::Dynamic;
    };
    if !model_class.is_django_model(db) {
        return DjangoRelationLookup::Dynamic;
    }

    let parts: Vec<_> = lookup.split("__").collect();
    django_model_select_related_path(db, env, model_class, &parts)
}

fn django_model_prefetch_related_model<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    class: StaticClassLiteral<'db>,
    path: &[&str],
) -> Option<Type<'db>> {
    let (head, tail) = path.split_first()?;

    let all_fields = collect_all_django_fields(db, env.program(db), class);
    let Some(field) = all_fields.iter().find(|field| field.name.as_str() == *head) else {
        let reverse_member = django_reverse_member_by_name(db, env, class, head)?;
        let source_model = Type::instance(
            db,
            env,
            reverse_member
                .source_model
                .apply_optional_specialization(db, None),
        );
        return if tail.is_empty() {
            Some(source_model)
        } else {
            django_model_prefetch_related_model(db, env, reverse_member.source_model, tail)
        };
    };
    if !matches!(
        field.kind,
        DjangoFieldKind::ForeignKey | DjangoFieldKind::OneToOne | DjangoFieldKind::ManyToMany
    ) {
        return None;
    }

    let related_class = lazy_target_model_for_relation_field(db, env, class, field)?;
    let related_model = Type::instance(
        db,
        env,
        related_class.apply_optional_specialization(db, None),
    );
    if tail.is_empty() {
        return Some(related_model);
    }

    django_model_prefetch_related_model(db, env, related_class, tail)
}

pub(crate) fn django_prefetch_related_model<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    model_instance: Type<'db>,
    lookup: &str,
) -> Option<Type<'db>> {
    let model_class = static_class_from_instance(db, env, model_instance)?;
    if !model_class.is_django_model(db) {
        return None;
    }

    let parts: Vec<_> = lookup.split("__").collect();
    django_model_prefetch_related_model(db, env, model_class, &parts)
}

fn django_model_prefetch_related_path<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    class: StaticClassLiteral<'db>,
    path: &[&str],
) -> DjangoRelationLookup {
    let Some((head, tail)) = path.split_first() else {
        return DjangoRelationLookup::Dynamic;
    };

    let all_fields = collect_all_django_fields(db, env.program(db), class);
    let Some(field) = all_fields.iter().find(|field| field.name.as_str() == *head) else {
        let Some(reverse_member) = django_reverse_member_by_name(db, env, class, head) else {
            return DjangoRelationLookup::UnknownField;
        };
        return if tail.is_empty() {
            DjangoRelationLookup::Valid
        } else {
            django_model_prefetch_related_path(db, env, reverse_member.source_model, tail)
        };
    };
    if matches!(field.kind, DjangoFieldKind::GenericForeignKey) {
        return if tail.is_empty() {
            DjangoRelationLookup::Valid
        } else {
            DjangoRelationLookup::Dynamic
        };
    }
    if !matches!(
        field.kind,
        DjangoFieldKind::ForeignKey | DjangoFieldKind::OneToOne | DjangoFieldKind::ManyToMany
    ) {
        return DjangoRelationLookup::NotRelation;
    }

    if tail.is_empty() {
        return DjangoRelationLookup::Valid;
    }

    let Some(related_model) = field.related_model else {
        return DjangoRelationLookup::Dynamic;
    };
    let Some(related_class) = static_class_from_instance(db, env, related_model) else {
        return DjangoRelationLookup::Dynamic;
    };

    django_model_prefetch_related_path(db, env, related_class, tail)
}

pub(crate) fn django_prefetch_related_lookup<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    model_instance: Type<'db>,
    lookup: &str,
) -> DjangoRelationLookup {
    let Some(model_class) = static_class_from_instance(db, env, model_instance) else {
        return DjangoRelationLookup::Dynamic;
    };
    if !model_class.is_django_model(db) {
        return DjangoRelationLookup::Dynamic;
    }

    let parts: Vec<_> = lookup.split("__").collect();
    django_model_prefetch_related_path(db, env, model_class, &parts)
}

fn django_model_generic_prefetch_related_path<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    class: StaticClassLiteral<'db>,
    path: &[&str],
) -> DjangoRelationLookup {
    let Some((head, tail)) = path.split_first() else {
        return DjangoRelationLookup::Dynamic;
    };

    let all_fields = collect_all_django_fields(db, env.program(db), class);
    let Some(field) = all_fields.iter().find(|field| field.name.as_str() == *head) else {
        return DjangoRelationLookup::UnknownField;
    };
    if !matches!(field.kind, DjangoFieldKind::GenericForeignKey) {
        return DjangoRelationLookup::NotRelation;
    }

    if tail.is_empty() {
        DjangoRelationLookup::Valid
    } else {
        DjangoRelationLookup::Dynamic
    }
}

pub(crate) fn django_generic_prefetch_related_lookup<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    model_instance: Type<'db>,
    lookup: &str,
) -> DjangoRelationLookup {
    let Some(model_class) = static_class_from_instance(db, env, model_instance) else {
        return DjangoRelationLookup::Dynamic;
    };
    if !model_class.is_django_model(db) {
        return DjangoRelationLookup::Dynamic;
    }

    let parts: Vec<_> = lookup.split("__").collect();
    django_model_generic_prefetch_related_path(db, env, model_class, &parts)
}

pub(crate) fn django_bulk_field_lookup<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    model_instance: Type<'db>,
    field_name: &str,
    allow_primary_key: bool,
) -> DjangoBulkFieldLookup {
    let Some(model_class) = static_class_from_instance(db, env, model_instance) else {
        return DjangoBulkFieldLookup::UnknownField;
    };
    if !model_class.is_django_model(db) {
        return DjangoBulkFieldLookup::UnknownField;
    }

    let fields = collect_all_django_fields(db, env.program(db), model_class);
    let field = if allow_primary_key && field_name == "pk" {
        fields.iter().find(|field| field.primary_key)
    } else {
        fields
            .iter()
            .find(|field| field.name.as_str() == field_name)
    };

    let Some(field) = field else {
        return DjangoBulkFieldLookup::UnknownField;
    };

    if matches!(field.kind, DjangoFieldKind::ManyToMany) {
        return DjangoBulkFieldLookup::NonConcrete;
    }
    if !allow_primary_key && field.primary_key {
        return DjangoBulkFieldLookup::PrimaryKey;
    }

    DjangoBulkFieldLookup::Valid
}

/// Extract the target name and call expression from a field assignment in a model
/// class body, returning `None` for statements that are not field assignments.
fn extract_field_assignment(stmt: &ast::Stmt) -> Option<(Name, &ast::ExprCall)> {
    let (name, value) = extract_assignment(stmt)?;
    let ast::Expr::Call(call) = value else {
        return None;
    };
    Some((name, call))
}

fn extract_bare_annotation(stmt: &ast::Stmt) -> Option<Name> {
    let ast::Stmt::AnnAssign(ann_assign) = stmt else {
        return None;
    };
    if ann_assign.value.is_some() {
        return None;
    }
    let ast::Expr::Name(name) = ann_assign.target.as_ref() else {
        return None;
    };
    Some(name.id.clone())
}

fn extract_assignment(stmt: &ast::Stmt) -> Option<(Name, &ast::Expr)> {
    match stmt {
        ast::Stmt::Assign(assign) => {
            let [target] = assign.targets.as_slice() else {
                return None;
            };
            let ast::Expr::Name(name) = target else {
                return None;
            };
            Some((name.id.clone(), assign.value.as_ref()))
        }
        ast::Stmt::AnnAssign(ann_assign) => {
            let ast::Expr::Name(name) = ann_assign.target.as_ref() else {
                return None;
            };
            Some((name.id.clone(), ann_assign.value.as_deref()?))
        }
        _ => None,
    }
}

fn field_call_class_name(call_expr: &ast::ExprCall) -> Option<(String, bool)> {
    let mut func = call_expr.func.as_ref();
    while let ast::Expr::Subscript(subscript) = func {
        func = subscript.value.as_ref();
    }

    Some(match func {
        ast::Expr::Name(name) => (name.id.to_string(), true),
        ast::Expr::Attribute(attr) => (attr.attr.to_string(), false),
        _ => return None,
    })
}

fn string_keyword(call_expr: &ast::ExprCall, keyword_name: &str) -> Option<Name> {
    call_expr
        .arguments
        .keywords
        .iter()
        .find_map(|keyword| {
            (keyword.arg.as_deref() == Some(keyword_name)).then_some(&keyword.value)
        })
        .and_then(|value| match value {
            ast::Expr::StringLiteral(string_lit) => Some(Name::new(string_lit.value.to_str())),
            _ => None,
        })
}

fn has_keyword(call_expr: &ast::ExprCall, keyword_name: &str) -> bool {
    call_expr
        .arguments
        .keywords
        .iter()
        .any(|keyword| keyword.arg.as_deref() == Some(keyword_name))
}

fn has_relation_target_argument(call_expr: &ast::ExprCall) -> bool {
    !call_expr.arguments.args.is_empty() || has_keyword(call_expr, "to")
}

fn relation_target_from_expr(expr: Option<&ast::Expr>) -> Option<DjangoRelationTarget> {
    let expr = expr?;
    if is_auth_user_model_reference(expr) {
        return Some(DjangoRelationTarget::AuthUser);
    }

    match expr {
        ast::Expr::Name(name) => Some(DjangoRelationTarget::Name(name.id.clone())),
        ast::Expr::StringLiteral(string_lit) => {
            let value = string_lit.value.to_str();
            if value == "self" {
                Some(DjangoRelationTarget::SelfModel)
            } else if let Some((app_label, model_name)) = value.rsplit_once('.') {
                Some(DjangoRelationTarget::Dotted {
                    app_label: app_label.to_string(),
                    model_name: model_name.to_string(),
                })
            } else {
                Some(DjangoRelationTarget::Name(Name::new(value)))
            }
        }
        _ => None,
    }
}

fn resolve_class_in_scope<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    file: File,
    class_name: &str,
) -> Option<StaticClassLiteral<'db>> {
    class_member(
        db,
        global_scope(db, program_file(db, env, file)),
        class_name,
    )
    .ignore_possibly_undefined()
    .and_then(|ty| ty.to_class_type(db))
    .and_then(|class| class.static_class_literal(db).map(|(class, _)| class))
}

fn class_literal_to_instance<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    class: StaticClassLiteral<'db>,
) -> Type<'db> {
    Type::instance(db, env, class.apply_optional_specialization(db, None))
}

fn enum_keyword_value_type<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    file: File,
    owner_class: StaticClassLiteral<'db>,
    call_expr: &ast::ExprCall,
) -> Option<Type<'db>> {
    let enum_expr = call_expr
        .arguments
        .keywords
        .iter()
        .find(|keyword| keyword.arg.as_deref() == Some("enum"))
        .map(|keyword| &keyword.value)?;

    let class = match enum_expr {
        ast::Expr::Name(name) => {
            class_member(db, owner_class.body_scope(db), name.id.as_str())
                .ignore_possibly_undefined()
                .or_else(|| {
                    class_member(
                        db,
                        global_scope(db, program_file(db, env, file)),
                        name.id.as_str(),
                    )
                    .ignore_possibly_undefined()
                })?
                .to_class_type(db)?
                .static_class_literal(db)?
                .0
        }
        ast::Expr::Attribute(attr) => {
            let ast::Expr::Name(module_name) = attr.value.as_ref() else {
                return None;
            };
            imported_symbol(
                db,
                env,
                Some(program_file(db, env, file)),
                module_name.id.as_str(),
                None,
            )
            .place
            .ignore_possibly_undefined()?;
            imported_symbol(
                db,
                env,
                Some(program_file(db, env, file)),
                attr.attr.as_str(),
                None,
            )
            .place
            .ignore_possibly_undefined()?
            .to_class_type(db)?
            .static_class_literal(db)?
            .0
        }
        _ => return None,
    };

    Some(class_literal_to_instance(db, env, class))
}

#[salsa::tracked]
impl<'db> StaticClassLiteral<'db> {
    #[salsa::tracked(returns(deref), cycle_initial=|_, _, _| Box::default(), heap_size=ruff_memory_usage::heap_size)]
    fn possible_django_field_member_names(self, db: &'db dyn Db) -> Box<[Name]> {
        let env = &ProgramEnvironment::from_file(self.program_file(db));
        let file = self.file(db);
        let module = parsed_module(db, python_file(db, env, file)).load(db);
        let class_stmt = self.node(db, &module);

        let mut names = Vec::new();
        for stmt in &class_stmt.body {
            let Some(target_name) = extract_field_assignment(stmt)
                .map(|(target_name, _)| target_name)
                .or_else(|| extract_bare_annotation(stmt))
            else {
                continue;
            };

            names.push(target_name.clone());
            names.push(Name::new(format!("{target_name}_id")));
            names.push(Name::new(format!("get_next_by_{target_name}")));
            names.push(Name::new(format!("get_previous_by_{target_name}")));
            names.push(Name::new(format!("get_{target_name}_display")));
        }

        names.into_boxed_slice()
    }

    #[salsa::tracked(
        returns(deref),
        cycle_initial=|_, _, _| Box::default(),
        cycle_fn=|_, _, _, _, _| Box::default(),
        heap_size=ruff_memory_usage::heap_size
    )]
    fn django_model_relation_fields(self, db: &'db dyn Db) -> Box<[DjangoFieldInfo<'db>]> {
        let env = &ProgramEnvironment::from_file(self.program_file(db));
        let file = self.file(db);
        let module = parsed_module(db, python_file(db, env, file)).load(db);
        let class_stmt = self.node(db, &module);

        let mut fields = Vec::new();

        for stmt in &class_stmt.body {
            let Some((target_name, call_expr)) = extract_field_assignment(stmt) else {
                continue;
            };

            let Some((field_class_name, can_resolve_custom_field)) =
                field_call_class_name(call_expr)
            else {
                continue;
            };

            let Some(kind) = field_class_to_kind(&field_class_name).or_else(|| {
                (can_resolve_custom_field
                    && class_name_could_be_custom_django_field(&field_class_name)
                    && has_relation_target_argument(call_expr))
                .then(|| resolve_custom_field_kind(db, env, file, &field_class_name))
                .flatten()
            }) else {
                continue;
            };
            if !matches!(
                kind,
                DjangoFieldKind::ForeignKey
                    | DjangoFieldKind::OneToOne
                    | DjangoFieldKind::ManyToMany
            ) {
                continue;
            }

            let mut nullable = false;
            for keyword in &call_expr.arguments.keywords {
                let Some(arg_name) = keyword.arg.as_deref() else {
                    continue;
                };
                let is_true = matches!(
                    keyword.value,
                    ast::Expr::BooleanLiteral(ast::ExprBooleanLiteral { value: true, .. })
                );
                if arg_name == "null" && is_true {
                    nullable = true;
                }
            }

            let to_kwarg = call_expr
                .arguments
                .keywords
                .iter()
                .find_map(|kw| (kw.arg.as_deref() == Some("to")).then_some(&kw.value));
            let target_expr = to_kwarg.or_else(|| call_expr.arguments.args.first());
            let related_target = relation_target_from_expr(target_expr);
            let related_model_is_auth_user = target_expr.is_some_and(is_auth_user_model_reference);

            fields.push(DjangoFieldInfo {
                name: target_name,
                file,
                class_name: field_class_name,
                kind,
                nullable,
                primary_key: false,
                has_choices: false,
                value_type_override: None,
                related_model: None,
                related_model_is_auth_user,
                related_target,
                related_name: string_keyword(call_expr, "related_name"),
                related_query_name: string_keyword(call_expr, "related_query_name"),
                to_field: string_keyword(call_expr, "to_field"),
            });
        }

        fields.into_boxed_slice()
    }

    /// Return the Django field declarations in this class's own body, excluding
    /// inherited fields.
    ///
    /// Use [`collect_all_django_fields`] to include inherited fields.
    #[salsa::tracked(returns(deref), cycle_initial=|_, _, _| Box::default(), heap_size=ruff_memory_usage::heap_size)]
    pub(super) fn django_model_fields(self, db: &'db dyn Db) -> Box<[DjangoFieldInfo<'db>]> {
        let env = &ProgramEnvironment::from_file(self.program_file(db));
        let file = self.file(db);
        let module = parsed_module(db, python_file(db, env, file)).load(db);
        let class_stmt = self.node(db, &module);

        let mut fields = Vec::new();

        for stmt in &class_stmt.body {
            if let Some(target_name) = extract_bare_annotation(stmt) {
                let value_type_override =
                    class_member(db, self.body_scope(db), target_name.as_str())
                        .ignore_possibly_undefined();

                fields.push(DjangoFieldInfo {
                    name: target_name,
                    file,
                    class_name: "AnnotatedField".to_string(),
                    kind: DjangoFieldKind::Json,
                    nullable: false,
                    primary_key: false,
                    has_choices: false,
                    value_type_override,
                    related_model: None,
                    related_model_is_auth_user: false,
                    related_target: None,
                    related_name: None,
                    related_query_name: None,
                    to_field: None,
                });
                continue;
            }

            let Some((target_name, call_expr)) = extract_field_assignment(stmt) else {
                continue;
            };

            // We can only match the trailing identifier (e.g. `CharField` from
            // `models.CharField(...)`) because full attribute resolution is not
            // available inside a `#[salsa::tracked]` method.
            let Some((field_class_name, can_resolve_custom_field)) =
                field_call_class_name(call_expr)
            else {
                continue;
            };

            let Some(kind) = field_class_to_kind(&field_class_name).or_else(|| {
                (can_resolve_custom_field
                    && class_name_could_be_custom_django_field(&field_class_name))
                .then(|| resolve_custom_field_kind(db, env, file, &field_class_name))
                .flatten()
            }) else {
                continue;
            };

            let mut nullable = false;
            let mut primary_key = false;
            let has_choices = has_keyword(call_expr, "choices");
            let related_name = string_keyword(call_expr, "related_name");
            let related_query_name = string_keyword(call_expr, "related_query_name");
            let to_field = string_keyword(call_expr, "to_field");
            for keyword in &call_expr.arguments.keywords {
                let Some(arg_name) = keyword.arg.as_deref() else {
                    continue;
                };
                let is_true = matches!(
                    keyword.value,
                    ast::Expr::BooleanLiteral(ast::ExprBooleanLiteral { value: true, .. })
                );
                match arg_name {
                    "null" if is_true => nullable = true,
                    "primary_key" if is_true => primary_key = true,
                    _ => {}
                }
            }

            // `NullBooleanField` is intrinsically nullable regardless of whether
            // `null=True` was explicitly passed. Deprecated since Django 3.1.
            if field_class_name == "NullBooleanField" {
                nullable = true;
            }

            let is_relation = matches!(
                kind,
                DjangoFieldKind::ForeignKey
                    | DjangoFieldKind::OneToOne
                    | DjangoFieldKind::ManyToMany
            );
            let to_kwarg = call_expr
                .arguments
                .keywords
                .iter()
                .find_map(|kw| (kw.arg.as_deref() == Some("to")).then_some(&kw.value));
            let target_expr = to_kwarg.or_else(|| call_expr.arguments.args.first());
            let related_target = is_relation
                .then(|| relation_target_from_expr(target_expr))
                .flatten();
            let related_model_is_auth_user =
                is_relation && target_expr.is_some_and(is_auth_user_model_reference);
            let related_model =
                if is_relation && !matches!(target_expr, Some(ast::Expr::StringLiteral(_))) {
                    Some(resolve_related_model(db, env, file, self, call_expr))
                } else {
                    None
                };

            fields.push(DjangoFieldInfo {
                name: target_name,
                file,
                class_name: field_class_name,
                kind,
                nullable,
                primary_key,
                has_choices,
                value_type_override: enum_keyword_value_type(db, env, file, self, call_expr),
                related_model,
                related_model_is_auth_user,
                related_target,
                related_name,
                related_query_name,
                to_field,
            });
        }

        fields.into_boxed_slice()
    }

    /// Return the reverse Django relation named `name` from models in the same
    /// Django `models` module or `models/` package.
    fn django_reverse_instance_member(self, db: &'db dyn Db, name: &Name) -> Option<Type<'db>> {
        let env = &ProgramEnvironment::from_file(self.program_file(db));
        if django_model_is_abstract(db, env.program(db), self) {
            return None;
        }

        if let Some(models_module) = django_models_module_for_file(db, env, self.file(db))
            && django_possible_reverse_names_in_models_module(db, env.program(db), models_module)
                .iter()
                .any(|possible_name| possible_name == name)
            && django_models_module_may_have_type_checking_cycle(db, models_module)
        {
            return Some(Type::unknown());
        }
        if let Some(top_level_package) = django_top_level_package_for_file(db, env, self.file(db))
            && django_possible_reverse_name_in_project_search_path(
                db,
                env.program(db),
                top_level_package,
                name.clone(),
            )
            && django_project_search_path_may_have_type_checking_cycle(
                db,
                env.program(db),
                top_level_package,
            )
        {
            return Some(Type::unknown());
        }

        let top_level_package = django_top_level_package_for_file(db, env, self.file(db));
        if let Some(models_module) = django_models_module_for_file(db, env, self.file(db)) {
            if django_possible_reverse_names_in_models_module(db, env.program(db), models_module)
                .iter()
                .any(|possible_name| possible_name == name)
            {
                for reverse_member in
                    &django_reverse_members_named_in_models_module(db, env, models_module, name)
                {
                    if reverse_member.target_model != self || reverse_member.name != *name {
                        continue;
                    }

                    return django_reverse_member_instance_type(db, env, reverse_member);
                }
            }
        }

        if let Some(top_level_package) = top_level_package {
            if django_possible_reverse_name_in_top_level_package(
                db,
                env.program(db),
                top_level_package,
                name.clone(),
            ) {
                for reverse_member in django_reverse_members_named_in_top_level_package(
                    db,
                    env.program(db),
                    top_level_package,
                    name.clone(),
                ) {
                    if reverse_member.target_model != self || reverse_member.name != *name {
                        continue;
                    }

                    return django_reverse_member_instance_type(db, env, reverse_member);
                }
            }
        }

        let imported_modules = if top_level_package
            .is_some_and(|top_level_package| module_is_project_code(db, top_level_package))
        {
            third_party_django_model_modules_imported_by_file(db, env.program(db), self.file(db))
        } else {
            django_model_modules_imported_by_file(db, env.program(db), self.file(db))
        };
        for module in imported_modules {
            if !possible_reverse_name_in_module(db, env, *module, name)
                && module_name_last_component(db, *module) != Some("models")
            {
                continue;
            }

            if module_name_last_component(db, *module) == Some("models")
                && !django_possible_reverse_names_in_models_module(db, env.program(db), *module)
                    .iter()
                    .any(|possible_name| possible_name == name)
            {
                continue;
            }

            let mut modules = Vec::new();
            push_django_model_module(db, env, *module, &mut modules);

            for module in modules {
                if !possible_reverse_name_in_module(db, env, module, name)
                    && module_name_last_component(db, module) != Some("models")
                {
                    continue;
                }
                if module_name_last_component(db, module) == Some("models")
                    && !django_possible_reverse_names_in_models_module(db, env.program(db), module)
                        .iter()
                        .any(|possible_name| possible_name == name)
                {
                    continue;
                }

                if module.file(db).is_none() {
                    continue;
                }

                for source_model in django_model_classes_in_module(db, env.program(db), module)
                    .iter()
                    .copied()
                {
                    let source_instance = Type::instance(
                        db,
                        env,
                        source_model.apply_optional_specialization(db, None),
                    );
                    for field in
                        collect_all_django_relation_fields(db, env.program(db), source_model)
                    {
                        if !matches!(
                            field.kind,
                            DjangoFieldKind::ForeignKey
                                | DjangoFieldKind::OneToOne
                                | DjangoFieldKind::ManyToMany
                        ) {
                            continue;
                        }
                        if !django_relation_targets_model(db, env, source_model, field, self) {
                            continue;
                        }
                        if reverse_related_name(db, env, source_model, field) != Some(name.clone())
                        {
                            continue;
                        }

                        return Some(match field.kind {
                            DjangoFieldKind::OneToOne => source_instance,
                            DjangoFieldKind::ForeignKey | DjangoFieldKind::ManyToMany => {
                                synthesize_reverse_related_manager_instance(db, env, source_model)
                            }
                            _ => continue,
                        });
                    }
                }
            }
        }

        let file = self.file(db);
        if let Some(module) = file_to_module(db, resolver_file(db, env, file))
            && possible_reverse_name_in_module(db, env, module, name)
        {
            for source_model in django_model_classes_in_module(db, env.program(db), module)
                .iter()
                .copied()
            {
                if source_model == self {
                    continue;
                }

                let source_instance = Type::instance(
                    db,
                    env,
                    source_model.apply_optional_specialization(db, None),
                );
                for field in collect_all_django_relation_fields(db, env.program(db), source_model) {
                    if !matches!(
                        field.kind,
                        DjangoFieldKind::ForeignKey
                            | DjangoFieldKind::OneToOne
                            | DjangoFieldKind::ManyToMany
                    ) {
                        continue;
                    }
                    if !django_relation_targets_model(db, env, source_model, field, self) {
                        continue;
                    }
                    if reverse_related_name(db, env, source_model, field) != Some(name.clone()) {
                        continue;
                    }

                    return Some(match field.kind {
                        DjangoFieldKind::OneToOne => source_instance,
                        DjangoFieldKind::ForeignKey | DjangoFieldKind::ManyToMany => {
                            synthesize_reverse_related_manager_instance(db, env, source_model)
                        }
                        _ => continue,
                    });
                }
            }
        }

        if let Some(top_level_package) = top_level_package
            && module_is_project_code(db, top_level_package)
            && django_possible_reverse_name_in_project_search_path(
                db,
                env.program(db),
                top_level_package,
                name.clone(),
            )
        {
            for reverse_member in django_reverse_members_named_in_project_search_path(
                db,
                env.program(db),
                top_level_package,
                name.clone(),
            ) {
                if reverse_member.target_model != self || reverse_member.name != *name {
                    continue;
                }

                return django_reverse_member_instance_type(db, env, reverse_member);
            }
        }

        None
    }
}

/// Return `true` if redeclaring `name` on the Django model `class` is idiomatic Django and must not
/// be reported as an incompatible attribute override.
///
/// Every model declares its own inner `Meta` options class, and a model may redeclare a field
/// inherited from an abstract base model with a different field type.
pub(crate) fn is_django_model_attribute_override_exempt<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    class: StaticClassLiteral<'db>,
    name: &str,
) -> bool {
    class.is_django_model(db)
        && (name == "Meta"
            || collect_all_django_fields(db, env.program(db), class)
                .iter()
                .any(|field| field.name == name))
}

/// Names of instance members that ty synthesizes for a Django model but that have no explicit
/// declaration in the class body. Member *enumeration* (e.g. for completions) only walks declared
/// members, so these synthesized names must be listed explicitly here; the caller resolves their
/// types through the normal member-lookup path (so this only needs to produce candidate names).
pub(crate) fn django_synthesized_instance_member_names<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    class: StaticClassLiteral<'db>,
) -> Vec<Name> {
    if class.is_known(db, KnownClass::DjangoModel) || !class.is_django_model(db) {
        return Vec::new();
    }

    let mut names = vec![Name::new_static("pk"), Name::new_static("id")];

    let all_fields = collect_all_django_fields(db, env.program(db), class);
    for field in all_fields {
        // Relation fields expose a `<field>_id` accessor for the underlying column.
        if relation_id_type_for_model(db, env, class, field).is_some() {
            names.push(Name::new(format!("{}_id", field.name)));
        }
        // Date/datetime fields expose `get_next_by_<field>` / `get_previous_by_<field>`.
        if matches!(
            field.kind,
            DjangoFieldKind::Date | DjangoFieldKind::DateTime
        ) {
            names.push(Name::new(format!("get_next_by_{}", field.name)));
            names.push(Name::new(format!("get_previous_by_{}", field.name)));
        }
    }

    for auth_name in ["is_staff", "is_active", "is_superuser"] {
        if synthesize_django_auth_boolean_instance_member(db, env, class, auth_name).is_some() {
            names.push(Name::new_static(auth_name));
        }
    }

    names.extend(django_reverse_member_names(db, env, class));

    names
}

/// Names of reverse-relation accessors synthesized on `class` (e.g. `book_set`, or an explicit
/// `related_name`/`related_query_name`) by models elsewhere in the project that point a
/// `ForeignKey`/`OneToOneField`/`ManyToManyField` at it. Mirrors the scopes searched by
/// [`StaticClassLiteral::django_reverse_instance_member`] so enumerated names stay resolvable.
fn django_reverse_member_names<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    class: StaticClassLiteral<'db>,
) -> Vec<Name> {
    django_reverse_members_for_target(db, env, class)
        .into_iter()
        .map(|member| member.name)
        .collect()
}

/// All reverse-relation members targeting `class`, collected across every scope the reverse-relation
/// machinery searches (the model's `models` module, the top-level package, the project search path,
/// and the model's own module). Callers pick either the attribute accessor name (`member.name`, e.g.
/// `book_set`) or the query-lookup name (`member.query_name`, e.g. `book`) depending on whether they
/// are completing attribute access or filter lookups.
fn django_reverse_members_for_target<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    class: StaticClassLiteral<'db>,
) -> Vec<DjangoReverseMemberInfo<'db>> {
    if django_model_is_abstract(db, env.program(db), class) {
        return Vec::new();
    }

    let file = class.file(db);
    let mut members = Vec::new();

    if let Some(models_module) = django_models_module_for_file(db, env, file) {
        for member in django_reverse_members_in_models_module(db, env.program(db), models_module) {
            if member.target_model == class {
                members.push(member.clone());
            }
        }
    }
    if let Some(top_level_package) = django_top_level_package_for_file(db, env, file) {
        for member in
            django_reverse_members_in_top_level_package(db, env.program(db), top_level_package)
        {
            if member.target_model == class {
                members.push(member.clone());
            }
        }
        for member in
            django_reverse_members_in_project_search_path(db, env.program(db), top_level_package)
        {
            if member.target_model == class {
                members.push(member.clone());
            }
        }
    }

    // Source models declared in the model's own module (covers projects where related models live
    // in the same file rather than a dedicated `models` package).
    if let Some(module) = file_to_module(db, resolver_file(db, env, file)) {
        for source_model in django_model_classes_in_module(db, env.program(db), module)
            .iter()
            .copied()
        {
            if source_model == class {
                continue;
            }
            for field in collect_all_django_relation_fields(db, env.program(db), source_model) {
                if !matches!(
                    field.kind,
                    DjangoFieldKind::ForeignKey
                        | DjangoFieldKind::OneToOne
                        | DjangoFieldKind::ManyToMany
                ) {
                    continue;
                }
                // Gate on the accessor name so this matches the reverse *attribute* enumeration; the
                // query name (used for filter lookups) falls back to the accessor name in the rare
                // case Django would suppress only the query name.
                if django_relation_targets_model(db, env, source_model, field, class)
                    && let Some(name) = reverse_related_name(db, env, source_model, field)
                {
                    let query_name = reverse_related_query_name(db, env, source_model, field)
                        .unwrap_or_else(|| name.clone());
                    members.push(DjangoReverseMemberInfo {
                        target_model: class,
                        name,
                        query_name,
                        source_model,
                        source_file: source_model.file(db),
                        kind: field.kind,
                    });
                }
            }
        }
    }

    members
}

/// Completion candidates for the string-literal lookup argument of a Django queryset method.
///
/// `receiver_ty` is the type of the call's receiver (a manager or queryset). `method_name`
/// selects whether relation paths (`select_related`/`prefetch_related`) or field-or-relation paths
/// (`values`/`values_list`/`only`/`defer`/`order_by`/`distinct`) are offered. `typed_prefix` is the
/// string body already typed before the cursor; any leading `field__field__` segments form a
/// relation path that is walked so the trailing (partial) segment is completed against the right
/// model. Returns full lookup strings (e.g. `author__name`); the client fuzzy-filters them.
pub(crate) fn django_lookup_string_completions<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    receiver_ty: Type<'db>,
    method_name: &str,
    typed_prefix: &str,
) -> Vec<String> {
    let relations_only = match method_name {
        "select_related" | "prefetch_related" => true,
        "values" | "values_list" | "only" | "defer" | "order_by" | "distinct" => false,
        _ => return Vec::new(),
    };

    let Some(model_instance) = model_instance_from_django_queryset_like(db, env, receiver_ty)
    else {
        return Vec::new();
    };
    let Some(model_class) = static_class_from_instance(db, env, model_instance) else {
        return Vec::new();
    };

    // `order_by` accepts a leading `-` for descending order; preserve it on the suggestions.
    let (sign, body) = typed_prefix
        .strip_prefix('-')
        .map_or(("", typed_prefix), |rest| ("-", rest));

    // Everything before the final `__` is a relation path that must be walked; the trailing
    // segment is the (partial) name being completed and is left to the client's fuzzy filter.
    let (path_str, _partial) = body.rsplit_once("__").unwrap_or(("", body));
    let mut current = model_class;
    if !path_str.is_empty() {
        for segment in path_str.split("__") {
            let Some(next) = django_relation_target_by_name(db, env, current, segment) else {
                return Vec::new();
            };
            current = next;
        }
    }

    let prefix = if path_str.is_empty() {
        String::new()
    } else {
        format!("{path_str}__")
    };

    let mut names: Vec<String> = Vec::new();
    if relations_only {
        for field in collect_all_django_relation_fields(db, env.program(db), current) {
            if matches!(
                field.kind,
                DjangoFieldKind::ForeignKey
                    | DjangoFieldKind::OneToOne
                    | DjangoFieldKind::ManyToMany
            ) {
                names.push(field.name.as_str().to_string());
            }
        }
        for name in django_reverse_member_names(db, env, current) {
            names.push(name.as_str().to_string());
        }
    } else {
        for field in collect_all_django_fields(db, env.program(db), current) {
            names.push(field.name.as_str().to_string());
        }
    }

    names.sort_unstable();
    names.dedup();
    names
        .into_iter()
        .map(|name| format!("{sign}{prefix}{name}"))
        .collect()
}

/// Completion candidates for the keyword-argument lookups of Django's `filter`/`exclude`/`get`
/// (and related) queryset methods, e.g. `filter(author__name__icontains=...)`.
///
/// This is the enumerating inverse of Django lookup *validation*: any leading `field__field`
/// segments of `typed_prefix` are walked as a relation path, and the resolved leaf model's fields
/// and relations are offered — fields additionally suffixed with the lookup transforms that apply
/// to their type (`__gte`, `__icontains`, `__year`, `__isnull`, ...). Returns full lookup strings;
/// the client fuzzy-filters them against what the user has typed.
pub(crate) fn django_filter_lookup_completions<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    receiver_ty: Type<'db>,
    typed_prefix: &str,
) -> Vec<String> {
    let Some(model_instance) = model_instance_from_django_queryset_like(db, env, receiver_ty)
    else {
        return Vec::new();
    };
    let Some(model_class) = static_class_from_instance(db, env, model_instance) else {
        return Vec::new();
    };

    // Everything before the final `__` is a relation path that must be walked; the trailing
    // segment is the (partial) name being completed and is left to the client's fuzzy filter.
    let (path_str, _partial) = typed_prefix.rsplit_once("__").unwrap_or(("", typed_prefix));
    let mut current = model_class;
    if !path_str.is_empty() {
        for segment in path_str.split("__") {
            // A path segment can be a forward field/relation or a reverse relation (matched by its
            // query name, e.g. `book` for a `Book.author` ForeignKey).
            let next = django_relation_target_by_name(db, env, current, segment).or_else(|| {
                django_reverse_relation_target_by_query_name(db, env, current, segment)
            });
            let Some(next) = next else {
                return Vec::new();
            };
            current = next;
        }
    }

    let prefix = if path_str.is_empty() {
        String::new()
    } else {
        format!("{path_str}__")
    };

    let mut candidates: Vec<String> = Vec::new();
    for field in collect_all_django_fields(db, env.program(db), current) {
        let name = field.name.as_str();
        // The bare field/relation name (relations can be traversed further with `__`).
        candidates.push(format!("{prefix}{name}"));
        for suffix in django_field_lookup_suffixes(field.kind) {
            candidates.push(format!("{prefix}{name}__{suffix}"));
        }
    }

    // Reverse relations, offered under their query name (`book`, not the `book_set` accessor). These
    // behave like forward relations for lookup purposes and can be traversed further with `__`.
    for member in django_reverse_members_for_target(db, env, current) {
        let query_name = member.query_name.as_str();
        candidates.push(format!("{prefix}{query_name}"));
        for suffix in django_field_lookup_suffixes(member.kind) {
            candidates.push(format!("{prefix}{query_name}__{suffix}"));
        }
    }

    candidates.sort_unstable();
    candidates.dedup();
    candidates
}

/// The Django lookup-transform suffixes (without the leading `__`) that apply to a field of the
/// given kind. Relation fields only expose the handful that operate on the relation itself; scalar
/// fields build from a common set plus type-specific text / comparison / date-component transforms.
fn django_field_lookup_suffixes(kind: DjangoFieldKind) -> Vec<&'static str> {
    if matches!(
        kind,
        DjangoFieldKind::ForeignKey
            | DjangoFieldKind::OneToOne
            | DjangoFieldKind::ManyToMany
            | DjangoFieldKind::GenericForeignKey
    ) {
        return vec!["exact", "in", "isnull"];
    }

    let mut suffixes = vec!["exact", "in", "isnull"];

    // Text lookups.
    if matches!(kind, DjangoFieldKind::Char) {
        suffixes.extend([
            "iexact",
            "contains",
            "icontains",
            "startswith",
            "istartswith",
            "endswith",
            "iendswith",
            "regex",
            "iregex",
        ]);
    }

    // Ordered comparisons / ranges.
    if matches!(
        kind,
        DjangoFieldKind::Integer
            | DjangoFieldKind::Float
            | DjangoFieldKind::Decimal
            | DjangoFieldKind::Auto
            | DjangoFieldKind::Date
            | DjangoFieldKind::DateTime
            | DjangoFieldKind::Time
    ) {
        suffixes.extend(["gt", "gte", "lt", "lte", "range"]);
    }

    // Date / time component extraction.
    if matches!(kind, DjangoFieldKind::Date | DjangoFieldKind::DateTime) {
        suffixes.extend([
            "year", "month", "day", "week", "week_day", "iso_year", "quarter",
        ]);
    }
    if matches!(kind, DjangoFieldKind::DateTime) {
        suffixes.extend(["date", "time", "hour", "minute", "second"]);
    }
    if matches!(kind, DjangoFieldKind::Time) {
        suffixes.extend(["hour", "minute", "second"]);
    }

    suffixes
}

/// Resolves a Django model class from the type produced by accessing a relation field on an
/// instance: the related model itself (`ForeignKey`/`OneToOneField`, possibly `... | None`), or the
/// related manager/queryset of a `ManyToManyField`.
fn django_model_class_from_related_type<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    ty: Type<'db>,
) -> Option<StaticClassLiteral<'db>> {
    if let Type::Union(union) = ty {
        return union
            .elements(db)
            .iter()
            .find_map(|element| django_model_class_from_related_type(db, env, *element));
    }
    if let Some(class) =
        static_class_from_instance(db, env, ty).filter(|class| class.is_django_model(db))
    {
        return Some(class);
    }
    model_instance_from_django_queryset_like(db, env, ty)
        .and_then(|model| static_class_from_instance(db, env, model))
}

fn django_relation_target_by_name<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    model_class: StaticClassLiteral<'db>,
    name: &str,
) -> Option<StaticClassLiteral<'db>> {
    let fields = collect_all_django_relation_fields(db, env.program(db), model_class);
    let field = fields.iter().find(|field| {
        field.name.as_str() == name
            && matches!(
                field.kind,
                DjangoFieldKind::ForeignKey
                    | DjangoFieldKind::OneToOne
                    | DjangoFieldKind::ManyToMany
            )
    })?;
    if let Some(target) = target_model_for_relation_field(db, env, model_class, field) {
        return Some(target);
    }
    // Fall back to the field's accessed instance type. The type system resolves the relation
    // target via the field descriptor even when the target model isn't declared in a `models`
    // module (which is all `target_model_for_relation_field` can resolve string references from).
    django_model_class_from_related_type(
        db,
        env,
        field.instance_type_for_model(db, env, model_class),
    )
}

/// Resolve a reverse-relation lookup segment (matched by its query name, e.g. `book`) to the model
/// on the near side of the relation (the model that declares the pointing field), so reverse
/// relations can be traversed within filter lookup paths.
fn django_reverse_relation_target_by_query_name<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    model_class: StaticClassLiteral<'db>,
    query_name: &str,
) -> Option<StaticClassLiteral<'db>> {
    django_reverse_members_for_target(db, env, model_class)
        .into_iter()
        .find(|member| member.query_name.as_str() == query_name)
        .map(|member| member.source_model)
}

pub(super) fn synthesize_django_auth_boolean_instance_member<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    class: StaticClassLiteral<'db>,
    name: &str,
) -> Option<Type<'db>> {
    let expected_base = match name {
        "is_staff" | "is_active" => "AbstractUser",
        "is_superuser" => "PermissionMixin",
        _ => return None,
    };

    class
        .iter_mro(db, None)
        .filter_map(super::super::class_base::ClassBase::into_class)
        .filter_map(|base| base.static_class_literal(db).map(|(base, _)| base))
        .any(|base| base.name(db).as_str() == expected_base)
        .then(|| KnownClass::Bool.to_instance(db, env))
}

/// Return the synthesized instance-member type for a Django model field, or `None`
/// if `name` is not a recognized field or `class` is not a Django model.
pub(super) fn synthesize_django_instance_member<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    class: StaticClassLiteral<'db>,
    name: &str,
) -> Option<Type<'db>> {
    if class.is_known(db, KnownClass::DjangoModel) || !class.is_django_model(db) {
        return None;
    }

    synthesize_django_instance_member_impl(db, env, class, name, true)
}

pub(super) fn synthesize_django_field_instance_member<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    class: StaticClassLiteral<'db>,
    name: &str,
) -> Option<Type<'db>> {
    if class.is_known(db, KnownClass::DjangoModel) || !class.is_django_model(db) {
        return None;
    }

    synthesize_django_instance_member_impl(db, env, class, name, false)
}

fn synthesize_django_instance_member_impl<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    class: StaticClassLiteral<'db>,
    name: &str,
    include_reverse_members: bool,
) -> Option<Type<'db>> {
    match name {
        "pk" => {
            let all_fields = collect_all_django_fields(db, env.program(db), class);
            Some(resolve_pk_type(db, env, all_fields))
        }
        "id" => {
            let all_fields = collect_all_django_fields(db, env.program(db), class);
            if let Some(field) = all_fields.iter().find(|f| f.name.as_str() == "id") {
                Some(field.instance_type_for_model(db, env, class))
            } else if all_fields.iter().any(|f| f.primary_key) {
                // Django only synthesizes an implicit `id` field when no field in the
                // hierarchy has `primary_key=True`.
                None
            } else {
                Some(KnownClass::Int.to_instance(db, env))
            }
        }
        // Regular fields only search this class's own body; inherited fields are
        // found by the caller's MRO walk via `own_instance_member` on each ancestor.
        // `pk` and `id` above must inspect the full hierarchy because determining
        // the primary key requires cross-class knowledge.
        _ => {
            let possible_field_member = class
                .possible_django_field_member_names(db)
                .iter()
                .any(|field_name| field_name.as_str() == name);
            if !possible_field_member {
                if django_model_reserved_non_field_instance_name(name) {
                    return None;
                }

                let all_fields = collect_all_django_fields(db, env.program(db), class);
                if let Some(field) = all_fields.iter().find(|field| field.name.as_str() == name) {
                    return Some(field.instance_type_for_model(db, env, class));
                }
                if let Some(id_type) = name.strip_suffix("_id").and_then(|field_name| {
                    all_fields
                        .iter()
                        .find(|field| field.name.as_str() == field_name)
                        .and_then(|field| relation_id_type_for_model(db, env, class, field))
                }) {
                    return Some(id_type);
                }

                return synthesize_django_auth_boolean_instance_member(db, env, class, name)
                    .or_else(|| mptt_model_instance_member(db, env, class, name))
                    .or_else(|| {
                        include_reverse_members
                            .then(|| class.django_reverse_instance_member(db, &Name::new(name)))
                            .flatten()
                    });
            }

            let fields = class.django_model_fields(db);
            fields
                .iter()
                .find(|f| f.name.as_str() == name)
                .map(|f| f.instance_type_for_model(db, env, class))
                .or_else(|| synthesize_django_auth_boolean_instance_member(db, env, class, name))
                .or_else(|| mptt_model_instance_member(db, env, class, name))
                .or_else(|| {
                    name.strip_prefix("get_next_by_")
                        .or_else(|| name.strip_prefix("get_previous_by_"))
                        .and_then(|field_name| {
                            fields
                                .iter()
                                .any(|field| {
                                    field.name.as_str() == field_name
                                        && matches!(
                                            field.kind,
                                            DjangoFieldKind::Date | DjangoFieldKind::DateTime
                                        )
                                })
                                .then(|| {
                                    Type::single_callable(
                                        db,
                                        Signature::new(
                                            Parameters::empty(),
                                            Type::instance(
                                                db,
                                                env,
                                                class.apply_optional_specialization(db, None),
                                            ),
                                        ),
                                    )
                                })
                        })
                })
                .or_else(|| {
                    name.strip_prefix("get_")
                        .and_then(|name| name.strip_suffix("_display"))
                        .and_then(|field_name| {
                            fields
                                .iter()
                                .any(|field| field.name.as_str() == field_name && field.has_choices)
                                .then(|| {
                                    Type::single_callable(
                                        db,
                                        Signature::new(
                                            Parameters::empty(),
                                            KnownClass::Str.to_instance(db, env),
                                        ),
                                    )
                                })
                        })
                })
                .or_else(|| {
                    name.strip_suffix("_id").and_then(|field_name| {
                        fields
                            .iter()
                            .find(|f| f.name.as_str() == field_name)
                            .and_then(|f| relation_id_type_for_model(db, env, class, f))
                    })
                })
                .or_else(|| {
                    include_reverse_members
                        .then(|| class.django_reverse_instance_member(db, &Name::new(name)))
                        .flatten()
                })
        }
    }
}

fn django_model_reserved_non_field_instance_name(name: &str) -> bool {
    matches!(
        name,
        "Meta"
            | "objects"
            | "_base_manager"
            | "_default_manager"
            | "save"
            | "asave"
            | "delete"
            | "adelete"
            | "refresh_from_db"
            | "arefresh_from_db"
            | "clean"
            | "clean_fields"
            | "full_clean"
            | "validate_constraints"
            | "validate_unique"
            | "serializable_value"
            | "get_deferred_fields"
            | "get_absolute_url"
    )
}

/// Return the synthesized class-member type for Django model attributes that Django
/// creates when no explicit class-body declaration exists.
pub(super) fn synthesize_django_class_member<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    class: StaticClassLiteral<'db>,
    name: &str,
) -> Option<Type<'db>> {
    if !matches!(
        name,
        "objects"
            | "_default_manager"
            | "_base_manager"
            | "_meta"
            | "DoesNotExist"
            | "NotUpdated"
            | "MultipleObjectsReturned"
            | "__init__"
    ) || class.is_known(db, KnownClass::DjangoModel)
        || !class.is_django_model(db)
    {
        return None;
    }

    if name == "__init__" {
        return Some(Type::single_callable(
            db,
            Signature::new(Parameters::gradual_form(), Type::none(db, env)),
        ));
    }

    if matches!(
        name,
        "DoesNotExist" | "NotUpdated" | "MultipleObjectsReturned"
    ) {
        return Some(KnownClass::Exception.to_subclass_of(db, env));
    }

    let file = class.file(db);
    if name == "_meta" {
        return resolve_django_symbol(db, env, file, "django.db.models.options", "Options")
            .and_then(|ty| ty.to_instance_approximation(db, env));
    }

    if name == "_default_manager"
        && let Some(manager_name) = meta_string_option(db, env, class, "default_manager_name")
        && let Some(manager) = named_manager(db, env, class, manager_name.as_str())
    {
        return Some(manager);
    }
    if name == "_base_manager"
        && let Some(manager_name) = meta_string_option(db, env, class, "base_manager_name")
        && let Some(manager) = named_manager(db, env, class, manager_name.as_str())
    {
        return Some(manager);
    }
    if name == "_default_manager"
        && let Some(manager) = first_declared_manager(db, env.program(db), class)
    {
        return Some(manager);
    }

    let model_instance = Type::instance(db, env, class.apply_optional_specialization(db, None));
    Some(synthesize_manager_instance(db, env, file, model_instance))
}
