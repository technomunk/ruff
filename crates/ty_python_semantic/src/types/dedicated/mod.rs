#[expect(
    dead_code,
    reason = "Django models are handled by `class::django_model`, which supersedes this module"
)]
pub(super) mod django;
pub(super) mod pydantic;
pub(super) mod pytest;
