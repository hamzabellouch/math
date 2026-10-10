import OAI.Geometry.RCD.Sobolev.UniformCenteredConvergence

namespace OAI

/-! # Addition of uniformly convergent real-valued families -/

open Filter
namespace RegularPointCoordinates

theorem uniform_real_add {X : Type*} {f g : ℕ → X → ℝ} {F G : X → ℝ}
    (hf : TendstoUniformly f F atTop) (hg : TendstoUniformly g G atTop) :
    TendstoUniformly (fun k x => f k x+g k x) (fun x => F x+G x) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [(Metric.tendstoUniformly_iff.mp hf) (ε/2) (by linarith),
    (Metric.tendstoUniformly_iff.mp hg) (ε/2) (by linarith)] with k hk hj
  intro x
  have hh := hk x
  have hh' := hj x
  rw [Real.dist_eq] at hh hh' ⊢
  rcases abs_lt.mp hh with ⟨ha,hb⟩
  rcases abs_lt.mp hh' with ⟨hc,hd⟩
  apply abs_lt.mpr
  constructor <;> linarith

end RegularPointCoordinates

end OAI
