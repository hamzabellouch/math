import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Tactic.Linarith

namespace OAI

/-! # Centering a uniformly convergent real-valued family -/

open Filter
open scoped Topology
namespace RegularPointCoordinates

theorem uniform_reverse_centered {Y : Type*} {f : ℕ → Y → ℝ} {g : Y → ℝ}
    (h : TendstoUniformly f g atTop) (a : Y) :
    TendstoUniformly (fun k x => f k a-f k x) (fun x => g a-g x) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [(Metric.tendstoUniformly_iff.mp h) (ε/2) (by linarith)] with k hk
  intro x
  have ha := hk a
  have hx := hk x
  rw [Real.dist_eq] at ha hx ⊢
  rcases abs_lt.mp ha with ⟨ha₁,ha₂⟩
  rcases abs_lt.mp hx with ⟨hx₁,hx₂⟩
  apply abs_lt.mpr
  constructor <;> linarith

end RegularPointCoordinates

end OAI
