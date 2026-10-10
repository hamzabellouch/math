import OAI.Probability.ContinuumTransition.UpperLimit

namespace OAI

universe u_1

section
open scoped BigOperators
open Set
namespace ContinuumTemperature

lemma closedBall_subset_cube {L r : ℝ} {c : Space} (hc : c ∈ cube L) :
    Metric.closedBall c r ⊆ cube (L+2*r) := by
  intro x hx k
  rw [Metric.mem_closedBall,dist_eq_norm] at hx
  have hd : |x k-c k| ≤ r := by
    exact (show |x k-c k| ≤ ‖x-c‖ from PiLp.norm_apply_le (x-c) k).trans hx
  have hh := abs_le.mp hd
  have hk : -L/2 ≤ c k ∧ c k ≤ L/2 := hc k
  constructor <;> dsimp only [Set.mem_Icc] <;> linarith

lemma closedBall_cross_sep {η r : ℝ} (_hη : 0 ≤ η) (hr : 2*r ≤ η)
    {a b : Space} (hab : 1+η ≤ ‖a-b‖)
    {x y : Space} (hx : x ∈ Metric.closedBall a r) (hy : y ∈ Metric.closedBall b r) :
    1 ≤ ‖x-y‖ := by
  rw [Metric.mem_closedBall,dist_eq_norm] at hx hy
  have h1 := norm_sub_le_norm_sub_add_norm_sub a x y
  have h2 := norm_sub_le_norm_sub_add_norm_sub a y b
  rw [norm_sub_rev a x] at h1
  linarith

lemma packingBalls_disjoint {ι : Type u_1} {η r : ℝ} (hη : 0 ≤ η) (hr : 2*r ≤ η)
    {c : ι → Space} (hsep : ∀ i j, i ≠ j → 1+η ≤ ‖c i-c j‖) {i j : ι} (hij : i ≠ j) :
    Disjoint (Metric.closedBall (c i) r) (Metric.closedBall (c j) r) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hh := closedBall_cross_sep hη hr (hsep i j hij) hx hy
  simp only [sub_self,norm_zero] at hh
  linarith

end ContinuumTemperature
end

end OAI
