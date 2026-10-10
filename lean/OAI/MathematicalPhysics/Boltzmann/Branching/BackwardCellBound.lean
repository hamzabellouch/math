import OAI.MathematicalPhysics.Boltzmann.Approximation.CapNonlinearHotLimit

namespace OAI

/-! # Every bounded endpoint path lies in the dilated fundamental box eventually -/

noncomputable section

open Set Filter
open scoped Topology

namespace BoltzmannNonuniqueness.PositiveIteration

theorem backward_path_in_cell {r R a t : ℝ} (hr : 0 ≤ r)
    (hrR : r*(2*R) ≤ 1) (ha : 0 ≤ a) (ht : t ≤ 1)
    {x v : Velocity} (hx : ‖x‖ ≤ R) (hv : ‖v‖ ≤ R) :
    ∀ s ∈ Ioc a t, ∀ k, |(r • (x-(t-s) • v)) k| ≤ 1 := by
  intro s hs k
  have hst : 0 ≤ t-s := sub_nonneg.mpr hs.2
  have hs0 : 0 ≤ s := ha.trans hs.1.le
  have hst1 : t-s ≤ 1 := (sub_le_self t hs0).trans ht
  have hp : ‖x-(t-s) • v‖ ≤ 2*R := by
    calc
      _ ≤ ‖x‖+‖(t-s) • v‖ := norm_sub_le _ _
      _ = ‖x‖+(t-s)*‖v‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hst]
      _ ≤ R+1*R := add_le_add hx (mul_le_mul hst1 hv (norm_nonneg _) (by norm_num))
      _ = _ := by ring
  have hk := PiLp.norm_apply_le (r • (x-(t-s) • v)) k
  rw [Real.norm_eq_abs] at hk
  apply hk.trans
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
  exact (mul_le_mul_of_nonneg_left hp hr).trans hrR

end BoltzmannNonuniqueness.PositiveIteration

end

end OAI
