import OAI.MeasureTheory.Falconer.Radial.RadialFreezing
import OAI.MeasureTheory.Falconer.Radial.RadialSphereLaw

namespace OAI

/-! # Unoriented closeness of a witness direction to the source-cell center -/

namespace Falconer
open NormedSpace
variable {d : ℕ}

theorem cell_center_witness_direction (w₀ : Sphere d) (x c z : Space d)
    {r D : ℝ} (hr : 0 < r) (hcx : r ≤ ‖c-x‖) (hzx : z ≠ x)
    (hzc : ‖z-c‖ ≤ D) :
    ‖normalize (c-x)+(normalizeToSphere w₀ (x-z):Space d)‖ ≤ 2*D/r := by
  rw [normalizeToSphere_coe_of_ne w₀ (sub_ne_zero.mpr hzx.symm)]
  have hn : normalize (x-z) = -normalize (z-x) := by
    rw [show x-z = -(z-x) by abel,normalize_neg]
  rw [hn,← sub_eq_add_neg]
  apply (le_div_iff₀ hr).mpr
  have hh := normalize_distance_scaled hcx (sub_ne_zero.mpr hzx)
  rw [dist_eq_norm,dist_eq_norm,sub_sub_sub_cancel_right,norm_sub_rev c z] at hh
  nlinarith

end Falconer

end OAI
