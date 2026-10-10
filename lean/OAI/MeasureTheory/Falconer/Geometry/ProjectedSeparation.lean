import OAI.MeasureTheory.Falconer.Angular.CapTransport

namespace OAI

/-! # Separated projected supports give the directional lower bound for cap lifting -/
namespace Falconer
open NormedSpace
variable {d m : ℕ}

theorem projected_direction_lower_of_dist (P : Space d →L[ℝ] Space m)
    (x y : Space d) {a b : ℝ} (ha : 0 < a)
    (hprojected : a ≤ dist (P x) (P y)) (hsource : dist x y ≤ b) :
    a/b ≤ ‖P (radialDirection x y)‖ := by
  have hne : x ≠ y := by
    intro h
    rw [h,dist_self] at hprojected
    exact (not_le_of_gt ha) hprojected
  have hd : 0 < dist x y := dist_pos.mpr hne
  have hid : ‖P (radialDirection x y)‖ = dist (P x) (P y) / dist x y := by
    rw [radialDirection,map_smul,norm_smul,
      Real.norm_eq_abs,abs_inv,abs_norm]
    rw [map_sub,← dist_eq_norm,← dist_eq_norm,dist_comm y x,dist_comm (P y) (P x)]
    rw [div_eq_mul_inv,mul_comm]
  rw [hid]
  calc
    a/b ≤ a/dist x y := div_le_div_of_nonneg_left ha.le hd hsource
    _ ≤ dist (P x) (P y) / dist x y := (div_le_div_iff_of_pos_right hd).mpr hprojected

end Falconer

end OAI
