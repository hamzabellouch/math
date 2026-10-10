import OAI.MeasureTheory.Falconer.Geometry.PlanarSlopeBalls

namespace OAI

/-! # Freezing radial directions in a source cell away from its pin -/

namespace Falconer
open NormedSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem normalize_distance_scaled {u v : E} {r : ℝ}
    (hu : r ≤ ‖u‖) (hv : v ≠ 0) :
    r*dist (normalize u) (normalize v) ≤ 2*dist u v := by
  have he : ‖u‖ • (normalize u-normalize v) =
      u-v+(‖v‖-‖u‖) • normalize v := by
    rw [smul_sub,norm_smul_normalize,sub_smul,norm_smul_normalize]
    abel
  have hb := norm_add_le (u-v) ((‖v‖-‖u‖) • normalize v)
  rw [← he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),
    norm_smul,Real.norm_eq_abs,norm_normalize hv,mul_one] at hb
  have hn := abs_norm_sub_norm_le v u
  rw [norm_sub_rev v u] at hn
  rw [dist_eq_norm,dist_eq_norm]
  have hh := mul_le_mul_of_nonneg_right hu (norm_nonneg (normalize u-normalize v))
  linarith

theorem perpendicular_normalize_self (v : E) : perpendicularPart (normalize v) v = 0 := by
  by_cases hv : v = 0
  · simp [hv,perpendicularPart,NormedSpace.normalize]
  · have he : v = ‖v‖ • normalize v := (norm_smul_normalize v).symm
    calc
      _ = perpendicularPart (normalize v) (‖v‖ • normalize v) := congrArg _ he
      _ = ‖v‖ • perpendicularPart (normalize v) (normalize v) := perpendicularPart_smul _ _ _
      _ = 0 := by simp [perpendicularPart,norm_normalize hv]

theorem frozen_radial_tube_error (x c z y : E) {r D W : ℝ}
    (hr : 0 < r) (hcx : r ≤ ‖c-x‖) (hzx : z ≠ x)
    (hzc : ‖z-c‖ ≤ D) (hyc : ‖y-c‖ ≤ D)
    (htube : ‖perpendicularPart (normalize (z-x)) (y-x)‖ ≤ W) :
    ‖perpendicularPart (normalize (c-x)) (y-z)‖ ≤ W+8*D^2/r := by
  have hc0 : c-x ≠ 0 := norm_pos_iff.mp (hr.trans_le hcx)
  have hz0 : z-x ≠ 0 := sub_ne_zero.mpr hzx
  have hD : 0 ≤ D := (norm_nonneg _).trans hzc
  have hd : ‖normalize (c-x)-normalize (z-x)‖ ≤ 2*D/r := by
    apply (le_div_iff₀ hr).mpr
    have hh := normalize_distance_scaled hcx hz0
    have he : dist (c-x) (z-x) = ‖z-c‖ := by
      rw [dist_eq_norm,sub_sub_sub_cancel_right,norm_sub_rev]
    rw [he,dist_eq_norm] at hh
    nlinarith
  have hyz : ‖y-z‖ ≤ 2*D := by
    have hh := norm_sub_le_norm_sub_add_norm_sub y c z
    rw [norm_sub_rev c z] at hh
    linarith
  have hshift : perpendicularPart (normalize (z-x)) (y-z) =
      perpendicularPart (normalize (z-x)) (y-x) := by
    have he : y-z = (y-x)-(z-x) := by abel
    rw [he,perpendicularPart_sub,perpendicular_normalize_self,sub_zero]
  have herr := perpendicularPart_direction_error (norm_normalize hc0) (norm_normalize hz0) (y-z)
  have hu : ‖perpendicularPart (normalize (c-x)) (y-z) -
      perpendicularPart (normalize (z-x)) (y-z)‖ ≤ 8*D^2/r := by
    apply herr.trans
    calc
      _ ≤ 2*(2*D/r)*(2*D) := by gcongr
      _ = _ := by ring
  calc
    _ = ‖(perpendicularPart (normalize (c-x)) (y-z)-
        perpendicularPart (normalize (z-x)) (y-z))+
          perpendicularPart (normalize (z-x)) (y-z)‖ := by congr 1; abel
    _ ≤ ‖perpendicularPart (normalize (c-x)) (y-z)-
        perpendicularPart (normalize (z-x)) (y-z)‖+
          ‖perpendicularPart (normalize (z-x)) (y-z)‖ := norm_add_le _ _
    _ ≤ 8*D^2/r+W := add_le_add hu (by rw [hshift]; exact htube)
    _ = _ := add_comm _ _

end Falconer

end OAI
