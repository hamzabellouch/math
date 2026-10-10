import OAI.MeasureTheory.Falconer.Radial.RadialAngleCaps
import OAI.MeasureTheory.Falconer.Radial.RadialFreezing

namespace OAI

/-! # Reverse radial caps bound collisions of original source directions -/

namespace Falconer
open NormedSpace
variable {n : ℕ}

theorem unit_perpendicular_norm_symm {u v : Space n} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖perpendicularPart u v‖ = ‖perpendicularPart v u‖ := by
  have h₁ := norm_perpendicularPart_sq hu v
  have h₂ := norm_perpendicularPart_sq hv u
  rw [hu] at h₂
  rw [hv] at h₁
  rw [real_inner_comm u v] at h₂
  nlinarith [norm_nonneg (perpendicularPart u v),norm_nonneg (perpendicularPart v u)]

theorem perpendicularPart_neg_left (u v : Space n) :
    perpendicularPart (-u) v = perpendicularPart u v := by
  simp [perpendicularPart,neg_smul]

theorem reverse_radial_angle_identity (x z y : Space n) (hz : z ≠ x) (hy : y ≠ z) :
    ‖y-z‖*displacementAngle z y x =
      ‖perpendicularPart (normalize (z-x)) (y-z)‖ := by
  have hx : x-z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have hy0 : y-z ≠ 0 := sub_ne_zero.mpr hy
  have hsym := unit_perpendicular_norm_symm (norm_normalize hy0) (norm_normalize hx)
  have hneg : normalize (x-z) = -normalize (z-x) := by
    simp only [NormedSpace.normalize,norm_sub_rev x z]
    rw [show x-z = -(z-x) by abel,smul_neg]
  have he : perpendicularPart (normalize (z-x)) (y-z) =
      ‖y-z‖ • perpendicularPart (normalize (z-x)) (normalize (y-z)) := by
    rw [← perpendicularPart_smul,norm_smul_normalize]
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  congr 1
  change ‖perpendicularPart (normalize (y-z)) (normalize (x-z))‖ = _
  rw [hsym,hneg,perpendicularPart_neg_left]

theorem reverse_radial_collision_angle (x z y : Space n) (hz : z ≠ x) (hy : y ≠ z)
    {D δ : ℝ} (hD : ‖y-x‖ ≤ D)
    (hclose : dist (normalize (y-x)) (normalize (z-x)) ≤ δ) :
    displacementAngle z y x ≤ D*δ/‖y-z‖ := by
  have hu : ‖normalize (z-x)‖ = 1 := norm_normalize (sub_ne_zero.mpr hz)
  have hperp : ‖perpendicularPart (normalize (z-x)) (normalize (y-x))‖ ≤ δ := by
    have hh := norm_perpendicularPart_le hu (normalize (y-x)-normalize (z-x))
    rw [perpendicularPart_sub] at hh
    have he : perpendicularPart (normalize (z-x)) (normalize (z-x)) = 0 := by
      simp [perpendicularPart,hu]
    rw [he,sub_zero] at hh
    exact hh.trans hclose
  have hraw : ‖perpendicularPart (normalize (z-x)) (y-z)‖ ≤ D*δ := by
    have he : y-z = (y-x)-(z-x) := by abel
    rw [he,perpendicularPart_sub,perpendicular_normalize_self,sub_zero]
    have he' : perpendicularPart (normalize (z-x)) (y-x) =
        ‖y-x‖ • perpendicularPart (normalize (z-x)) (normalize (y-x)) := by
      rw [← perpendicularPart_smul,norm_smul_normalize]
    rw [he',norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
    exact mul_le_mul hD hperp (norm_nonneg _) ((norm_nonneg _).trans hD)
  apply (le_div_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hy))).mpr
  rw [mul_comm,reverse_radial_angle_identity x z y hz hy]
  exact hraw

end Falconer

end OAI
