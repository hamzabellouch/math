import OAI.Analysis.CircleDomains.Selection.FlattenedHeightError

namespace OAI

/-! The elementary two-coordinate product estimate for a compact cutoff. -/
open Set Function MeasureTheory
noncomputable section
namespace CircleDomainRigidity

 theorem plane_norm_sq (v : EuclideanPlane) : ‖v‖^2 = v 0^2+v 1^2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

 theorem cutoff_gradient_square_bound {η u a b c d C₀ C₁ e : ℝ}
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (he : 0 ≤ e)
    (hη : |η| ≤ C₀) (hu : |u| ≤ e) (hc : |c| ≤ C₁) (hd : |d| ≤ C₁) :
    (η*a+c*u)^2+(η*b+d*u)^2 ≤ 2*C₀^2*(a^2+b^2)+4*C₁^2*e^2 := by
  have hηsq : η^2 ≤ C₀^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg η) hC₀).mpr hη
  have ha := mul_le_mul_of_nonneg_right hηsq (sq_nonneg a)
  have hb := mul_le_mul_of_nonneg_right hηsq (sq_nonneg b)
  have hcu : |c*u| ≤ C₁*e := by
    rw [abs_mul]
    exact mul_le_mul hc hu (abs_nonneg u) hC₁
  have hdu : |d*u| ≤ C₁*e := by
    rw [abs_mul]
    exact mul_le_mul hd hu (abs_nonneg u) hC₁
  have hcs : (c*u)^2 ≤ (C₁*e)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (c*u)) (mul_nonneg hC₁ he)).mpr hcu
  have hds : (d*u)^2 ≤ (C₁*e)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (d*u)) (mul_nonneg hC₁ he)).mpr hdu
  nlinarith [sq_nonneg (η*a-c*u), sq_nonneg (η*b-d*u)]

end CircleDomainRigidity

end

end OAI
