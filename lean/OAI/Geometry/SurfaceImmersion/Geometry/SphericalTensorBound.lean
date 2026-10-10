import OAI.Geometry.SurfaceImmersion.Geometry.SphericalPointFlattening

namespace OAI

/-! The spherical correction tensor is bounded using only the first two
derivatives, uniformly without choosing a normal frame. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.SphericalJets

lemma norm_sphericalSecondFormCLM_le (F : Plane → Space) (p : Plane) :
    ‖sphericalSecondFormCLM F p‖ ≤ ‖fderiv ℝ (fderiv ℝ F) p‖ +
      ‖fderiv ℝ F p‖^2 * ‖F p‖ := by
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
  intro v w
  rw [sphericalSecondFormCLM_apply,sphericalSecondForm]
  calc
    _ ≤ ‖secondForm F p v w‖ +
        ‖inner ℝ (fderiv ℝ F p v) (fderiv ℝ F p w) • F p‖ := norm_add_le _ _
    _ ≤ ‖fderiv ℝ (fderiv ℝ F) p v w‖ +
        (‖fderiv ℝ F p v‖ * ‖fderiv ℝ F p w‖) * ‖F p‖ := by
      apply add_le_add
      · exact (normalSpace F p).norm_starProjection_apply_le _
      · rw [norm_smul]
        exact mul_le_mul_of_nonneg_right (norm_inner_le_norm _ _) (norm_nonneg _)
    _ ≤ ‖fderiv ℝ (fderiv ℝ F) p‖ * ‖v‖ * ‖w‖ +
        ((‖fderiv ℝ F p‖ * ‖v‖) * (‖fderiv ℝ F p‖ * ‖w‖)) * ‖F p‖ := by
      apply add_le_add
      · exact ContinuousLinearMap.le_opNorm₂ _ _ _
      · gcongr
        · exact (fderiv ℝ F p).le_opNorm v
        · exact (fderiv ℝ F p).le_opNorm w
    _ = (‖fderiv ℝ (fderiv ℝ F) p‖ + ‖fderiv ℝ F p‖^2 * ‖F p‖) * ‖v‖ * ‖w‖ := by ring

lemma norm_sphericalSecondFormCLM_of_bounds {F : Plane → Space} {p : Plane}
    {C₁ C₂ : ℝ} (h₁ : ‖fderiv ℝ F p‖ ≤ C₁) (h₂ : ‖fderiv ℝ (fderiv ℝ F) p‖ ≤ C₂)
    (hp : ‖F p‖ = 1) : ‖sphericalSecondFormCLM F p‖ ≤ C₂+C₁^2 := by
  apply (norm_sphericalSecondFormCLM_le F p).trans
  rw [hp,mul_one]
  gcongr

end ClosedSurfaceR4.SphericalJets

end

end OAI
