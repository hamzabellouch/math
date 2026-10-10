import OAI.Probability.InvariantIsing.Gaussian.GaussianQuadraticLaw
import OAI.Probability.InvariantIsing.Gaussian.GaussianLipschitzIntegrability

namespace OAI

/-! The proved regular-potential Poincare inequality at the standard Gaussian. -/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped NNReal
namespace InvariantIsing

theorem gaussian_test_variance_le {d : ℕ} {L : ℝ≥0}
    {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (ht : LeanBlast.KLS.IsTestFunction f) (hf : LipschitzWith L f) :
    variance f (stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ (L : ℝ)^2 := by
  have hp := gaussianQuadraticPotential_poincare_test f ht
  rw [gaussianQuadratic_potentialMeasure_eq_stdGaussian] at hp
  have hv : variance f (stdGaussian (EuclideanSpace ℝ (Fin d))) =
      LeanBlast.KLS.variance (stdGaussian (EuclideanSpace ℝ (Fin d))) f := by
    rw [variance_eq_integral hf.continuous.aemeasurable]
    rfl
  rw [hv]
  apply hp.trans
  change (∫ x, ‖gradient f x‖^2 ∂stdGaussian _) ≤ _
  calc
    _ ≤ ∫ _ : EuclideanSpace ℝ (Fin d), (L : ℝ)^2 ∂stdGaussian _ := by
      apply integral_mono (ht.integrable_gradient_sq _) (integrable_const _)
      intro x
      dsimp only
      rw [LeanBlast.KLS.norm_gradient_eq_norm_fderiv]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ hf) 2
    _ = _ := by simp

end InvariantIsing

end

end OAI
