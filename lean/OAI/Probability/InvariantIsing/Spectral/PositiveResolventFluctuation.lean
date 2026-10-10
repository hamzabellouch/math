import OAI.Probability.InvariantIsing.Spectral.PositiveResolventVariance
import OAI.Probability.InvariantIsing.Magnetic.RestrictedPressureFluctuation

namespace OAI

/-! Uniform Gaussian mean absolute fluctuations of a normalized resolvent quadratic form. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
namespace InvariantIsing

lemma positiveResolvent_normalized_mean {N : ℕ} {t : ℝ} (ht : 0 < t)
    {B : Matrix (Fin N) (Fin N) ℝ} (hB : B.PosSemidef) :
    (∫ x, (1/(N : ℝ))*gaussianQuadraticForm (positiveResolvent t B) x ∂stdGaussian _) =
      (positiveResolvent t B).trace / N := by
  rw [integral_const_mul,hermitianGaussianQuadratic_mean _ (positiveResolvent_posDef ht hB).isHermitian]
  ring

lemma positiveResolvent_normalized_fluctuation {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : 0 < t)
    {B : Matrix (Fin N) (Fin N) ℝ} (hB : B.PosSemidef) :
    (∫ x, |(1/(N : ℝ))*gaussianQuadraticForm (positiveResolvent t B) x-
      (positiveResolvent t B).trace / N| ∂stdGaussian _) ≤ Real.sqrt (2/((N : ℝ)*t^2)) := by
  have hf := (gaussianQuadraticForm_memLp (positiveResolvent t B)).const_mul (1/(N : ℝ))
  have h := integral_abs_sub_mean_le_sqrt_variance (stdGaussian _)
    (fun x => (1/(N : ℝ))*gaussianQuadraticForm (positiveResolvent t B) x) hf
  rw [positiveResolvent_normalized_mean ht hB] at h
  exact h.trans (Real.sqrt_le_sqrt (positiveResolvent_normalized_variance hN ht hB))

end InvariantIsing

end

end OAI
