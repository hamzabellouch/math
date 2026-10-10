import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Distributions.Gaussian.Real

namespace OAI

namespace Yau.Probability
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section

lemma gaussian_pdf_upper_bound (mean x : ℝ) (v : ℝ≥0) :
    gaussianPDFReal mean v x ≤ (Real.sqrt (2*Real.pi*v))⁻¹ := by
  unfold gaussianPDFReal
  apply mul_le_of_le_one_right (by positivity)
  apply Real.exp_le_one_iff.mpr
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)

lemma gaussian_interval_bound (mean center radius : ℝ) (hr : 0 ≤ radius)
    (v : ℝ≥0) (hv : v ≠ 0) :
    gaussianReal mean v (Icc (center-radius) (center+radius)) ≤
      ENNReal.ofReal (2*radius/(Real.sqrt (2*Real.pi*v))) := by
  rw [gaussianReal_apply mean hv]
  calc
    _ ≤ ∫⁻ _ in Icc (center-radius) (center+radius),
        ENNReal.ofReal ((Real.sqrt (2*Real.pi*v))⁻¹) := by
      apply lintegral_mono
      intro x
      exact ENNReal.ofReal_le_ofReal (gaussian_pdf_upper_bound mean x v)
    _ = _ := by
      rw [lintegral_const,Measure.restrict_apply_univ,Real.volume_Icc]
      rw [← ENNReal.ofReal_mul' (by linarith only [hr])]
      congr 1
      ring

end
end Yau.Probability

end OAI
