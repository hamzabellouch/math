import OAI.Probability.InvariantIsing.Gaussian.GaussianGramTransformLimit
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

namespace OAI

/-! Convergence in probability of the physical Gaussian Gram resolvents. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal
namespace InvariantIsing

theorem gaussianPatternStieltjes_tendsto {α t : ℝ} (hα : 0 ≤ α) (ht : 0 < t)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : (N : ℕ) → Ω → EuclideanSpace ℝ (Fin N × Fin (gaussianPatternCount α N)))
    (hZ : ∀ N, HasLaw (Z N) (stdGaussian _) P) :
    TendstoInMeasure P (fun k ω => gaussianGramStieltjes t (Z (k+1) ω)) atTop
      (fun _ => marchenkoPasturTransform t α) := by
  have hi (k : ℕ) : Integrable (fun ω =>
      gaussianGramStieltjes t (Z (k+1) ω)-marchenkoPasturTransform t α) P := by
    have hm : AEStronglyMeasurable
        (fun z : EuclideanSpace ℝ (Fin (k+1) × Fin (gaussianPatternCount α (k+1))) =>
          gaussianGramStieltjes t z-marchenkoPasturTransform t α) (stdGaussian _) :=
      ((continuous_gaussianGramStieltjes (N := k+1)
      (m := gaussianPatternCount α (k+1)) ht).sub continuous_const).aestronglyMeasurable
    have hh : Integrable (fun z : EuclideanSpace ℝ (Fin (k+1) × Fin (gaussianPatternCount α (k+1))) =>
        gaussianGramStieltjes t z-marchenkoPasturTransform t α) (stdGaussian _) :=
      (integrable_norm_iff hm).mp (by
        simpa only [Real.norm_eq_abs] using gaussianGramTransform_error_integrable ht α)
    exact (hZ (k+1)).integrable_comp hh
  have he (k : ℕ) : eLpNorm ((fun ω => gaussianGramStieltjes t (Z (k+1) ω))-
      (fun _ => marchenkoPasturTransform t α)) 1 P =
      ENNReal.ofReal (∫ ω, |gaussianGramStieltjes t (Z (k+1) ω)-marchenkoPasturTransform t α| ∂P) := by
    change eLpNorm (fun ω => gaussianGramStieltjes t (Z (k+1) ω)-marchenkoPasturTransform t α) 1 P = _
    rw [eLpNorm_one_eq_lintegral_enorm (hi k).aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm (hi k)]
    simp only [Real.norm_eq_abs]
  apply tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1 : ℝ≥0∞) ≠ 0)
  simpa only [he,ENNReal.ofReal_zero,Function.comp_def] using
    (ENNReal.continuous_ofReal.tendsto 0).comp (gaussianPatternStieltjes_L1 hα ht P Z hZ)

end InvariantIsing

end

end OAI
