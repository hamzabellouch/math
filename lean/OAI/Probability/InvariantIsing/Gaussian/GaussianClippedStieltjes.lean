import OAI.Probability.InvariantIsing.Gaussian.GaussianZeroUpperExcess
import OAI.Probability.InvariantIsing.Spectral.ClippedEmpiricalTransform

namespace OAI

/-! The original Gaussian transform limit survives clipping to the MP support bounds. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace InvariantIsing

theorem gaussianPattern_clipped_stieltjes {α t : ℝ} (hα : 0 < α) (ht : 0 < t)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : (N : ℕ) → Ω → EuclideanSpace ℝ (Fin N × Fin (gaussianPatternCount α N)))
    (hZ : ∀ N, HasLaw (Z N) (stdGaussian _) P) :
    TendstoInMeasure P (fun k ω => ∫ x, positiveResolventTest t (spectralClip 0 (marchenkoPasturB α) x)
      ∂(empiricalSpectralLaw (Nat.succ_pos k) (gaussianPatternEigenvalues (Z (k+1) ω)) : Measure ℝ))
      atTop (fun _ => marchenkoPasturTransform t α) := by
  have hE := tendstoInMeasure_div_pos P _ (gaussianPattern_zero_upper_excess hα P Z hZ) (sq_pos_of_pos ht)
  apply tendstoInMeasure_of_dist_le P _ _ _ _ (gaussianPatternStieltjes_tendsto hα.le ht P Z hZ) hE
  intro k ω
  rw [Real.dist_eq,← gaussianGramStieltjes_empirical_integral (Nat.succ_pos k) ht]
  exact empirical_transform_clip_excess (Nat.succ_pos k) _ (sq_nonneg _) ht

end InvariantIsing

end

end OAI
