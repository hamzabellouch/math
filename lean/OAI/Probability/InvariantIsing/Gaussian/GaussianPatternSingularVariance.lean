import OAI.Probability.InvariantIsing.Gaussian.GaussianPatternEuclideanNorm
import OAI.Probability.InvariantIsing.Gaussian.GaussianPatternSingularMinimum
import OAI.Probability.InvariantIsing.Gaussian.GaussianVarianceInput

namespace OAI

/-! Dimension-free Gaussian variance for the physical rectangular operator norm. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace InvariantIsing

lemma finiteGaussian_lipschitz_variance {ι : Type*} [Fintype ι] {L : ℝ≥0}
    {f : EuclideanSpace ℝ ι → ℝ} (hf : LipschitzWith L f) :
    variance f (stdGaussian (EuclideanSpace ℝ ι)) ≤ (L : ℝ)^2 := by
  let e : EuclideanSpace ℝ (Fin (Fintype.card ι)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin ι).symm
  have hh : LipschitzWith L (f ∘ e) := by simpa only [mul_one] using hf.comp e.lipschitz
  have hv := gaussianLipschitzVariance_proved (Fintype.card ι) L (f ∘ e) hh
  have hm := stdGaussian_map e
  rw [← hm,variance_map hf.continuous.aemeasurable e.continuous.aemeasurable]
  exact hv

theorem gaussianPatternSingularMax_variance (N m : ℕ) :
    variance (gaussianPatternSingularMax (N := N) (m := m))
      (stdGaussian (EuclideanSpace ℝ (Fin N × Fin m))) ≤ 1 := by
  simpa only [NNReal.coe_one,one_pow] using
    finiteGaussian_lipschitz_variance (gaussianPatternSingularMax_lipschitz N m)

theorem gaussianPatternSingularMin_variance (N m : ℕ) (hm : 0 < m) :
    variance (gaussianPatternSingularMin (N := N) (m := m))
      (stdGaussian (EuclideanSpace ℝ (Fin N × Fin m))) ≤ 1 := by
  simpa only [NNReal.coe_one,one_pow] using
    finiteGaussian_lipschitz_variance (gaussianPatternSingularMin_lipschitz N m hm)

end InvariantIsing

end

end OAI
