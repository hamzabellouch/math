import OAI.Probability.InvariantIsing.Gaussian.GaussianClippedWeak
import OAI.Probability.InvariantIsing.Spectral.EmpiricalClippingDistance

namespace OAI

/-! The original Gaussian Gram empirical measures converge to the literal MP law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace InvariantIsing

theorem gaussianPattern_empirical_weak {α : ℝ} (hα : 0 < α)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : (N : ℕ) → Ω → EuclideanSpace ℝ (Fin N × Fin (gaussianPatternCount α N)))
    (hZ : ∀ N, HasLaw (Z N) (stdGaussian _) P) :
    TendstoInMeasure P (fun k ω => LevyProkhorov.ofMeasure
      (empiricalSpectralLaw (Nat.succ_pos k) (gaussianPatternEigenvalues (Z (k+1) ω)))) atTop
      (fun _ => LevyProkhorov.ofMeasure (⟨marchenkoPasturMeasure α,marchenkoPastur_probability hα⟩ : ProbabilityMeasure ℝ)) := by
  apply tendstoInMeasure_of_dist_le P _ _ _ _ (gaussianPattern_clipped_weak hα P Z hZ)
    (gaussianPattern_zero_upper_excess hα P Z hZ)
  intro k ω
  exact empirical_clipping_distance (Nat.succ_pos k) _ (sq_nonneg _)

end InvariantIsing

end

end OAI
