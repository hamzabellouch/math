import Mathlib
import OAI.Probability.Ballisticity.Estimates.BindIntegral
import OAI.Probability.Ballisticity.Coupling.QuenchedSuccessComparison

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma successfulAverage_eq_bind {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d) (H : ℝ) :
    successfulAverage ν ℓ H = (environmentLaw ν).bind (successQuenchedKernel ℓ 0 H) := by
  apply Measure.ext
  intro A hA
  rw [successfulAverage_apply ν ℓ H A hA,Measure.bind_apply hA (Kernel.measurable _).aemeasurable]
  apply lintegral_congr
  intro ω
  exact (successQuenchedKernel_apply ℓ 0 H ω A hA).symm

lemma successfulAverage_integral {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d) (H : ℝ)
    (F : Path d → ℝ) (hF : Measurable F) (h0 : ∀ X, 0 ≤ F X)
    (hi : ∀ ω, Integrable F (successQuenchedKernel ℓ 0 H ω)) :
    (∫ X, F X ∂successfulAverage ν ℓ H) =
      ∫ ω, ∫ X, F X ∂successQuenchedKernel ℓ 0 H ω ∂environmentLaw ν := by
  rw [successfulAverage_eq_bind]
  exact integral_bind_nonneg_of_integrable _ _ (Kernel.measurable _) F hF h0 hi

lemma crossingQuenched_positive_ae {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ) :
    ∀ᵐ ω ∂environmentLaw ν, ∀ x H, crossingQuenched ℓ x H ω ≠ 0 := by
  filter_upwards [quenched_noDrop_positive_of_directionallyTransient ν hue ℓ hℓ htrans,
    quenched_noDrop_subset_cross_ae ν ℓ htrans] with ω hp hs x H
  exact ne_of_gt ((hp x).trans_le (measure_mono_ae (hs x H)))

end DirectionalTransience

end

end

end OAI
