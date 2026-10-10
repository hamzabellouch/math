import Mathlib
import OAI.Probability.SKValue.Evolution.MeanDerivativeContinuous
import OAI.Probability.SKValue.Processes.StripPaths
import OAI.Probability.SKValue.Equations.LiteralNormalizer

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

lemma IsDiffusion.finite_gaussian_fixed_strip {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) {T K L D Lu La : ℝ}
    (hT : 0<T) (hT1 : T<1) (hg : GradientStrip T γ.coeff (gradient W γ) K L)
    (hD : 0≤D) (hLu : 0≤Lu) (hLa : 0≤La)
    (ha : ∀ t∈Icc (0 : ℝ) T, ∀ x, |curvature W γ t x|≤D)
    (huLip : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |gradient W γ s x-gradient W γ t y|≤Lu*(|s-t|+|x-y|))
    (haLip : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |curvature W γ s x-curvature W γ t y|≤La*(|s-t|+|x-y|))
    (hmom : ∀ t∈Icc (0 : ℝ) T, (∫ ω, (curvature W γ t (X t ω))^2 ∂W.μ)=1) :
    (∀ᶠ N in atTop, ∀ j<N, 0<normalizer W γ T N j) ∧
    Tendsto (shiftedCoefficientSum W γ T) atTop
      (𝓝 (∫ t in (0 : ℝ)..T, ∫ ω, curvature W γ t (X t ω) ∂W.μ)) := by
  have hh := finiteGaussian_from_diffusion W.brownian.toIsPreBrownianReal hT hT1.le hg
    hD hLu hLa ha huLip haLip
    (fun t ht ↦ (hX.measurable ⟨ht.1,ht.2.trans hT1.le⟩).aestronglyMeasurable)
    (hX.strip_paths hT.le hT1 hLu (fun t ht s hs x y ↦ huLip s hs t ht y x)) hmom
  constructor
  · simpa only [literal_normalizer] using hh.1
  · apply hh.2.congr'
    exact Eventually.of_forall (fun N ↦ (literal_shiftedCoefficientSum W γ T N).symm)

end SKValue

end

end OAI
