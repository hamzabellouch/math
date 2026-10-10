import OAI.Geometry.RCD.Metric.LocalSignedMeasureOrder

namespace OAI

/-! # Restricting a positive bilinear distribution to an interior set -/

open Set MeasureTheory
open scoped NNReal BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X E : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SecondCountableTopology X] [AddCommGroup E] [Module ℝ E]

def positiveBilinearMeasure_of_local_tests
    (Q : E →ₗ[ℝ] E →ₗ[ℝ] SignedMeasure X) (hQ : ∀ v w, Q v w = Q w v)
    {Ω S : Set X} (hS : MeasurableSet S)
    (χ : X →ᵇ ℝ) {L : ℝ≥0} (hχ : LipschitzWith L χ)
    (hχc : HasCompactSupport (χ : X → ℝ)) (hχΩ : tsupport χ ⊆ Ω)
    (hχ0 : 0 ≤ χ) (hχ1 : ∀ x ∈ S, χ x = 1)
    (hpos : ∀ v (f : compactLipschitzTests Ω), 0 ≤ (f : X →ᵇ ℝ) →
      0 ≤ ∫ᵛ x, (f : X →ᵇ ℝ) x ∂<•(Q v v)) : PositiveBilinearMeasure X E where
  bilinear := Q.compr₂ (VectorMeasure.restrictₗ S)
  symmetric v w := congrArg (fun ν : SignedMeasure X => ν.restrict S) (hQ v w)
  nonneg v := signedMeasure_nonneg_restrict_of_tests (Q v v) hS χ hχ hχc hχΩ hχ0 hχ1 (hpos v)

end RegularPointCoordinates

end

end OAI
