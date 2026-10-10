import OAI.Geometry.RCD.Metric.LocalSignedMeasureOrder
import OAI.Geometry.RCD.Sobolev.SignedTestFunctional

namespace OAI

/-! # Local test identities determine the full signed measure -/

open Set MeasureTheory
open scoped NNReal BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SecondCountableTopology X]

/-- Equality on the local compact Lipschitz test class includes singular
parts of the measure on every interior set carrying such a cutoff. -/
theorem signedMeasure_eq_restrict_of_tests (ν τ : SignedMeasure X)
    {Ω S : Set X} (hS : MeasurableSet S)
    (χ : X →ᵇ ℝ) {L : ℝ≥0} (hχ : LipschitzWith L χ)
    (hχc : HasCompactSupport (χ : X → ℝ)) (hχΩ : tsupport χ ⊆ Ω)
    (hχ0 : ∀ x, 0≤χ x) (hχ1 : ∀ x ∈ S, χ x=1)
    (h : ∀ f : compactLipschitzTests Ω,
      signedTestIntegral (f : X →ᵇ ℝ) ν = signedTestIntegral (f : X →ᵇ ℝ) τ) :
    ν.restrict S=τ.restrict S := by
  have hforward : 0≤(ν-τ).restrict S := by
    apply signedMeasure_nonneg_restrict_of_tests (ν-τ) hS χ hχ hχc hχΩ hχ0 hχ1
    intro f _
    change 0 ≤ signedTestIntegral (f : X →ᵇ ℝ) (ν-τ)
    rw [map_sub,h f,sub_self]
  have hreverse : 0≤(τ-ν).restrict S := by
    apply signedMeasure_nonneg_restrict_of_tests (τ-ν) hS χ hχ hχc hχΩ hχ0 hχ1
    intro f _
    change 0 ≤ signedTestIntegral (f : X →ᵇ ℝ) (τ-ν)
    rw [map_sub,h f,sub_self]
  rw [VectorMeasure.restrict_sub] at hforward hreverse
  exact le_antisymm (sub_nonneg.mp hreverse) (sub_nonneg.mp hforward)

end RegularPointCoordinates

end

end OAI
