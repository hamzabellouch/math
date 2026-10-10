import OAI.Geometry.RCD.Metric.LocalSignedMeasureEquality
import OAI.Geometry.RCD.Sobolev.MeasureLaplacianProduct
import OAI.Geometry.RCD.Sobolev.CompactLipschitzTests
import OAI.Geometry.RCD.Sobolev.SupportedEnergyLocality

namespace OAI

/-! # Uniqueness of the full local measure Laplacian -/

open Set MeasureTheory
open scoped NNReal BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SecondCountableTopology X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
  (hQ : QuadraticCheegerEnergy μ)

/-- Local representatives have the same full Laplacian measure on every
interior set with a compact cutoff. This includes singular parts. -/
theorem IsMeasureLaplacianOn.unique_restrict {Ω S : Set X} (hΩ : MeasurableSet Ω)
    (hS : MeasurableSet S) {f g : SobolevSpace μ hQ} {ν τ : SignedMeasure X}
    (hf : IsMeasureLaplacianOn μ hQ Ω f ν) (hg : IsMeasureLaplacianOn μ hQ Ω g τ)
    (hfg : SobolevSpace.toLp μ hQ f =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ g)
    (χ : X →ᵇ ℝ) {L : ℝ≥0} (hχ : LipschitzWith L χ)
    (hχc : HasCompactSupport (χ : X → ℝ)) (hχΩ : tsupport χ ⊆ Ω)
    (hχ0 : ∀ x, 0≤χ x) (hχ1 : ∀ x ∈ S, χ x=1) :
    ν.restrict S=τ.restrict S := by
  apply signedMeasure_eq_restrict_of_tests ν τ hS χ hχ hχc hχΩ hχ0 hχ1
  intro q
  obtain ⟨C,hq,hqc,hqs⟩ := q.property
  let ψ := compactTestSobolev μ hQ Ω q
  have hψ := compactTestSobolev_coe μ hQ Ω q
  have he := energyForm_eq_of_test_support μ hQ hΩ hfg q hψ hqs
  have hν := hf ψ q hq.continuous hqc hqs hψ
  have hτ := hg ψ q hq.continuous hqc hqs hψ
  change energyForm μ hQ f ψ = -signedTestIntegral (q : X →ᵇ ℝ) ν at hν
  change energyForm μ hQ g ψ = -signedTestIntegral (q : X →ᵇ ℝ) τ at hτ
  linarith only [he,hν,hτ]

end RegularPointCoordinates

end

end OAI
