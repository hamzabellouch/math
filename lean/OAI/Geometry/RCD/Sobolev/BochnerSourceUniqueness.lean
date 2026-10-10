import OAI.Geometry.RCD.Sobolev.BochnerGramSource
import OAI.Geometry.RCD.Sobolev.MeasureLaplacianUniqueness
import OAI.Geometry.RCD.Metric.SignedWeightedRadon
import OAI.Geometry.RCD.Metric.SignedRadonLocal

namespace OAI

/-! # Local uniqueness of the full Bochner measure and its density -/

open Set Filter MeasureTheory
open scoped NNReal BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SecondCountableTopology X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
  (hQ : QuadraticCheegerEnergy μ)

theorem bochnerGramSource_unique_restrict {Ω S : Set X} (hΩ : MeasurableSet Ω)
    (hS : MeasurableSet S) (K : ℝ) (f g df dg F G : SobolevSpace μ hQ)
    (ν τ : SignedMeasure X)
    (hF : IsMeasureLaplacianOn μ hQ Ω F (bochnerGramSource μ hQ K f g df dg ν))
    (hG : IsMeasureLaplacianOn μ hQ Ω G (bochnerGramSource μ hQ K f g df dg τ))
    (hFG : SobolevSpace.toLp μ hQ F =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ G)
    (χ : X →ᵇ ℝ) {L : ℝ≥0} (hχ : LipschitzWith L χ)
    (hχc : HasCompactSupport (χ : X → ℝ)) (hχΩ : tsupport χ ⊆ Ω)
    (hχ0 : ∀ x, 0≤χ x) (hχ1 : ∀ x ∈ S, χ x=1) :
    ν.restrict S=τ.restrict S := by
  have he := hF.unique_restrict μ hQ hΩ hS hG hFG χ hχ hχc hχΩ hχ0 hχ1
  simp only [bochnerGramSource,VectorMeasure.restrict_add,VectorMeasure.restrict_smul] at he
  have he' := add_right_cancel he
  ext T hT
  have h := congrArg (fun s : SignedMeasure X => s T) he'
  simp only [smul_apply,smul_eq_mul] at h
  linarith only [h]

/-- Local uniqueness of the full source also identifies the density used
in a pointwise Hessian estimate, independently of the auxiliary family. -/
theorem bochnerDensity_unique [SigmaFinite μ] {Ω S : Set X} (hΩ : MeasurableSet Ω)
    (hS : MeasurableSet S) (K : ℝ) (f g df dg F G : SobolevSpace μ hQ)
    (ν τ : Measure X) [IsFiniteMeasure ν] [IsFiniteMeasure τ]
    (hF : IsMeasureLaplacianOn μ hQ Ω F (bochnerGramSource μ hQ K f g df dg ν.toSignedMeasure))
    (hG : IsMeasureLaplacianOn μ hQ Ω G (bochnerGramSource μ hQ K f g df dg τ.toSignedMeasure))
    (hFG : SobolevSpace.toLp μ hQ F =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ G)
    (χ : X →ᵇ ℝ) {L : ℝ≥0} (hχ : LipschitzWith L χ)
    (hχc : HasCompactSupport (χ : X → ℝ)) (hχΩ : tsupport χ ⊆ Ω)
    (hχ0 : ∀ x, 0≤χ x) (hχ1 : ∀ x ∈ S, χ x=1) :
    (fun x => (ν.rnDeriv μ x).toReal) =ᵐ[μ.restrict S] fun x => (τ.rnDeriv μ x).toReal := by
  have he := bochnerGramSource_unique_restrict μ hQ hΩ hS K f g df dg F G
    ν.toSignedMeasure τ.toSignedMeasure hF hG hFG χ hχ hχc hχΩ hχ0 hχ1
  have hr := signed_rnDeriv_eq_on_of_restrict_eq μ hS he
  filter_upwards [hr,ae_restrict_of_ae (signed_rnDeriv_toSignedMeasure μ ν),
    ae_restrict_of_ae (signed_rnDeriv_toSignedMeasure μ τ)] with x hx hn ht
  exact hn.symm.trans (hx.trans ht)

end RegularPointCoordinates

end

end OAI
