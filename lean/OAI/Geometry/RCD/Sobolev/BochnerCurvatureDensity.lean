import OAI.Geometry.RCD.Sobolev.BochnerSourceUniqueness

namespace OAI

/-! # Comparison of Bochner densities under a lower curvature parameter -/

open Set Filter MeasureTheory
open scoped NNReal BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]

theorem signed_rnDeriv_two_add_density (ν : SignedMeasure X) {h : X → ℝ} (hh : Integrable h μ) :
    SignedMeasure.rnDeriv ((2:ℝ) • ν+μ.withDensityᵥ h) μ =ᵐ[μ]
      fun x => 2*ν.rnDeriv μ x+h x := by
  filter_upwards [SignedMeasure.rnDeriv_add ((2:ℝ) • ν) (μ.withDensityᵥ h) μ,
    SignedMeasure.rnDeriv_smul ν μ 2,signed_rnDeriv_density μ hh] with x ha hs hd
  rw [ha]
  simp only [Pi.add_apply]
  rw [hs,hd]
  simp only [Pi.smul_apply,smul_eq_mul]

variable [MetricSpace X] [BorelSpace X] [ProperSpace X] [SecondCountableTopology X]
  [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

/-- Decreasing the curvature parameter increases the Bochner density.
This compares the actual full local sources before passing to densities. -/
theorem bochnerDensity_curvature_le {Ω S : Set X} (hΩ : MeasurableSet Ω)
    (hS : MeasurableSet S) {J K : ℝ} (hJK : J≤K)
    (f d F G : SobolevSpace μ hQ) (ν τ : Measure X) [IsFiniteMeasure ν] [IsFiniteMeasure τ]
    (hF : IsMeasureLaplacianOn μ hQ Ω F (bochnerGramSource μ hQ K f f d d ν.toSignedMeasure))
    (hG : IsMeasureLaplacianOn μ hQ Ω G (bochnerGramSource μ hQ J f f d d τ.toSignedMeasure))
    (hFG : SobolevSpace.toLp μ hQ F =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ G)
    (χ : X →ᵇ ℝ) {L : ℝ≥0} (hχ : LipschitzWith L χ)
    (hχc : HasCompactSupport (χ : X → ℝ)) (hχΩ : tsupport χ ⊆ Ω)
    (hχ0 : ∀ x, 0≤χ x) (hχ1 : ∀ x ∈ S, χ x=1) :
    ∀ᵐ x ∂μ.restrict S, (ν.rnDeriv μ x).toReal≤(τ.rnDeriv μ x).toReal := by
  have he := hF.unique_restrict μ hQ hΩ hS hG hFG χ hχ hχc hχΩ hχ0 hχ1
  have hr := signed_rnDeriv_eq_on_of_restrict_eq μ hS he
  have hν := signed_rnDeriv_two_add_density μ ν.toSignedMeasure (bochnerDrift_integrable μ hQ K f f d d)
  have hτ := signed_rnDeriv_two_add_density μ τ.toSignedMeasure (bochnerDrift_integrable μ hQ J f f d d)
  filter_upwards [hr,ae_restrict_of_ae hν,ae_restrict_of_ae hτ,
    ae_restrict_of_ae (signed_rnDeriv_toSignedMeasure μ ν),
    ae_restrict_of_ae (signed_rnDeriv_toSignedMeasure μ τ),
    ae_restrict_of_ae (localGamma_self μ hQ f)] with x hr hν hτ hn ht hg
  change SignedMeasure.rnDeriv ((2:ℝ) • ν.toSignedMeasure+μ.withDensityᵥ (bochnerDrift μ hQ K f f d d)) μ x =
    SignedMeasure.rnDeriv ((2:ℝ) • τ.toSignedMeasure+μ.withDensityᵥ (bochnerDrift μ hQ J f f d d)) μ x at hr
  rw [hν,hτ,hn,ht] at hr
  dsimp only [bochnerDrift] at hr
  have hpos : 0≤(K-J)*localGamma μ hQ f f x := by
    rw [hg]
    exact mul_nonneg (sub_nonneg.mpr hJK) (sq_nonneg _)
  nlinarith only [hr,hpos]

end RegularPointCoordinates

end

end OAI
