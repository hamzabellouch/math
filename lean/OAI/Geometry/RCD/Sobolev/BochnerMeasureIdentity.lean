import OAI.Geometry.RCD.Sobolev.MeasureLaplacianProduct

namespace OAI

/-! # From positive Bochner test identities to the full measure Laplacian -/

open Set Filter MeasureTheory
open scoped BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [ProperSpace X] in
theorem bochner_measure_laplacian {Ω : Set X} (hΩ : MeasurableSet Ω)
    (f G : SobolevSpace μ hQ) (κ : ℝ) (σ : Measure X) [IsFiniteMeasure σ]
    (hG : SobolevSpace.toLp μ hQ G =ᵐ[μ.restrict Ω] localGamma μ hQ f f)
    (hσ : ∀ (ψ : SobolevSpace μ hQ) (v : X → ℝ), Continuous v → HasCompactSupport v →
      tsupport v ⊆ Ω → SobolevSpace.toLp μ hQ ψ =ᵐ[μ] v →
      (∫ x, v x ∂σ) = -(1 / 2 : ℝ) * energyForm μ hQ G ψ +
        κ * inner ℝ (SobolevSpace.toLp μ hQ ψ) (SobolevSpace.toLp μ hQ G)) :
    IsMeasureLaplacianOn μ hQ Ω G
      ((2 : ℝ) • σ.toSignedMeasure - (2 * κ) • μ.withDensityᵥ (localGamma μ hQ f f)) := by
  intro ψ v hv hs hvs hψ
  let w : X →ᵇ ℝ := ofCompactSupport v hv hs
  have hI : inner ℝ (SobolevSpace.toLp μ hQ ψ) (SobolevSpace.toLp μ hQ G) =
      ∫ x, v x * localGamma μ hQ f f x ∂μ := by
    rw [L2.inner_def]
    have hG' := (ae_restrict_iff' hΩ).mp hG
    apply integral_congr_ae
    filter_upwards [hG', hψ] with x hx hy
    simp only [Real.inner_apply, hy]
    by_cases hmem : x ∈ Ω
    · rw [hx hmem]
    · have hz := image_eq_zero_of_notMem_tsupport (fun hm => hmem (hvs hm))
      rw [hz, zero_mul, zero_mul]
  have hν : (∫ᵛ x, w x ∂<•((2 : ℝ) • σ.toSignedMeasure -
        (2 * κ) • μ.withDensityᵥ (localGamma μ hQ f f))) =
      2 * (∫ x, w x ∂σ) - 2 * κ * ∫ x, w x * localGamma μ hQ f f x ∂μ := by
    rw [VectorMeasure.integral_sub_vectorMeasure
      (PositiveBilinearMeasure.integrable_weight w _)
      (PositiveBilinearMeasure.integrable_weight w _),
      VectorMeasure.integral_smul_vectorMeasure, VectorMeasure.integral_smul_vectorMeasure,
      VectorMeasure.integral_toSignedMeasure, integral_signedDensity _ (localGamma_memL1 μ hQ f f)]
    rfl
  have hh := hσ ψ v hv hs hvs hψ
  rw [hI] at hh
  change energyForm μ hQ G ψ = -(∫ᵛ x, w x ∂<•((2 : ℝ) • σ.toSignedMeasure -
    (2 * κ) • μ.withDensityᵥ (localGamma μ hQ f f)))
  rw [hν]
  change energyForm μ hQ G ψ = -(2 * (∫ x, v x ∂σ) -
    2 * κ * ∫ x, v x * localGamma μ hQ f f x ∂μ)
  linarith

end RegularPointCoordinates

end

end OAI
