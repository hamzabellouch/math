import OAI.Geometry.RCD.Sobolev.SupportedEnergyLocality
import OAI.Geometry.RCD.Sobolev.BochnerMeasureIdentity
import OAI.Geometry.RCD.Sobolev.SobolevTestFunctional

namespace OAI

/-! # The bilinear scalar Bochner test form -/

open Set Filter MeasureTheory
open scoped BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

def bochnerTestForm (κ : ℝ) : SobolevSpace μ hQ →ₗ[ℝ] SobolevSpace μ hQ →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun G ψ => -(1 / 2 : ℝ) * energyForm μ hQ G ψ +
      κ * inner ℝ (SobolevSpace.toLp μ hQ ψ) (SobolevSpace.toLp μ hQ G))
    (by intro G H ψ; simp only [energyForm_add_left, map_add, inner_add_right]; ring)
    (by intro a G ψ; simp only [energyForm_smul_left, map_smul, real_inner_smul_right]; ring)
    (by intro G ψ φ; simp only [energyForm_add_right, map_add, inner_add_left]; ring)
    (by intro a G ψ; simp only [energyForm_smul_right, map_smul, real_inner_smul_left]; ring)

omit [BorelSpace X] in
theorem bochnerTestForm_apply (κ : ℝ) (G ψ : SobolevSpace μ hQ) :
    bochnerTestForm μ hQ κ G ψ = -(1 / 2 : ℝ) * energyForm μ hQ G ψ +
      κ * inner ℝ (SobolevSpace.toLp μ hQ ψ) (SobolevSpace.toLp μ hQ G) := rfl

theorem bochnerTestForm_congr_on [ProperSpace X] {Ω : Set X} (hΩ : MeasurableSet Ω)
    (κ : ℝ) {G H : SobolevSpace μ hQ}
    (hGH : SobolevSpace.toLp μ hQ G =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ H)
    (ψ : SobolevSpace μ hQ) (v : X → ℝ) (hψ : SobolevSpace.toLp μ hQ ψ =ᵐ[μ] v)
    (hv : tsupport v ⊆ Ω) : bochnerTestForm μ hQ κ G ψ = bochnerTestForm μ hQ κ H ψ := by
  rw [bochnerTestForm_apply, bochnerTestForm_apply,
    energyForm_eq_of_test_support μ hQ hΩ hGH v hψ hv]
  congr 2
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(ae_restrict_iff' hΩ).mp hGH, hψ] with x hx hpx
  simp only [Real.inner_apply, hpx]
  by_cases hm : x ∈ Ω
  · rw [hx hm]
  · rw [image_eq_zero_of_notMem_tsupport (fun hs => hm (hv hs)), zero_mul, zero_mul]

theorem bochnerTestForm_of_measure_laplacian {Ω : Set X} (hΩ : MeasurableSet Ω)
    (f G : SobolevSpace μ hQ) (κ : ℝ) (σ : Measure X) [IsFiniteMeasure σ]
    (hG : SobolevSpace.toLp μ hQ G =ᵐ[μ.restrict Ω] localGamma μ hQ f f)
    (hΔ : IsMeasureLaplacianOn μ hQ Ω G
      ((2 : ℝ) • σ.toSignedMeasure - (2 * κ) • μ.withDensityᵥ (localGamma μ hQ f f)))
    (ψ : SobolevSpace μ hQ) (v : X → ℝ) (hv : Continuous v) (hs : HasCompactSupport v)
    (hvs : tsupport v ⊆ Ω) (hψ : SobolevSpace.toLp μ hQ ψ =ᵐ[μ] v) :
    bochnerTestForm μ hQ κ G ψ = ∫ x, v x ∂σ := by
  let w : X →ᵇ ℝ := ofCompactSupport v hv hs
  have hI : inner ℝ (SobolevSpace.toLp μ hQ ψ) (SobolevSpace.toLp μ hQ G) =
      ∫ x, v x * localGamma μ hQ f f x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(ae_restrict_iff' hΩ).mp hG, hψ] with x hx hy
    simp only [Real.inner_apply, hy]
    by_cases hm : x ∈ Ω
    · rw [hx hm]
    · rw [image_eq_zero_of_notMem_tsupport (fun ht => hm (hvs ht)), zero_mul, zero_mul]
  have hd := hΔ ψ v hv hs hvs hψ
  change energyForm μ hQ G ψ = -(∫ᵛ x, w x ∂<•((2 : ℝ) • σ.toSignedMeasure -
    (2 * κ) • μ.withDensityᵥ (localGamma μ hQ f f))) at hd
  rw [VectorMeasure.integral_sub_vectorMeasure
    (PositiveBilinearMeasure.integrable_weight w _) (PositiveBilinearMeasure.integrable_weight w _),
    VectorMeasure.integral_smul_vectorMeasure, VectorMeasure.integral_smul_vectorMeasure,
    VectorMeasure.integral_toSignedMeasure, integral_signedDensity μ (localGamma_memL1 μ hQ f f)] at hd
  change energyForm μ hQ G ψ = -(2 * (∫ x, v x ∂σ) -
    2 * κ * ∫ x, v x * localGamma μ hQ f f x ∂μ) at hd
  rw [bochnerTestForm_apply, hI]
  linarith

end RegularPointCoordinates

end

end OAI
