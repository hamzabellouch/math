import OAI.Geometry.RCD.Heat.HarmonicBochnerHeat

namespace OAI

/-! # Uniform bounds for the actual compact energy density -/

open Set MeasureTheory Filter
open scoped NNReal BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {U : E →L[ℝ] SobolevSpace μ hQ} {M : PositiveBilinearMeasure X E}
  {κ : ℝ} {p : X} {r : ℝ} {L : ℝ≥0} {v : E}

omit [ProperSpace X] [FiniteDimensional ℝ E] in
/-- The true Sobolev product inherits the original directional gradient
bound because the cutoff takes values in [0,1]. -/
theorem LocalHarmonicEnergy.cutoffEnergy_bound
    (G : LocalHarmonicEnergy μ hQ U M κ p r L v)
    (χ : X →ᵇ ℝ) (hχ : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1)
    (c : SobolevSpace μ hQ) (hc : SobolevSpace.toLp μ hQ c =ᵐ[μ] χ) :
    ∀ᵐ z ∂μ, |SobolevSpace.toLp μ hQ (G.cutoffEnergy μ hQ χ c) z| ≤
      (L : ℝ) ^ 2 * ‖v‖ ^ 2 := by
  have hcb : ∀ᵐ z ∂μ, |SobolevSpace.toLp μ hQ c z| ≤ (‖χ‖₊ : ℝ) := by
    filter_upwards [hc] with z hz
    simpa only [hz, Real.norm_eq_abs, coe_nnnorm] using χ.norm_coe_le_norm z
  have hp := SobolevSpace.product_coe μ hQ G.energy c (L ^ 2 * ‖v‖₊ ^ 2) ‖χ‖₊ G.bounded hcb
  filter_upwards [hp, G.bounded, hc] with z hz hg hcz
  change |SobolevSpace.toLp μ hQ (SobolevSpace.product μ hQ G.energy c _ _) z| ≤ _
  rw [hz, hcz, abs_mul]
  have hχz : |χ z| ≤ 1 := by rw [abs_of_nonneg (hχ z).1]; exact (hχ z).2
  have hgb : |SobolevSpace.toLp μ hQ G.energy z| ≤ (L : ℝ) ^ 2 * ‖v‖ ^ 2 := by
    simpa only [NNReal.coe_mul, NNReal.coe_pow, coe_nnnorm] using hg
  exact (mul_le_mul hgb hχz (abs_nonneg _) (by positivity)).trans_eq (mul_one _)

omit [ProperSpace X] [FiniteDimensional ℝ E] in
/-- The compact density vanishes off any region containing the cutoff. -/
theorem LocalHarmonicEnergy.cutoffEnergy_zero_off
    (G : LocalHarmonicEnergy μ hQ U M κ p r L v)
    (χ : X →ᵇ ℝ) (c : SobolevSpace μ hQ) (hc : SobolevSpace.toLp μ hQ c =ᵐ[μ] χ)
    {A : Set X} (hzero : ∀ z ∉ A, χ z = 0) :
    ∀ᵐ z ∂μ, z ∉ A → SobolevSpace.toLp μ hQ (G.cutoffEnergy μ hQ χ c) z = 0 :=
  cutoffProduct_zero_off μ hQ G.energy c χ hc _ G.bounded hzero

end RegularPointCoordinates

end

end OAI
