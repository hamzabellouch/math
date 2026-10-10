import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Coordinates.BoundedSourceIntegral
import OAI.Geometry.RCD.Sobolev.CutoffEnergyBound

namespace OAI

/-! # Actual curvature-source integrals for the harmonic coordinate map -/

open Set Metric MeasureTheory Filter
open scoped InnerProductSpace NNReal ENNReal BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] [IsLocallyFiniteMeasure μ] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
include hk in
/-- The short- and long-time curvature pairings of the genuine cutoff
energy have a uniform vanishing bound. The same constant works in every
direction and does not depend on the working radius. -/
theorem exists_harmonic_curvature_integral_bound (hg : HasCoordinateHeatBounds μ ker)
    (hdiff : HasGaussianHeatDifferenceBounds μ ker)
    (n : ℕ) {A V W : ℝ} (hA : 0 ≤ A) (hV : 0 < V) (hW : 0 ≤ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ), 0 < R → R ≤ 1 → ∀ (i : ℕ) (x q : X),
      μ (ball q (R / 2 ^ i)) ≠ ∞ →
      V * (R / 2 ^ i) ^ n ≤ μ.real (ball q (R / 2 ^ i)) → dist x q ≤ A * (R / 2 ^ i) →
      (∀ j, μ.real (ball x (R / 2 ^ j)) ≤ W * (R / 2 ^ j) ^ n) →
      (∀ t, 0 < t → t ≤ R ^ 2 → ∀ z ∈ ball x R,
        V * (Real.sqrt t) ^ n ≤ μ.real (ball z (Real.sqrt t))) →
      ∀ (U : E →L[ℝ] SobolevSpace μ hQ) (M : PositiveBilinearMeasure X E)
        (κ : ℝ) (p : X) (r : ℝ) (L : ℝ≥0) (v : E)
        (_G : LocalHarmonicEnergy μ hQ U M κ p r L v) (χ : X →ᵇ ℝ),
      (∀ z, 0 ≤ χ z ∧ χ z ≤ 1) → tsupport (χ : X → ℝ) ⊆ ball p (2 * r) →
      (∀ z ∉ ball x R, χ z = 0) → ∀ (c : SobolevSpace μ hQ),
      SobolevSpace.toLp μ hQ c =ᵐ[μ] χ →
      |∫ t in (0 : ℝ)..(R / 2 ^ i) ^ 2,
        ∫ z, kernelAverage μ ker t (ball q (R / 2 ^ i)) z *
          (χ z * localGamma μ hQ (U v) (U v) z) ∂μ| +
      |∫ t in (R / 2 ^ i) ^ 2..R ^ 2,
        ∫ z, (kernelAverage μ ker t (ball q (R / 2 ^ i)) z - ker t x z) *
          (χ z * localGamma μ hQ (U v) (U v) z) ∂μ| ≤
      C * ((L : ℝ) ^ 2 * ‖v‖ ^ 2) * ((R / 2 ^ i) ^ 2 + (R / 2 ^ i) * R) := by
  obtain ⟨C₀, hC₀, hsbound⟩ := exists_short_bounded_source_integral_bound μ hQ hk hg n hA hV hW
  obtain ⟨C₁, hC₁, hlbound⟩ := exists_long_bounded_source_integral_bound μ hQ hk hg hdiff n hA hV hW
  refine ⟨C₀ + C₁, add_pos hC₀ hC₁, ?_⟩
  intro R hR hR1 i x q hfinite hvolume hcenter hupper hsource U M κ p r L v G χ hχ hχΩ hzero c hc
  let f := SobolevSpace.toLp μ hQ (G.cutoffEnergy μ hQ χ c)
  let B := (L : ℝ) ^ 2 * ‖v‖ ^ 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hfb : ∀ᵐ z ∂μ, |f z| ≤ B := G.cutoffEnergy_bound μ hQ χ hχ c hc
  have hfzero : ∀ᵐ z ∂μ, z ∉ ball x R → f z = 0 := G.cutoffEnergy_zero_off μ hQ χ c hc hzero
  have hroot : (2 : ℝ) ^ i * (R / (2 : ℝ) ^ i) = R := by field_simp
  have hvol : ∀ j ≤ i, μ.real (ball x (2 ^ j * (R / (2 : ℝ) ^ i))) ≤
      W * (2 ^ j * (R / (2 : ℝ) ^ i)) ^ n := by
    intro j hj
    have he := outward_radius_eq_ancestor hroot (Nat.sub_le i j)
    simp only [Nat.sub_sub_self hj] at he
    rw [he]
    exact hupper (i - j)
  have hs := hsbound R hR hR1 i x q hfinite hvolume hcenter hvol hsource f B hB hfb hfzero
  have hpos : 0 < μ.real (ball q (R / (2 : ℝ) ^ i)) :=
    (mul_pos hV (pow_pos (div_pos hR (by positivity)) n)).trans_le hvolume
  have hl := hlbound R hR hR1 i x q hfinite hpos hcenter hupper hsource f B hB hfb hfzero
  have hf : f =ᵐ[μ] fun z => χ z * localGamma μ hQ (U v) (U v) z := by
    filter_upwards [G.cutoffEnergy_coe μ hQ χ hχΩ c hc, localGamma_self μ hQ (U v)] with z hz hΓ
    simpa only [f, hΓ] using hz
  have he (k : X → ℝ) : (∫ z, k z * (χ z * localGamma μ hQ (U v) (U v) z) ∂μ) =
      ∫ z, k z * f z ∂μ := by
    apply integral_congr_ae
    filter_upwards [hf] with z hz
    rw [hz]
  simp_rw [he]
  have hr : 0 < R / (2 : ℝ) ^ i := div_pos hR (by positivity)
  have hcross₀ : 0 ≤ C₀ * B * ((R / (2 : ℝ) ^ i) * R) := by positivity
  have hcross₁ : 0 ≤ C₁ * B * (R / (2 : ℝ) ^ i) ^ 2 := by positivity
  change _ ≤ (C₀ + C₁) * B * ((R / (2 : ℝ) ^ i) ^ 2 + (R / (2 : ℝ) ^ i) * R)
  nlinarith only [hs, hl, hcross₀, hcross₁]

end RegularPointCoordinates

end

end OAI
