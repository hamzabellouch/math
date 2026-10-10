import OAI.Geometry.RCD.Heat.DyadicHeatFamily

namespace OAI

/-! # A supported heat envelope with no exterior mass constant -/

open Set Metric MeasureTheory
open scoped BigOperators InnerProductSpace NNReal

noncomputable section

namespace RegularPointCoordinates

/-- The supported upper-decrement constant has no dependence on the
total Bochner mass outside the working ball. -/
def supportedHeatEnvelopeConstant (m : ℕ) (A D R lambda η : ℝ) : ℝ :=
  (3 / 2 : ℝ) * A * gaussianMassConvolutionConstant m D⁻¹ +
    (3 / 4 : ℝ) * R ^ 2 * (lambda + η)

theorem supportedHeatEnvelopeConstant_nonneg (m : ℕ) {A D R lambda η : ℝ}
    (hA : 0 ≤ A) (hreg : 0 ≤ lambda + η) :
    0 ≤ supportedHeatEnvelopeConstant m A D R lambda η := by
  have hg := gaussianMassConvolutionConstant_nonneg m D⁻¹
  unfold supportedHeatEnvelopeConstant
  positivity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)
  {n : ℕ} {U : Euclidean n →L[ℝ] SobolevSpace μ hQ}
  {M : PositiveBilinearMeasure X (Euclidean n)} {κ r : ℝ} {p : X} {L : ℝ≥0}
  (G : ∀ v, LocalHarmonicEnergy μ hQ U M κ p r L v)
  {ρ Ccut : ℝ} (χ : GoodLaplacianCutoff μ hQ p ρ Ccut)

/-- With cutoff support inside the fixed outer ball, the exterior term
vanishes exactly. The actual upper heat decrement then has a constant
depending only on Gaussian bounds, scale and regularization. -/
theorem dyadicHeatGram_upper_supported (m : ℕ) (hn : n = m + 2)
    (hρ : 0 < ρ) (hρr : ρ < r) (hκ : 0 ≤ κ)
    {R A D η lambda : ℝ} (hR : 0 < R) (hlambda : 0 < lambda)
    (hA : 0 ≤ A) (hD : 0 < D) (hη : 0 ≤ η)
    (hreg : 2 * κ * (L : ℝ) ^ 2 + η ≤ lambda) (i : ℕ)
    (hχzero : ∀ z ∉ ball p R, (χ.weight : X → ℝ) z = 0)
    (herror : ∀ t ∈ Icc ((R / 2 ^ i) ^ 2 / 4) ((R / 2 ^ i) ^ 2),
      ‖harmonicHeatError μ hQ (k := ker) G χ t p‖ ≤ η)
    (hgaussian : ∀ t ∈ Icc ((R / 2 ^ i) ^ 2 / 4) ((R / 2 ^ i) ^ 2),
      ∀ q : ℝ, 0 ≤ q → ∀ z, q * (R / 2 ^ i) ≤ dist p z →
        (χ.weight : X → ℝ) z * ker t p z ≤
          (A / (R / 2 ^ i) ^ n) * Real.exp (-q ^ 2 / D)) (v : Euclidean n) :
    ⟪v, ((dyadicHeatGram μ hQ hk U χ hR hlambda i : Euclidean n →L[ℝ] Euclidean n) -
        (dyadicHeatGram μ hQ hk U χ hR hlambda (i + 1) : Euclidean n →L[ℝ] Euclidean n)) v⟫_ℝ ≤
      supportedHeatEnvelopeConstant m A D R lambda η *
        ⟪v, dyadicBochnerEnvelope M n p R i v⟫_ℝ := by
  let s := R / (2 : ℝ) ^ i
  let S := ∑ j ∈ Finset.range (i + 1), (3 / 4 : ℝ) ^ (i - j) *
    ⟪v, dyadicBochnerMass M n p R j v⟫_ℝ
  have hs : 0 < s := div_pos hR (by positivity)
  have hroot : (2 : ℝ) ^ i * s = R := by dsimp only [s]; field_simp
  have hsum : (∑ j ∈ Finset.range (i + 1), (3 / 4 : ℝ) ^ j *
      (((2 ^ j * s) ^ 2 / (2 ^ j * s) ^ (m + 2)) *
        (M.measure v).real (ball p (2 ^ j * s)))) = S := by
    rw [outward_sum_eq_inward_sum (fun r => (r ^ 2 / r ^ (m + 2)) *
      (M.measure v).real (ball p r)) (3 / 4) i hroot]
    simp only [S, dyadicBochnerMass_inner, hn]
  have hm (t : ℝ) (ht : t ∈ Icc (s ^ 2 / 4) (s ^ 2)) (htp : 0 < t) :
      s ^ 2 * ⟪v, cutoffHeatMass μ hQ hk χ.weight.continuous
        (χ.hasCompactSupport μ hQ) M htp p v⟫_ℝ ≤ A * gaussianMassConvolutionConstant m D⁻¹ * S := by
    have hb := scaled_cutoffHeatMass_le_geometric μ hQ hk χ.weight.continuous
      (χ.hasCompactSupport μ hQ) M m p hs htp hA (inv_pos.mpr hD) (le_refl (0 : ℝ)) i
      (fun j _ z hz => by
        apply shell_bound_of_displacement p hs (fun z => (χ.weight : X → ℝ) z * ker t p z)
          (fun q hq z hsep => by simpa only [hn] using hgaussian t ht q hq z hsep) j hz)
      (fun z hz => by rw [hroot] at hz; rw [hχzero z hz, zero_mul]) v
    simpa only [hsum, mul_zero, zero_mul, add_zero] using hb
  have hb := dyadic_heat_increment_upper_bound μ hQ hk G χ hρ hρr hκ hs
    hlambda.le hreg herror v hm
  have hnext := cutoffHeatGram_time_congr μ hQ hk U χ (lambda := lambda)
    (sq_pos_of_pos (show 0 < R / (2 : ℝ) ^ (i + 1) from div_pos hR (by positivity)))
    (div_pos (sq_pos_of_pos hs) (by norm_num : (0 : ℝ) < 4)) (dyadic_radius_square_succ R i)
  simp only [sub_apply, inner_sub_right, dyadicHeatGram_coe]
  rw [hnext, dyadicBochnerEnvelope_inner]
  change _ ≤ supportedHeatEnvelopeConstant m A D R lambda η *
    ((3 / 4 : ℝ) ^ i * ‖v‖ ^ 2 + S)
  have hG := gaussianMassConvolutionConstant_nonneg m D⁻¹
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ =>
    mul_nonneg (by positivity) ((dyadicBochnerMass_isPositive M n p hR.le j).inner_nonneg_right v)
  have hrl : 0 ≤ lambda + η := add_nonneg hlambda.le hη
  have hsmall := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (dyadic_square_le_three_quarters hs.le i hroot) hrl) (sq_nonneg ‖v‖)
  have hcross₁ : 0 ≤ ((3 / 2 : ℝ) * A * gaussianMassConvolutionConstant m D⁻¹) *
      ((3 / 4 : ℝ) ^ i * ‖v‖ ^ 2) := by positivity
  have hcross₂ : 0 ≤ ((3 / 4 : ℝ) * R ^ 2 * (lambda + η)) * S := by positivity
  unfold supportedHeatEnvelopeConstant
  nlinarith only [hb, hsmall, hcross₁, hcross₂]

end RegularPointCoordinates

end

end OAI
