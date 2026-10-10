import OAI.Geometry.RCD.Heat.HeatPoleIncrements
import OAI.Geometry.RCD.Heat.SupportedHeatEnvelope

namespace OAI

/-! # One fixed cutoff and the actual dyadic heat metrics at nearby poles -/

open Set Metric MeasureTheory
open scoped BigOperators InnerProductSpace NNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)
  {n : ℕ} (U : Euclidean n →L[ℝ] SobolevSpace μ hQ)
  {p : X} {ρ C : ℝ} (χ : GoodLaplacianCutoff μ hQ p ρ C)

/-- The cutoff remains fixed while the heat pole varies. -/
def dyadicHeatGramAt (x : X) {R lambda : ℝ} (hR : 0 < R) (hlambda : 0 < lambda) (i : ℕ) :
    Euclidean n ≃L[ℝ] Euclidean n :=
  cutoffHeatGramEquiv μ hQ hk χ.weight.continuous (χ.hasCompactSupport μ hQ)
    U (fun z => (χ.bounds z).1)
    (sq_pos_of_pos (show 0 < R / (2 : ℝ) ^ i from div_pos hR (by positivity))) x hlambda

theorem dyadicHeatGramAt_coe (x : X) {R lambda : ℝ} (hR : 0 < R) (hlambda : 0 < lambda) (i : ℕ) :
    (dyadicHeatGramAt μ hQ hk U χ x hR hlambda i : Euclidean n →L[ℝ] Euclidean n) =
      cutoffHeatGram μ hQ hk χ.weight.continuous (χ.hasCompactSupport μ hQ)
        U (sq_pos_of_pos (div_pos hR (show 0 < (2 : ℝ) ^ i by positivity))) x lambda := rfl

theorem dyadicHeatGramAt_isPositive (x : X) {R lambda : ℝ} (hR : 0 < R)
    (hlambda : 0 < lambda) (i : ℕ) :
    (dyadicHeatGramAt μ hQ hk U χ x hR hlambda i : Euclidean n →L[ℝ] Euclidean n).IsPositive := by
  rw [dyadicHeatGramAt_coe]
  exact cutoffHeatGram_isPositive μ hQ hk _ _ U (fun z => (χ.bounds z).1) _ x hlambda.le

theorem cutoffHeatGram_time_congr_at (x : X) {s t lambda : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hst : s = t) :
    cutoffHeatGram μ hQ hk χ.weight.continuous (χ.hasCompactSupport μ hQ) U hs x lambda =
      cutoffHeatGram μ hQ hk χ.weight.continuous (χ.hasCompactSupport μ hQ) U ht x lambda := by
  subst t
  rfl

variable {U} {M : PositiveBilinearMeasure X (Euclidean n)} {κ r : ℝ} {L : ℝ≥0}
  (G : ∀ v, LocalHarmonicEnergy μ hQ U M κ p r L v)

/-- The lower mass bound also remains centered at the heat pole. -/
theorem dyadicHeatGramAt_lower (x : X) (hρ : 0 < ρ) (hρr : ρ < r) (hκ : 0 ≤ κ)
    {R c η lambda : ℝ} (hR : 0 < R) (hlambda : 0 < lambda)
    (hreg : 2 * κ * (L : ℝ) ^ 2 + η ≤ lambda) (i : ℕ)
    (hχone : ∀ y ∈ ball x (R / 2 ^ i), (χ.weight : X → ℝ) y = 1)
    (herror : ∀ t ∈ Icc ((R / 2 ^ i) ^ 2 / 4) ((R / 2 ^ i) ^ 2),
      ‖harmonicHeatError μ hQ (k := ker) G χ t x‖ ≤ η)
    (hkernel : ∀ t ∈ Icc ((R / 2 ^ i) ^ 2 / 4) ((R / 2 ^ i) ^ 2),
      ∀ y ∈ ball x (R / 2 ^ i), c / (R / 2 ^ i) ^ n ≤ ker t x y)
    (v : Euclidean n) :
    (3 * c / 2) * ⟪v, dyadicBochnerMass M n x R i v⟫_ℝ ≤
      ⟪v, ((dyadicHeatGramAt μ hQ hk U χ x hR hlambda i : Euclidean n →L[ℝ] Euclidean n) -
        (dyadicHeatGramAt μ hQ hk U χ x hR hlambda (i + 1) : Euclidean n →L[ℝ] Euclidean n)) v⟫_ℝ := by
  have hs : 0 < R / (2 : ℝ) ^ i := div_pos hR (by positivity)
  have hb := harmonic_heat_increment_lower_mass_at μ hQ hk G χ x hρ hρr hκ
    (ball x (R / 2 ^ i)) measurableSet_ball hχone
    (div_pos (sq_pos_of_pos hs) (by norm_num : (0 : ℝ) < 4))
    (show (R / 2 ^ i) ^ 2 / 4 ≤ (R / 2 ^ i) ^ 2 by nlinarith [sq_nonneg (R / 2 ^ i)])
    hlambda.le hreg herror hkernel v
  have hnext := cutoffHeatGram_time_congr_at μ hQ hk U χ x (lambda := lambda)
    (sq_pos_of_pos (show 0 < R / (2 : ℝ) ^ (i + 1) from div_pos hR (by positivity)))
    (div_pos (sq_pos_of_pos hs) (by norm_num : (0 : ℝ) < 4)) (dyadic_radius_square_succ R i)
  simp only [dyadicBochnerMass_inner, M.measure_real v _ measurableSet_ball,
    sub_apply, inner_sub_right, dyadicHeatGramAt_coe]
  rw [hnext]
  convert hb using 1
  ring

/-- The upper mass envelope is centered at the pole, independently of the
center of the one fixed cutoff. -/
theorem dyadicHeatGramAt_upper_supported (x : X) (m : ℕ) (hn : n = m + 2)
    (hρ : 0 < ρ) (hρr : ρ < r) (hκ : 0 ≤ κ)
    {R A D η lambda : ℝ} (hR : 0 < R) (hlambda : 0 < lambda)
    (hA : 0 ≤ A) (hD : 0 < D) (hη : 0 ≤ η)
    (hreg : 2 * κ * (L : ℝ) ^ 2 + η ≤ lambda) (i : ℕ)
    (hχzero : ∀ z ∉ ball x R, (χ.weight : X → ℝ) z = 0)
    (herror : ∀ t ∈ Icc ((R / 2 ^ i) ^ 2 / 4) ((R / 2 ^ i) ^ 2),
      ‖harmonicHeatError μ hQ (k := ker) G χ t x‖ ≤ η)
    (hgaussian : ∀ t ∈ Icc ((R / 2 ^ i) ^ 2 / 4) ((R / 2 ^ i) ^ 2),
      ∀ q : ℝ, 0 ≤ q → ∀ z, q * (R / 2 ^ i) ≤ dist x z →
        (χ.weight : X → ℝ) z * ker t x z ≤
          (A / (R / 2 ^ i) ^ n) * Real.exp (-q ^ 2 / D)) (v : Euclidean n) :
    ⟪v, ((dyadicHeatGramAt μ hQ hk U χ x hR hlambda i : Euclidean n →L[ℝ] Euclidean n) -
        (dyadicHeatGramAt μ hQ hk U χ x hR hlambda (i + 1) : Euclidean n →L[ℝ] Euclidean n)) v⟫_ℝ ≤
      supportedHeatEnvelopeConstant m A D R lambda η *
        ⟪v, dyadicBochnerEnvelope M n x R i v⟫_ℝ := by
  let s := R / (2 : ℝ) ^ i
  let S := ∑ j ∈ Finset.range (i + 1), (3 / 4 : ℝ) ^ (i - j) *
    ⟪v, dyadicBochnerMass M n x R j v⟫_ℝ
  have hs : 0 < s := div_pos hR (by positivity)
  have hroot : (2 : ℝ) ^ i * s = R := by dsimp only [s]; field_simp
  have hsum : (∑ j ∈ Finset.range (i + 1), (3 / 4 : ℝ) ^ j *
      (((2 ^ j * s) ^ 2 / (2 ^ j * s) ^ (m + 2)) *
        (M.measure v).real (ball x (2 ^ j * s)))) = S := by
    rw [outward_sum_eq_inward_sum (fun r => (r ^ 2 / r ^ (m + 2)) *
      (M.measure v).real (ball x r)) (3 / 4) i hroot]
    simp only [S, dyadicBochnerMass_inner, hn]
  have hm (t : ℝ) (ht : t ∈ Icc (s ^ 2 / 4) (s ^ 2)) (htp : 0 < t) :
      s ^ 2 * ⟪v, cutoffHeatMass μ hQ hk χ.weight.continuous
        (χ.hasCompactSupport μ hQ) M htp x v⟫_ℝ ≤ A * gaussianMassConvolutionConstant m D⁻¹ * S := by
    have hb := scaled_cutoffHeatMass_le_geometric μ hQ hk χ.weight.continuous
      (χ.hasCompactSupport μ hQ) M m x hs htp hA (inv_pos.mpr hD) (le_refl (0 : ℝ)) i
      (fun j _ z hz => by
        apply shell_bound_of_displacement x hs (fun z => (χ.weight : X → ℝ) z * ker t x z)
          (fun q hq z hsep => by simpa only [hn] using hgaussian t ht q hq z hsep) j hz)
      (fun z hz => by rw [hroot] at hz; rw [hχzero z hz, zero_mul]) v
    simpa only [hsum, mul_zero, zero_mul, add_zero] using hb
  have hb := dyadic_heat_increment_upper_bound_at μ hQ hk G χ x hρ hρr hκ hs
    hlambda.le hreg herror v hm
  have hnext := cutoffHeatGram_time_congr_at μ hQ hk U χ x (lambda := lambda)
    (sq_pos_of_pos (show 0 < R / (2 : ℝ) ^ (i + 1) from div_pos hR (by positivity)))
    (div_pos (sq_pos_of_pos hs) (by norm_num : (0 : ℝ) < 4)) (dyadic_radius_square_succ R i)
  simp only [sub_apply, inner_sub_right, dyadicHeatGramAt_coe]
  rw [hnext, dyadicBochnerEnvelope_inner]
  change _ ≤ supportedHeatEnvelopeConstant m A D R lambda η *
    ((3 / 4 : ℝ) ^ i * ‖v‖ ^ 2 + S)
  have hG := gaussianMassConvolutionConstant_nonneg m D⁻¹
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ =>
    mul_nonneg (by positivity) ((dyadicBochnerMass_isPositive M n x hR.le j).inner_nonneg_right v)
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
