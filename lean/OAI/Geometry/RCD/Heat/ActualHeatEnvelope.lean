import OAI.Geometry.RCD.Sobolev.DyadicBochnerMass
import OAI.Geometry.RCD.Metric.DyadicMassReindex

namespace OAI

/-! # The Gaussian upper decrement in terms of the actual Bochner envelope -/

open Set Metric MeasureTheory
open scoped BigOperators InnerProductSpace NNReal

noncomputable section

namespace RegularPointCoordinates

variable {X E : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A single constant for the shell convolution, exterior finite mass and
scalar regularizer, independent of the dyadic index and vector. -/
def dyadicHeatEnvelopeConstant (M : PositiveBilinearMeasure X E) (m : ℕ)
    (A D R lambda η : ℝ) : ℝ :=
  (3 / 2 : ℝ) * A * gaussianMassConvolutionConstant m D⁻¹ +
    ((3 / 2 : ℝ) * A * gaussianMassConvolutionConstant m D⁻¹ *
      (R ^ 2 / R ^ (m + 2)) * ‖M.massOperator univ‖ +
      (3 / 4 : ℝ) * R ^ 2 * (lambda + η))

omit [MetricSpace X] [BorelSpace X] in
theorem dyadicHeatEnvelopeConstant_nonneg (M : PositiveBilinearMeasure X E) (m : ℕ)
    {A D R lambda η : ℝ} (hA : 0 ≤ A) (hR : 0 ≤ R) (hreg : 0 ≤ lambda + η) :
    0 ≤ dyadicHeatEnvelopeConstant M m A D R lambda η := by
  have hG := gaussianMassConvolutionConstant_nonneg m D⁻¹
  unfold dyadicHeatEnvelopeConstant
  positivity

/-- Reindexing the Gaussian shell bound and using the finite total source
gives the desired actual positive operator envelope. -/
theorem gaussian_mass_budget_le_envelope (M : PositiveBilinearMeasure X E)
    (m N : ℕ) (p : X) {s R A D lambda η : ℝ}
    (hs : 0 < s) (hR : (2 : ℝ) ^ N * s = R)
    (hA : 0 ≤ A) (hD : 0 < D) (hreg_nonneg : 0 ≤ lambda + η) (v : E) :
    (3 / 2 : ℝ) * (A * gaussianMassConvolutionConstant m D⁻¹ *
      (∑ j ∈ Finset.range (N + 1), (3 / 4 : ℝ) ^ j *
        (((2 ^ j * s) ^ 2 / (2 ^ j * s) ^ (m + 2)) *
          (M.measure v).real (ball p (2 ^ j * s)))) +
      s ^ 2 * ((A / s ^ (m + 2)) * Real.exp (-(4 : ℝ) ^ N / D)) *
        (M.measure v).real univ) +
      (3 / 4 : ℝ) * s ^ 2 * (lambda + η) * ‖v‖ ^ 2 ≤
    dyadicHeatEnvelopeConstant M m A D R lambda η *
      ⟪v, dyadicBochnerEnvelope M (m + 2) p R N v⟫_ℝ := by
  have hRp : 0 < R := hR ▸ mul_pos (by positivity) hs
  let a := (3 / 2 : ℝ) * A * gaussianMassConvolutionConstant m D⁻¹
  let b := (3 / 2 : ℝ) * A * gaussianMassConvolutionConstant m D⁻¹ *
    (R ^ 2 / R ^ (m + 2)) * ‖M.massOperator univ‖ +
    (3 / 4 : ℝ) * R ^ 2 * (lambda + η)
  let B := (3 / 4 : ℝ) ^ N * ‖v‖ ^ 2
  let S := ∑ j ∈ Finset.range (N + 1), (3 / 4 : ℝ) ^ (N - j) *
    ⟪v, dyadicBochnerMass M (m + 2) p R j v⟫_ℝ
  have hG : 0 ≤ gaussianMassConvolutionConstant m D⁻¹ :=
    gaussianMassConvolutionConstant_nonneg m D⁻¹
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hS : 0 ≤ S := by
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (by positivity)
      ((dyadicBochnerMass_isPositive M (m + 2) p hRp.le j).inner_nonneg_right v)
  have hsum : (∑ j ∈ Finset.range (N + 1), (3 / 4 : ℝ) ^ j *
      (((2 ^ j * s) ^ 2 / (2 ^ j * s) ^ (m + 2)) *
        (M.measure v).real (ball p (2 ^ j * s)))) = S := by
    rw [outward_sum_eq_inward_sum (fun r => (r ^ 2 / r ^ (m + 2)) *
      (M.measure v).real (ball p r)) (3 / 4) N hR]
    simp only [S, dyadicBochnerMass_inner]
  have hext := heat_exterior_term_le_geometric m N hs hA hD
    (show 0 ≤ (M.measure v).real univ from ENNReal.toReal_nonneg) hR
  have hmass := bochner_total_mass_le M v
  have hext' := hext.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmass (by positivity :
      0 ≤ A * gaussianMassConvolutionConstant m D⁻¹ * (R ^ 2 / R ^ (m + 2))))
    (by positivity : 0 ≤ (3 / 4 : ℝ) ^ N))
  have hreg := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (dyadic_square_le_three_quarters hs.le N hR) hreg_nonneg)
    (sq_nonneg ‖v‖)
  rw [hsum, dyadicBochnerEnvelope_inner]
  change _ ≤ (a + b) * (B + S)
  dsimp only [a, b, B] at ha hb hB ⊢
  nlinarith [mul_nonneg ha hB, mul_nonneg hb hS]

variable [ProperSpace X] (μ : Measure X) [μ.Regular]
  (hQ : QuadraticCheegerEnergy μ) {ker : ℝ → X → X → ℝ}
  (hk : IsContinuousHeatKernel μ hQ ker)
  {n : ℕ} {U : Euclidean n →L[ℝ] SobolevSpace μ hQ}
  {M : PositiveBilinearMeasure X (Euclidean n)} {κ : ℝ} {p : X} {r : ℝ} {L : ℝ≥0}
  (G : ∀ v, LocalHarmonicEnergy μ hQ U M κ p r L v)
  {ρ Ccut : ℝ} (χ : GoodLaplacianCutoff μ hQ p ρ Ccut)

/-- The actual cutoff heat Gram satisfies the upper envelope required by
the cumulative comparison, with the actual scaled Bochner mass operators. -/
theorem gaussian_dyadic_heat_increment_envelope (m : ℕ)
    (hρ : 0 < ρ) (hρr : ρ < r) (hκ : 0 ≤ κ)
    {s R A D η lambda : ℝ} (hs : 0 < s) (hA : 0 ≤ A) (hD : 0 < D)
    (hη : 0 ≤ η) (hlambda0 : 0 ≤ lambda)
    (hlambda : 2 * κ * (L : ℝ) ^ 2 + η ≤ lambda)
    (herror : ∀ t ∈ Icc (s ^ 2 / 4) (s ^ 2), ‖harmonicHeatError μ hQ (k := ker) G χ t p‖ ≤ η)
    (hgaussian : ∀ t ∈ Icc (s ^ 2 / 4) (s ^ 2), ∀ q : ℝ, 0 ≤ q → ∀ z,
      q * s ≤ dist p z → (χ.weight : X → ℝ) z * ker t p z ≤
        (A / s ^ (m + 2)) * Real.exp (-q ^ 2 / D))
    (N : ℕ) (hR : (2 : ℝ) ^ N * s = R) (v : Euclidean n) :
    ⟪v, cutoffHeatGram μ hQ hk χ.weight.continuous (χ.hasCompactSupport μ hQ)
      U (sq_pos_of_pos hs) p lambda v⟫_ℝ -
    ⟪v, cutoffHeatGram μ hQ hk χ.weight.continuous (χ.hasCompactSupport μ hQ)
      U (div_pos (sq_pos_of_pos hs) (by norm_num : (0 : ℝ) < 4)) p lambda v⟫_ℝ ≤
    dyadicHeatEnvelopeConstant M m A D R lambda η *
      ⟪v, dyadicBochnerEnvelope M (m + 2) p R N v⟫_ℝ :=
  (gaussian_dyadic_heat_increment_upper μ hQ hk G χ m hρ hρr hκ hs hA hD
    hlambda0 hlambda herror hgaussian N v).trans
      (gaussian_mass_budget_le_envelope M m N p hs hR hA hD (add_nonneg hlambda0 hη) v)

end RegularPointCoordinates

end

end OAI
