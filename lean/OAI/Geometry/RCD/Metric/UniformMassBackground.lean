import OAI.Geometry.RCD.Sobolev.DyadicBochnerMass
import OAI.Geometry.RCD.Heat.FinitePrefixEnvelope

namespace OAI

/-! # One finite coarse-scale mass bound for every center -/

open Set Metric MeasureTheory
open scoped InnerProductSpace BigOperators

noncomputable section
namespace RegularPointCoordinates

variable {X E : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The total full Bochner measure bounds the scaled mass at any center. -/
theorem dyadicBochnerMass_le_total (M : PositiveBilinearMeasure X E) (n : ℕ)
    {R : ℝ} (hR : 0 < R) (i : ℕ) (x : X) (v : E) :
    ⟪v, dyadicBochnerMass M n x R i v⟫_ℝ ≤
      ((R / 2 ^ i) ^ 2 / (R / 2 ^ i) ^ n) * ‖M.massOperator univ‖ * ‖v‖ ^ 2 := by
  rw [dyadicBochnerMass_inner]
  have hb : (M.measure v).real (ball x (R / 2 ^ i)) ≤ (M.measure v).real univ :=
    measureReal_mono (subset_univ _) (measure_ne_top _ _)
  have hc : 0 ≤ (R / (2 : ℝ) ^ i) ^ 2 / (R / (2 : ℝ) ^ i) ^ n :=
    div_nonneg (sq_nonneg _) (pow_nonneg (div_pos hR (by positivity)).le _)
  exact (mul_le_mul_of_nonneg_left (hb.trans (bochner_total_mass_le M v)) hc).trans_eq (by ring)

/-- The finitely many omitted scales have a single finite background
constant, independent of the ball center. -/
theorem exists_uniform_mass_background (M : PositiveBilinearMeasure X E)
    (n : ℕ) {R : ℝ} (hR : 0 < R) (J : ℕ) :
    ∃ b : ℝ, 1 ≤ b ∧ ∀ x i v,
      ⟪v, dyadicBochnerEnvelope M n x R (J + i) v⟫_ℝ ≤
        b * (3 / 4 : ℝ) ^ i * ‖v‖ ^ 2 +
          ∑ j ∈ Finset.range (i + 1), (3 / 4 : ℝ) ^ (i - j) *
            ⟪v, dyadicBochnerMass M n x R (J + j) v⟫_ℝ := by
  let d := fun j => ((R / (2 : ℝ) ^ j) ^ 2 / (R / (2 : ℝ) ^ j) ^ n) * ‖M.massOperator univ‖
  have hd j : 0 ≤ d j := by dsimp only [d]; positivity
  let b := 1 + ∑ j ∈ Finset.range J, (3 / 4 : ℝ) ^ (J - j) * d j
  have hb : 1 ≤ b := by
    dsimp only [b]
    linarith [Finset.sum_nonneg (fun j (_ : j ∈ Finset.range J) =>
      mul_nonneg (by positivity : (0 : ℝ) ≤ (3 / 4) ^ (J - j)) (hd j))]
  refine ⟨b, hb, ?_⟩
  intro x i v
  rw [dyadicBochnerEnvelope_inner, geometric_envelope_shift]
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range J) =>
    mul_le_mul_of_nonneg_left (dyadicBochnerMass_le_total M n hR j x v)
      (by positivity : (0 : ℝ) ≤ (3 / 4) ^ (J - j)))
  change (∑ j ∈ Finset.range J, (3 / 4 : ℝ) ^ (J - j) *
    ⟪v, dyadicBochnerMass M n x R j v⟫_ℝ) ≤
      ∑ j ∈ Finset.range J, (3 / 4 : ℝ) ^ (J - j) * (d j * ‖v‖ ^ 2) at hsum
  simp only [← mul_assoc, ← Finset.sum_mul] at hsum
  have hfirst := mul_le_mul_of_nonneg_right
    (pow_le_one₀ (n := J) (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num)) (sq_nonneg ‖v‖)
  have hp : (3 / 4 : ℝ) ^ J * ‖v‖ ^ 2 +
      ∑ j ∈ Finset.range J, (3 / 4 : ℝ) ^ (J - j) *
        ⟪v, dyadicBochnerMass M n x R j v⟫_ℝ ≤ b * ‖v‖ ^ 2 := by
    dsimp only [b]
    nlinarith only [hsum, hfirst]
  have hscaled := mul_le_mul_of_nonneg_left hp (by positivity : (0 : ℝ) ≤ (3 / 4) ^ i)
  nlinarith only [hscaled]

end RegularPointCoordinates

end

end OAI
