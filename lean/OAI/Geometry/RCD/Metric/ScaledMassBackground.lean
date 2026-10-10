import OAI.Geometry.RCD.Metric.UniformMassBackground

namespace OAI

/-! # A uniform coarse-mass background from a local scaled mass bound -/

open Set Metric MeasureTheory
open scoped InnerProductSpace BigOperators

noncomputable section
namespace RegularPointCoordinates

variable {X E : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Coarse masses use only the local measure, not arbitrary mass outside
its Bochner equation region. The physical scale cancels exactly. -/
theorem dyadicBochnerMass_le_scaled_local (M : PositiveBilinearMeasure X E)
    (n : ℕ) {p x : X} {R D : ℝ} (hR : 0 < R) (hx : x ∈ ball p R)
    (hlocal : ∀ v, ⟪v, M.massOperator (ball p (2 * R)) v⟫_ℝ ≤
      D * (R ^ n / R ^ 2) * ‖v‖ ^ 2) (i : ℕ) (v : E) :
    ⟪v, dyadicBochnerMass M n x R i v⟫_ℝ ≤
      (((2 : ℝ) ^ i) ^ n / ((2 : ℝ) ^ i) ^ 2 * D) * ‖v‖ ^ 2 := by
  have hs : R / (2 : ℝ) ^ i ≤ R := div_le_self hR.le (one_le_pow₀ (by norm_num))
  have hsub : ball x (R / (2 : ℝ) ^ i) ⊆ ball p (2 * R) := by
    intro y hy
    have hyx : dist y x < R / (2 : ℝ) ^ i := hy
    have hxp : dist x p < R := hx
    change dist y p < 2 * R
    linarith [dist_triangle y x p]
  have hm := measureReal_mono (μ := M.measure v) hsub (measure_ne_top _ _)
  rw [M.measure_real v _ measurableSet_ball, M.measure_real v _ measurableSet_ball] at hm
  rw [dyadicBochnerMass_inner, M.measure_real v _ measurableSet_ball]
  have hb := mul_le_mul_of_nonneg_left (hm.trans (hlocal v))
    (show 0 ≤ (R / (2 : ℝ) ^ i) ^ 2 / (R / (2 : ℝ) ^ i) ^ n by positivity)
  apply hb.trans_eq
  generalize ha : (2 : ℝ) ^ i = a
  have ha0 : a ≠ 0 := by rw [← ha]; positivity
  field_simp [hR.ne', ha0]
  have haInv : a ^ n * a⁻¹ ^ n = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ ha0, one_pow]
  calc
    _ = D * R ^ n * ‖v‖ ^ 2 * (a ^ n * a⁻¹ ^ n) := by rw [haInv]; ring
    _ = _ := by ring

/-- The finite omitted prefix is bounded before selecting the radius
or the actual harmonic measure, once its local scaled mass is bounded. -/
theorem exists_scaled_mass_background (n J : ℕ) {D : ℝ} (hD : 0 ≤ D) :
    ∃ b : ℝ, 1 ≤ b ∧ ∀ (R : ℝ), 0 < R → ∀ (p : X) (M : PositiveBilinearMeasure X E),
      (∀ v, ⟪v, M.massOperator (ball p (2 * R)) v⟫_ℝ ≤
        D * (R ^ n / R ^ 2) * ‖v‖ ^ 2) →
      ∀ x ∈ ball p R, ∀ i v,
      ⟪v, dyadicBochnerEnvelope M n x R (J + i) v⟫_ℝ ≤
        b * (3 / 4 : ℝ) ^ i * ‖v‖ ^ 2 +
          ∑ j ∈ Finset.range (i + 1), (3 / 4 : ℝ) ^ (i - j) *
            ⟪v, dyadicBochnerMass M n x R (J + j) v⟫_ℝ := by
  let d := fun j : ℕ => (((2 : ℝ) ^ j) ^ n / ((2 : ℝ) ^ j) ^ 2) * D
  have hd j : 0 ≤ d j := by dsimp only [d]; positivity
  let b := 1 + ∑ j ∈ Finset.range J, (3 / 4 : ℝ) ^ (J - j) * d j
  have hb : 1 ≤ b := by
    dsimp only [b]
    linarith [Finset.sum_nonneg (fun j (_ : j ∈ Finset.range J) =>
      mul_nonneg (by positivity : (0 : ℝ) ≤ (3 / 4) ^ (J - j)) (hd j))]
  refine ⟨b, hb, ?_⟩
  intro R hR p M hlocal x hx i v
  rw [dyadicBochnerEnvelope_inner, geometric_envelope_shift]
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range J) =>
    mul_le_mul_of_nonneg_left (dyadicBochnerMass_le_scaled_local M n hR hx hlocal j v)
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
