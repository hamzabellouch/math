import OAI.Geometry.RCD.Sobolev.DyadicBochnerMass

namespace OAI

/-! # Absorbing scalar remainders into the actual dyadic mass envelope -/

open Set Metric
open scoped BigOperators InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X E : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The geometric background retains every error decaying at least like 2⁻ⁱ. -/
theorem dyadic_half_background_le (M : PositiveBilinearMeasure X E) (n : ℕ)
    (x : X) {R : ℝ} (hR : 0 ≤ R) (i : ℕ) (v : E) :
    (1 / 2 : ℝ) ^ i * ‖v‖ ^ 2 ≤ ⟪v, dyadicBochnerEnvelope M n x R i v⟫_ℝ := by
  rw [dyadicBochnerEnvelope_inner]
  have hp : (1 / 2 : ℝ) ^ i ≤ (3 / 4 : ℝ) ^ i := pow_le_pow_left₀ (by norm_num) (by norm_num) i
  have hs : 0 ≤ ∑ j ∈ Finset.range (i + 1), (3 / 4 : ℝ) ^ (i - j) *
      ⟪v, dyadicBochnerMass M n x R j v⟫_ℝ := by
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (by positivity) ((dyadicBochnerMass_isPositive M n x hR j).inner_nonneg_right v)
  exact (mul_le_mul_of_nonneg_right hp (sq_nonneg ‖v‖)).trans (le_add_of_nonneg_right hs)

/-- All polynomial scalar terms needed in the source comparison are
controlled by the same geometric background. -/
theorem dyadic_scalar_background_bounds (M : PositiveBilinearMeasure X E) (n : ℕ)
    (x : X) {R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1) (i : ℕ) (v : E) :
    ((R / (2 : ℝ) ^ i) / R) * ‖v‖ ^ 2 ≤ ⟪v, dyadicBochnerEnvelope M n x R i v⟫_ℝ ∧
    (R / (2 : ℝ) ^ i) ^ 2 * ‖v‖ ^ 2 ≤ R ^ 2 * ⟪v, dyadicBochnerEnvelope M n x R i v⟫_ℝ ∧
    ((R / (2 : ℝ) ^ i) ^ 2 + (R / (2 : ℝ) ^ i) * R) * ‖v‖ ^ 2 ≤
      2 * R ^ 2 * ⟪v, dyadicBochnerEnvelope M n x R i v⟫_ℝ ∧
    ((R / (2 : ℝ) ^ i) ^ 2 + (R / (2 : ℝ) ^ i) * R ^ 2) * ‖v‖ ^ 2 ≤
      2 * R ^ 2 * ⟪v, dyadicBochnerEnvelope M n x R i v⟫_ℝ := by
  let r := R / (2 : ℝ) ^ i
  let F := ⟪v, dyadicBochnerEnvelope M n x R i v⟫_ℝ
  have hr : 0 < r := div_pos hR (by positivity)
  have hrR : r ≤ R := div_le_self hR.le (one_le_pow₀ (by norm_num))
  have hh := dyadic_half_background_le M n x hR.le i v
  have he : r / R = (1 / 2 : ℝ) ^ i := by
    dsimp only [r]
    rw [one_div_pow]
    field_simp
  have hfirst : (r / R) * ‖v‖ ^ 2 ≤ F := by simpa only [he, F] using hh
  have hrad : r * R * ‖v‖ ^ 2 ≤ R ^ 2 * F := by
    have h := mul_le_mul_of_nonneg_left hfirst (sq_nonneg R)
    have hid : R ^ 2 * ((r / R) * ‖v‖ ^ 2) = r * R * ‖v‖ ^ 2 := by field_simp
    rwa [hid] at h
  have hsquare : r ^ 2 * ‖v‖ ^ 2 ≤ r * R * ‖v‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (by nlinarith only [mul_le_mul_of_nonneg_left hrR hr.le]) (sq_nonneg ‖v‖)
  have hsmall : r * R ^ 2 * ‖v‖ ^ 2 ≤ r * R * ‖v‖ ^ 2 := by
    have hRsq : R ^ 2 ≤ R := by nlinarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRsq hr.le) (sq_nonneg ‖v‖)
  refine ⟨hfirst, hsquare.trans hrad, ?_, ?_⟩ <;> dsimp only [r, F] at * <;>
    nlinarith only [hrad, hsquare, hsmall]

end RegularPointCoordinates

end

end OAI
