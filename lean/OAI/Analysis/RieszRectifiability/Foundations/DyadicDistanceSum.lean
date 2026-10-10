import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.PlaneDistanceTransfer

namespace OAI

namespace RieszRectifiability

noncomputable section

open scoped BigOperators

theorem geom_sum_le_pow_div (b : ℝ) (hb : 1 < b) (l : ℕ) :
    (∑ i ∈ Finset.range l, b ^ i) ≤ b ^ l / (b - 1) := by
  rw [geom_sum_eq (ne_of_gt hb) l]
  exact div_le_div_of_nonneg_right (by linarith) (sub_nonneg.mpr hb.le)

theorem dyadic_distance_error_sum_le (B δ b X : ℝ)
    (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hb : 1 < b) (hX : 0 ≤ X)
    (l : ℕ) (hXl : X ≤ (2 : ℝ) ^ l) :
    (∑ i ∈ Finset.range l, B * δ * (2 : ℝ) ^ i * b ^ i * (3 + X / (2 : ℝ) ^ i)) ≤
      B * δ * (2 : ℝ) ^ l * b ^ l * (3 / (2 * b - 1) + 1 / (b - 1)) := by
  have hterm : ∀ i : ℕ, B * δ * (2 : ℝ) ^ i * b ^ i * (3 + X / (2 : ℝ) ^ i) =
      B * δ * (3 * (2 * b) ^ i + X * b ^ i) := by
    intro i
    rw [mul_pow]
    field_simp
  have hsum : (∑ i ∈ Finset.range l, B * δ * (2 : ℝ) ^ i * b ^ i * (3 + X / (2 : ℝ) ^ i)) =
      B * δ * (3 * (∑ i ∈ Finset.range l, (2 * b) ^ i) +
        X * (∑ i ∈ Finset.range l, b ^ i)) := by
    simp only [hterm, Finset.mul_sum, Finset.sum_add_distrib, mul_add]
  have htwo : 1 < 2 * b := by linarith
  have hinner : 3 * (∑ i ∈ Finset.range l, (2 * b) ^ i) + X * (∑ i ∈ Finset.range l, b ^ i) ≤
      3 * ((2 * b) ^ l / (2 * b - 1)) + (2 : ℝ) ^ l * (b ^ l / (b - 1)) := by
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left (geom_sum_le_pow_div (2 * b) htwo l) (by norm_num)
    · exact (mul_le_mul_of_nonneg_left (geom_sum_le_pow_div b hb l) hX).trans
        (mul_le_mul_of_nonneg_right hXl (div_nonneg (pow_nonneg (by linarith) l)
          (sub_nonneg.mpr hb.le)))
  rw [hsum]
  calc
    _ ≤ B * δ * (3 * ((2 * b) ^ l / (2 * b - 1)) + (2 : ℝ) ^ l * (b ^ l / (b - 1))) :=
      mul_le_mul_of_nonneg_left hinner (mul_nonneg hB hδ)
    _ = _ := by rw [mul_pow]; ring

theorem dyadic_distance_chain_bound (d : ℕ → ℝ) (B δ b X : ℝ)
    (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hb : 1 < b) (hX : 0 ≤ X)
    (l : ℕ) (hXl : X ≤ (2 : ℝ) ^ l)
    (hstep : ∀ i < l, d i ≤ d (i + 1) +
      B * δ * (2 : ℝ) ^ i * b ^ i * (3 + X / (2 : ℝ) ^ i)) :
    d 0 ≤ d l + B * δ * (2 : ℝ) ^ l * b ^ l * (3 / (2 * b - 1) + 1 / (b - 1)) := by
  exact (upper_bound_by_last_and_step_sum d
    (fun i => B * δ * (2 : ℝ) ^ i * b ^ i * (3 + X / (2 : ℝ) ^ i)) l hstep).trans
      (add_le_add le_rfl (dyadic_distance_error_sum_le B δ b X hB hδ hb hX l hXl))

end

end RieszRectifiability

end OAI
