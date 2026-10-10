import OAI.NumberTheory.TwoPointCorrelations.HalaszSmoothSeries
import Mathlib.Algebra.BigOperators.Intervals

namespace OAI

/-! Unsmoothing the triple convolution by a finite difference. Only the
coefficients in the short boundary interval contribute to the error. -/

namespace TwoPointCorrelations

open Finset Complex

noncomputable def halaszTriangularSum (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, a n * ((1 - (n : ℝ) / x : ℝ) : ℂ)

lemma halasz_triangle_scale (a : ℕ → ℂ) {x : ℝ} (hx : x ≠ 0) :
    (x : ℂ) * halaszTriangularSum a x =
      ∑ n ∈ Icc 1 ⌊x⌋₊, a n * ((x - (n : ℝ) : ℝ) : ℂ) := by
  rw [halaszTriangularSum, mul_sum]
  apply sum_congr rfl
  intro n _
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
  push_cast
  field_simp

lemma halasz_triangle_difference (a : ℕ → ℂ) {x : ℝ} (hx : 0 < x) (m : ℕ) :
    (((x + m : ℝ) : ℂ) * halaszTriangularSum a (x + m) -
      (x : ℂ) * halaszTriangularSum a x) =
      (m : ℂ) * (∑ n ∈ Icc 1 ⌊x⌋₊, a n) +
        ∑ n ∈ Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m), a n * ((x + m - (n : ℝ) : ℝ) : ℂ) := by
  rw [halasz_triangle_scale a (by positivity), halasz_triangle_scale a hx.ne',
    Nat.floor_add_natCast hx.le]
  have hsplit (f : ℕ → ℂ) :
      (∑ n ∈ Icc 1 (⌊x⌋₊ + m), f n) =
      (∑ n ∈ Icc 1 ⌊x⌋₊, f n) + ∑ n ∈ Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m), f n := by
    simpa only [Ico_add_one_right_eq_Icc] using
      (sum_Ico_consecutive f (by omega : 1 ≤ ⌊x⌋₊ + 1)
        (by omega : ⌊x⌋₊ + 1 ≤ (⌊x⌋₊ + m) + 1)).symm
  rw [hsplit]
  have he : (∑ n ∈ Icc 1 ⌊x⌋₊, a n * ((x + m - (n : ℝ) : ℝ) : ℂ)) -
      (∑ n ∈ Icc 1 ⌊x⌋₊, a n * ((x - (n : ℝ) : ℝ) : ℂ)) =
      (m : ℂ) * ∑ n ∈ Icc 1 ⌊x⌋₊, a n := by
    rw [← sum_sub_distrib, mul_sum]
    apply sum_congr rfl
    intro n _
    push_cast
    ring
  linear_combination he

lemma halasz_triangle_remainder (a : ℕ → ℂ) {x B : ℝ} (hx : 0 < x) (m : ℕ)
    (hB : ∀ n ∈ Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m), ‖a n‖ ≤ B) :
    ‖∑ n ∈ Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m), a n * ((x + m - (n : ℝ) : ℝ) : ℂ)‖ ≤
      B * (m : ℝ) ^ 2 := by
  have hp (n : ℕ) (hn : n ∈ Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m)) :
      ‖a n * ((x + m - (n : ℝ) : ℝ) : ℂ)‖ ≤ B * m := by
    obtain ⟨hnlo, hnhi⟩ := mem_Icc.mp hn
    have hnx : x < (n : ℝ) := (Nat.lt_floor_add_one x).trans_le (by exact_mod_cast hnlo)
    have hny : (n : ℝ) ≤ x + m := by
      have hf := Nat.floor_le hx.le
      have hn' : (n : ℝ) ≤ (⌊x⌋₊ : ℝ) + m := by exact_mod_cast hnhi
      linarith
    have hw0 : 0 ≤ x + m - (n : ℝ) := by linarith
    have hwm : x + m - (n : ℝ) ≤ (m : ℝ) := by linarith
    have hBn := hB n (mem_Icc.mpr ⟨hnlo, hnhi⟩)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]
    exact mul_le_mul hBn hwm hw0 ((norm_nonneg _).trans hBn)
  have hc : #(Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m)) = m := by rw [Nat.card_Icc]; omega
  calc
    _ ≤ ∑ n ∈ Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m),
        ‖a n * ((x + m - (n : ℝ) : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m), B * m := sum_le_sum hp
    _ = _ := by rw [sum_const, hc, nsmul_eq_mul]; ring

theorem halasz_unsmoothing_error (a : ℕ → ℂ) {x B : ℝ} (hx : 0 < x)
    (m : ℕ) (hm : 0 < m)
    (hB : ∀ n ∈ Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m), ‖a n‖ ≤ B) :
    ‖(((x + m : ℝ) : ℂ) * halaszTriangularSum a (x + m) -
        (x : ℂ) * halaszTriangularSum a x) / (m : ℂ) -
      ∑ n ∈ Icc 1 ⌊x⌋₊, a n‖ ≤ B * m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  rw [halasz_triangle_difference a hx m, add_div, mul_div_cancel_left₀ _ hmC,
    add_sub_cancel_left, norm_div, Complex.norm_natCast]
  exact (div_le_div_of_nonneg_right (halasz_triangle_remainder a hx m hB) hmR.le).trans_eq
    (by field_simp)

end TwoPointCorrelations

end OAI
