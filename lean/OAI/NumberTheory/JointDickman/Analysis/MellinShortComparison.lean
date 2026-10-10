import OAI.NumberTheory.JointDickman.Counting.ComplexFiniteShortAverages

namespace OAI

/-! # Reciprocal weights in a short interval

Replacing the counting weight by `x/n` costs at most `(H+1)/x` in a
one-bounded short average. This is the elementary bridge to logarithmic
windows; the bound is uniform in the coefficients.
-/
namespace JointDickman
open Finset PublishedInputs

noncomputable def reciprocalShortAverage (f : ArithmeticFunction ℂ) (H x : ℝ) : ℂ :=
  (x : ℂ) * (∑ n ∈ Ioc ⌊x⌋₊ ⌊x + H⌋₊, f n / (n : ℂ)) / (H : ℂ)

theorem mellin_short_interval_card_le {x H : ℝ} (hx : 0 ≤ x) (hH : 0 ≤ H) :
    ((Ioc ⌊x⌋₊ ⌊x + H⌋₊).card : ℝ) ≤ H + 1 := by
  have hfloor : ⌊x⌋₊ ≤ ⌊x + H⌋₊ := Nat.floor_mono (by linarith)
  rw [Nat.card_Ioc, Nat.cast_sub hfloor]
  have hl := Nat.lt_floor_add_one x
  have hu := Nat.floor_le (show 0 ≤ x + H by linarith)
  have hl' : x < (⌊x⌋₊ : ℝ) + 1 := hl
  linarith

/-- The reciprocal-weight normalization has a vanishing error whenever
`H/x` and `1/x` tend to zero. -/
theorem short_average_reciprocal_error (f : ArithmeticFunction ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) {x H : ℝ} (hx : 0 < x) (hH : 0 < H) :
    ‖complexShortAverage f H x - reciprocalShortAverage f H x‖ ≤ (H + 1) / x := by
  let S := Ioc ⌊x⌋₊ ⌊x + H⌋₊
  have hn (n : ℕ) (hn : n ∈ S) : x < (n : ℝ) ∧ (n : ℝ) ≤ x + H := by
    obtain ⟨hl, hu⟩ := mem_Ioc.mp hn
    exact ⟨Nat.lt_of_floor_lt hl, (Nat.le_floor_iff (by linarith : 0 ≤ x + H)).mp hu⟩
  have hweight (n : ℕ) (hnS : n ∈ S) : |1 - x / (n : ℝ)| ≤ H / x := by
    have hn' := hn n hnS
    have hn0 : (0 : ℝ) < n := hx.trans hn'.1
    have hratio : x / (n : ℝ) ≤ 1 := (div_le_one hn0).mpr hn'.1.le
    rw [abs_of_nonneg (by linarith)]
    apply (le_div_iff₀ hx).mpr
    have hdiv := (div_mul_cancel₀ x hn0.ne')
    have hh : (1 - x / (n : ℝ)) * x ≤ H := by
      have hsmall : (1 - x / (n : ℝ)) * x ≤
          (1 - x / (n : ℝ)) * n :=
        mul_le_mul_of_nonneg_left hn'.1.le (by linarith)
      nlinarith
    exact hh
  have heq : complexShortAverage f H x - reciprocalShortAverage f H x =
      (∑ n ∈ S, ((1 - x / (n : ℝ) : ℝ) : ℂ) * f n) / (H : ℂ) := by
    unfold complexShortAverage reciprocalShortAverage
    rw [← sub_div, mul_sum, ← sum_sub_distrib]
    congr 1
    apply sum_congr rfl
    intro n _
    push_cast
    ring
  rw [heq, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hH]
  have hs : ‖∑ n ∈ S, ((1 - x / (n : ℝ) : ℝ) : ℂ) * f n‖ ≤
      (S.card : ℝ) * (H / x) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _n ∈ S, H / x := by
        apply sum_le_sum
        intro n hnS
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact (mul_le_mul (hweight n hnS) (hf n) (norm_nonneg _) (by positivity)).trans_eq
          (mul_one _)
      _ = _ := by simp
  calc
    _ ≤ ((S.card : ℝ) * (H / x)) / H :=
      div_le_div_of_nonneg_right hs hH.le
    _ = (S.card : ℝ) / x := by field_simp [hH.ne', hx.ne']
    _ ≤ (H + 1) / x := div_le_div_of_nonneg_right (mellin_short_interval_card_le hx.le hH.le) hx.le

end JointDickman

end OAI
