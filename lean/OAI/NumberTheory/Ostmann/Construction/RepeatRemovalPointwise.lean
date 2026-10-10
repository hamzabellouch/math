import Mathlib.Analysis.SpecialFunctions.Pow.Real
import OAI.NumberTheory.Ostmann.Supply.TernaryProductPolynomial

namespace OAI

/-! # A moment-sensitive bound for deleting repeated indices

A square-root shift gives a convenient alternative to the cycle expansion:
`|D_k-S^k| ≤ (|S|+sqrt(k*J))^k-|S|^k`. After normalization and Hölder,
this has the same vanishing relative error at the manuscript's scales.
-/

namespace Ostmann

open scoped BigOperators Classical

theorem recurrence_power_error (f c : ℕ → ℝ) (s b : ℝ) (k : ℕ)
    (hb : 0 ≤ b) (hzero : f 0 = 1) (hone : f 1 = s)
    (hrec : ∀ n, n + 2 ≤ k → f (n + 2) = s * f (n + 1) - c n * f n)
    (hc : ∀ n, n + 2 ≤ k → |c n| ≤ b ^ 2) :
    |f k - s ^ k| ≤ (|s| + b) ^ k - |s| ^ k := by
  have hq : 0 ≤ |s| + b := add_nonneg (abs_nonneg s) hb
  have hbound (n : ℕ) (h : |f n - s ^ n| ≤ (|s| + b) ^ n - |s| ^ n) :
      |f n| ≤ (|s| + b) ^ n := by
    calc
      |f n| = |(f n - s ^ n) + s ^ n| := by rw [sub_add_cancel]
      _ ≤ |f n - s ^ n| + |s ^ n| := abs_add_le _ _
      _ ≤ (|s| + b) ^ n := by rw [abs_pow]; linarith
  have hall : ∀ n, n ≤ k → |f n - s ^ n| ≤ (|s| + b) ^ n - |s| ^ n := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => intro _; simp [hzero]
    | one => intro _; simp only [hone, pow_one, sub_self, abs_zero]; linarith
    | more n ihn ihn1 =>
      intro hn
      have he0 := ihn (by omega)
      have he1 := ihn1 (by omega)
      have hf0 := hbound n he0
      have hid : f (n + 2) - s ^ (n + 2) =
          s * (f (n + 1) - s ^ (n + 1)) - c n * f n := by
        rw [hrec n hn, pow_succ]
        ring
      have hmul : b ^ 2 * (|s| + b) ^ n ≤ b * (|s| + b) ^ (n + 1) := by
        rw [pow_succ (|s| + b) n]
        have hh := mul_nonneg (abs_nonneg s) hb
        have hp := mul_nonneg hh (pow_nonneg hq n)
        nlinarith only [hp]
      calc
        |f (n + 2) - s ^ (n + 2)| =
            |s * (f (n + 1) - s ^ (n + 1)) - c n * f n| := congrArg abs hid
        _ ≤ |s| * |f (n + 1) - s ^ (n + 1)| + |c n| * |f n| := by
          simpa only [abs_mul] using abs_sub (s * (f (n + 1) - s ^ (n + 1))) (c n * f n)
        _ ≤ |s| * ((|s| + b) ^ (n + 1) - |s| ^ (n + 1)) +
            b ^ 2 * (|s| + b) ^ n := add_le_add
          (mul_le_mul_of_nonneg_left he1 (abs_nonneg s))
          (mul_le_mul (hc n hn) hf0 (abs_nonneg _) (sq_nonneg b))
        _ ≤ |s| * ((|s| + b) ^ (n + 1) - |s| ^ (n + 1)) +
            b * (|s| + b) ^ (n + 1) := add_le_add_right hmul _
        _ = (|s| + b) ^ (n + 2) - |s| ^ (n + 2) := by rw [pow_succ, pow_succ]; ring
  exact hall k le_rfl

theorem ternary_distinct_product_error {A : Type*} [Fintype A] [DecidableEq A]
    (y : A → ℝ) (hy : ∀ i, y i = 0 ∨ y i = 1 ∨ y i = -1)
    (k : ℕ) (hk : k ≤ Fintype.card A) :
    |(∑ e : Fin k ↪ A, ∏ i, y (e i)) - (∑ i, y i) ^ k| ≤
      (|(∑ i, y i)| + Real.sqrt ((k : ℝ) * Fintype.card A)) ^ k - |(∑ i, y i)| ^ k := by
  have hycube (i : A) : (y i) ^ 3 = y i := by
    rcases hy i with h | h | h <;> rw [h] <;> norm_num
  have hysq (i : A) : (y i) ^ 2 ≤ 1 := by
    rcases hy i with h | h | h <;> rw [h] <;> norm_num
  have hJ : (0 : ℝ) ≤ Fintype.card A := Nat.cast_nonneg _
  have hK : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hmass : (∑ i, (y i) ^ 2) ≤ (Fintype.card A : ℝ) := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using
      Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hysq i)
  have hmass0 : 0 ≤ ∑ i, (y i) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  rw [distinct_tuple_product_coeff]
  apply recurrence_power_error (fun n => ternaryDistinct Finset.univ y n)
    (fun n => (n + 1) * ((∑ i, (y i) ^ 2) - n)) (∑ i, y i)
    (Real.sqrt ((k : ℝ) * Fintype.card A)) k (Real.sqrt_nonneg _)
    (ternaryDistinct_zero _ _) (ternaryDistinct_one _ _)
  · intro n _
    exact ternaryDistinct_recurrence _ _ (fun i _ => hycube i) n
  · intro n hn
    have hnJ : (n : ℝ) ≤ Fintype.card A := by exact_mod_cast (show n ≤ Fintype.card A by omega)
    have hnK : (n : ℝ) + 1 ≤ k := by exact_mod_cast (show n + 1 ≤ k by omega)
    have hd : |(∑ i, (y i) ^ 2) - n| ≤ Fintype.card A := by
      rw [abs_le]
      constructor <;> linarith
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n + 1),
      Real.sq_sqrt (mul_nonneg hK hJ)]
    exact mul_le_mul hnK hd (abs_nonneg _) hK

theorem normalized_ternary_distinct_product_error {A : Type*} [Fintype A] [DecidableEq A]
    (y : A → ℝ) (hy : ∀ i, y i = 0 ∨ y i = 1 ∨ y i = -1)
    (k : ℕ) (hk : k ≤ Fintype.card A) (hA : 0 < Fintype.card A) :
    |(∑ e : Fin k ↪ A, ∏ i, y (e i)) / (Fintype.card A : ℝ) ^ k -
        ((∑ i, y i) / (Fintype.card A : ℝ)) ^ k| ≤
      (|((∑ i, y i) / (Fintype.card A : ℝ))| +
        Real.sqrt ((k : ℝ) * Fintype.card A) / Fintype.card A) ^ k -
      |((∑ i, y i) / (Fintype.card A : ℝ))| ^ k := by
  have hJ : (0 : ℝ) < Fintype.card A := by exact_mod_cast hA
  have h := div_le_div_of_nonneg_right (ternary_distinct_product_error y hy k hk)
    (pow_pos hJ k).le
  rw [div_pow, ← sub_div, abs_div, abs_of_pos (pow_pos hJ k)]
  apply h.trans_eq
  rw [sub_div, ← div_pow, ← div_pow, add_div, abs_div, abs_of_pos hJ]

end Ostmann

end OAI
