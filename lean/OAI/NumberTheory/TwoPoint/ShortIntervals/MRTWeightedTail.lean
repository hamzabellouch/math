import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTFactoredReciprocal
import Mathlib.Algebra.BigOperators.Module

namespace OAI

/-! Partial summation of the supported-divisor second moment. This keeps
the mixed Dirichlet coefficient square mass proportional to the inverse
lower endpoint, rather than losing the ratio of its endpoints. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma mrt_real_prefix_zero_extension (a : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ range (n + 1), if i = 0 then 0 else a i) = ∑ i ∈ Icc 1 n, a i := by
  rw [Nat.range_succ_eq_Icc_zero, ← add_sum_Ioc_eq_sum_Icc (Nat.zero_le n)]
  simp only [ite_true, zero_add]
  have he : Ioc 0 n = Icc 1 n := by ext i; simp only [mem_Ioc, mem_Icc]; omega
  rw [he]
  apply sum_congr rfl
  intro i hi
  rw [ite_eq_right (by have := (mem_Icc.mp hi).1; omega)]

lemma mrt_square_reciprocal_partial_sum (a : ℕ → ℝ) {m n : ℕ} (hmn : m < n) :
    (∑ i ∈ Ioc m n, a i / (i : ℝ) ^ 2) =
      (∑ i ∈ Icc 1 n, a i) / (n : ℝ) ^ 2 -
      (∑ i ∈ Icc 1 m, a i) / (m + 1 : ℕ) ^ 2 +
      ∑ i ∈ Ioc m (n - 1), (∑ j ∈ Icc 1 i, a j) *
        (1 / (i : ℝ) ^ 2 - 1 / (i + 1 : ℕ) ^ 2) := by
  have he := sum_Ioc_by_parts (fun i : ℕ => (1 : ℝ) / (i : ℝ) ^ 2)
    (fun i : ℕ => if i = 0 then 0 else a i) hmn
  simp only [smul_eq_mul, mrt_real_prefix_zero_extension] at he
  have hl : (∑ i ∈ Ioc m n, 1 / (i : ℝ) ^ 2 * (if i = 0 then 0 else a i)) =
      ∑ i ∈ Ioc m n, a i / (i : ℝ) ^ 2 := by
    apply sum_congr rfl
    intro i hi
    rw [ite_eq_right (by have := (mem_Ioc.mp hi).1; omega)]
    ring
  rw [hl] at he
  rw [he]
  have hs : (∑ i ∈ Ioc m (n - 1),
      (1 / (i + 1 : ℕ) ^ 2 - 1 / (i : ℝ) ^ 2) * (∑ j ∈ Icc 1 i, a j)) =
      -(∑ i ∈ Ioc m (n - 1), (∑ j ∈ Icc 1 i, a j) *
        (1 / (i : ℝ) ^ 2 - 1 / (i + 1 : ℕ) ^ 2)) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro i _
    ring
  rw [hs]
  ring

theorem mrt_weighted_square_tail (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i)
    {L U : ℕ} (hL : 0 < L) (hLU : L ≤ U) {C : ℝ} (hC : 0 ≤ C)
    (hprefix : ∀ n ≤ U, (∑ i ∈ Icc 1 n, a i) ≤ C * n) :
    (∑ i ∈ Ioc L U, a i / (i : ℝ) ^ 2) ≤ 2 * C / L := by
  by_cases heq : L = U
  · subst U
    simp only [Ioc_eq_empty_of_le le_rfl, sum_empty]
    positivity
  have hlt : L < U := lt_of_le_of_ne hLU heq
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hUR : (0 : ℝ) < U := by exact_mod_cast hL.trans_le hLU
  have hgap (i : ℕ) (hi : i ∈ Ioc L (U - 1)) :
      (∑ j ∈ Icc 1 i, a j) * (1 / (i : ℝ) ^ 2 - 1 / (i + 1 : ℕ) ^ 2) ≤
        2 * C * (1 / (i : ℝ) - 1 / (i + 1 : ℕ)) := by
    have hi0 : (0 : ℝ) < i := by exact_mod_cast hL.trans (mem_Ioc.mp hi).1
    have hiU : i ≤ U := (mem_Ioc.mp hi).2.trans (Nat.sub_le _ _)
    have hnon : 0 ≤ 1 / (i : ℝ) ^ 2 - 1 / (i + 1 : ℕ) ^ 2 := by
      apply sub_nonneg.mpr
      apply one_div_le_one_div_of_le (by positivity)
      push_cast
      nlinarith
    calc
      _ ≤ (C * i) * (1 / (i : ℝ) ^ 2 - 1 / (i + 1 : ℕ) ^ 2) :=
        mul_le_mul_of_nonneg_right (hprefix i hiU) hnon
      _ ≤ _ := by
        have hg : (i : ℝ) * (1 / (i : ℝ) ^ 2 - 1 / (i + 1 : ℕ) ^ 2) ≤
            2 * (1 / (i : ℝ) - 1 / (i + 1 : ℕ)) := by
          push_cast
          field_simp
          nlinarith
        nlinarith
  have htel : (∑ i ∈ Ioc L (U - 1), (1 / (i : ℝ) - 1 / (i + 1 : ℕ))) =
      1 / (L + 1 : ℕ) - 1 / (U : ℝ) := by
    have hset : Ioc L (U - 1) = Ico (L + 1) U := by
      ext i
      simp only [mem_Ioc, mem_Ico]
      omega
    rw [hset]
    calc
      _ = -(∑ i ∈ Ico (L + 1) U, (1 / (i + 1 : ℕ) - 1 / (i : ℝ))) := by
        rw [← sum_neg_distrib]
        apply sum_congr rfl
        intro i _
        ring
      _ = _ := by
        rw [sum_Ico_sub (fun i : ℕ => (1 : ℝ) / i) (show L + 1 ≤ U by omega)]
        ring
  rw [mrt_square_reciprocal_partial_sum a hlt]
  have htop : (∑ i ∈ Icc 1 U, a i) / (U : ℝ) ^ 2 ≤ C / U := by
    apply (div_le_div_of_nonneg_right (hprefix U le_rfl) (sq_nonneg _)).trans_eq
    field_simp
  have hbot : 0 ≤ (∑ i ∈ Icc 1 L, a i) / (L + 1 : ℕ) ^ 2 :=
    div_nonneg (sum_nonneg (fun i _ => ha i)) (sq_nonneg _)
  have hsum := sum_le_sum hgap
  rw [← mul_sum, htel] at hsum
  have hn : 0 ≤ C / (U : ℝ) := div_nonneg hC hUR.le
  calc
    _ ≤ C / U + 2 * C * (1 / (L + 1 : ℕ) - 1 / (U : ℝ)) := by linarith
    _ = 2 * C / (L + 1 : ℕ) - C / U := by ring
    _ ≤ 2 * C / (L + 1 : ℕ) := sub_le_self _ hn
    _ ≤ 2 * C / L := div_le_div_of_nonneg_left (by positivity) hLR
      (by exact_mod_cast Nat.le_add_right L 1)

end TwoPointCorrelations

end OAI
