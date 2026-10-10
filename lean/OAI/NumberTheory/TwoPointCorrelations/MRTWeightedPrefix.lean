import OAI.NumberTheory.TwoPointCorrelations.MRTCountMean
import Mathlib.Algebra.BigOperators.Module

namespace OAI

/-! Finite partial summation from ordinary prefix cancellation to a
normalized Dirichlet polynomial on a bounded-ratio interval. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma mrt_range_zero_extension (F : ℕ → ℂ) (n : ℕ) :
    (∑ i ∈ range (n + 1), if i = 0 then 0 else F i) = ∑ i ∈ Icc 1 n, F i := by
  rw [Nat.range_succ_eq_Icc_zero,
    ← add_sum_Ioc_eq_sum_Icc (Nat.zero_le n)]
  simp only [ite_true, zero_add]
  have he : Ioc 0 n = Icc 1 n := by ext i; simp only [mem_Ioc, mem_Icc]; omega
  rw [he]
  apply sum_congr rfl
  intro i hi
  rw [ite_eq_right (by have := (mem_Icc.mp hi).1; omega)]

lemma mrt_reciprocal_summation_by_parts (F : ℕ → ℂ) {m n : ℕ} (hmn : m < n) :
    (∑ i ∈ Ioc m n, F i / (i : ℂ)) =
      ((1 / (n : ℝ) : ℝ) : ℂ) * (∑ i ∈ Icc 1 n, F i) -
      ((1 / (m + 1 : ℕ) : ℝ) : ℂ) * (∑ i ∈ Icc 1 m, F i) -
      ∑ i ∈ Ioc m (n - 1),
        (((1 / (i + 1 : ℕ) : ℝ) : ℂ) - ((1 / (i : ℝ) : ℝ) : ℂ)) *
          (∑ j ∈ Icc 1 i, F j) := by
  have he := sum_Ioc_by_parts
    (fun i : ℕ => ((1 / (i : ℝ) : ℝ) : ℂ))
    (fun i : ℕ => if i = 0 then (0 : ℂ) else F i) hmn
  simp only [smul_eq_mul, mrt_range_zero_extension] at he
  convert he using 1
  apply sum_congr rfl
  intro i hi
  have hi0 : i ≠ 0 := by have := (mem_Ioc.mp hi).1; omega
  simp only [ite_eq_right hi0, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_natCast]
  ring

lemma mrt_reciprocal_gap {i : ℕ} (hi : 0 < i) :
    |1 / ((i + 1 : ℕ) : ℝ) - 1 / (i : ℝ)| * i =
      1 / ((i + 1 : ℕ) : ℝ) := by
  have hiR : (0 : ℝ) < i := by exact_mod_cast hi
  have hle : 1 / ((i + 1 : ℕ) : ℝ) ≤ 1 / (i : ℝ) :=
    one_div_le_one_div_of_le hiR (by norm_num)
  rw [abs_of_nonpos (sub_nonpos.mpr hle)]
  push_cast
  field_simp
  ring

/-- A prefix bound on the same scale controls the normalized polynomial
on every interval of ratio at most three. -/
theorem mrt_weighted_prefix_bound (F : ℕ → ℂ) {m n : ℕ}
    (hm : 0 < m) (hmn : m ≤ n) (hn3 : n ≤ 3 * m)
    {A : ℝ} (hA : 0 ≤ A)
    (hF : ∀ k ∈ Icc m n, ‖∑ i ∈ Icc 1 k, F i‖ ≤ A * k) :
    ‖∑ i ∈ Ioc m n, F i / (i : ℂ)‖ ≤ 5 * A := by
  by_cases he : m = n
  · subst n
    simp only [Ioc_eq_empty_of_le le_rfl, sum_empty, norm_zero]
    positivity
  have hmn' : m < n := lt_of_le_of_ne hmn he
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < n := by exact_mod_cast (hm.trans_le hmn)
  have htop : ‖((1 / (n : ℝ) : ℝ) : ℂ) * (∑ i ∈ Icc 1 n, F i)‖ ≤ A := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc
      _ ≤ (1 / (n : ℝ)) * (A * n) :=
        mul_le_mul_of_nonneg_left (hF n (mem_Icc.mpr ⟨hmn, le_rfl⟩)) (by positivity)
      _ = _ := by field_simp
  have hbot : ‖((1 / (m + 1 : ℕ) : ℝ) : ℂ) * (∑ i ∈ Icc 1 m, F i)‖ ≤ A := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc
      _ ≤ (1 / ((m + 1 : ℕ) : ℝ)) * (A * m) :=
        mul_le_mul_of_nonneg_left (hF m (mem_Icc.mpr ⟨le_rfl, hmn⟩)) (by positivity)
      _ ≤ A := by
        rw [one_div, inv_mul_eq_div]
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < (m + 1 : ℕ))).mpr
        push_cast
        nlinarith
  have hterm (i : ℕ) (hi : i ∈ Ioc m (n - 1)) :
      ‖(((1 / (i + 1 : ℕ) : ℝ) : ℂ) - ((1 / (i : ℝ) : ℝ) : ℂ)) *
        (∑ j ∈ Icc 1 i, F j)‖ ≤ A / (m : ℝ) := by
    have hi0 : 0 < i := hm.trans (mem_Ioc.mp hi).1
    have hin : i ≤ n := (mem_Ioc.mp hi).2.trans (Nat.sub_le _ _)
    rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ |1 / ((i + 1 : ℕ) : ℝ) - 1 / (i : ℝ)| * (A * i) :=
        mul_le_mul_of_nonneg_left (hF i (mem_Icc.mpr ⟨(mem_Ioc.mp hi).1.le, hin⟩))
          (abs_nonneg _)
      _ = A * (1 / ((i + 1 : ℕ) : ℝ)) := by
        rw [mul_left_comm, mrt_reciprocal_gap hi0]
      _ ≤ A * (1 / (m : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hA
        apply one_div_le_one_div_of_le hmR
        exact_mod_cast (show m ≤ i + 1 by have := (mem_Ioc.mp hi).1; omega)
      _ = _ := by ring
  have hsum : ‖∑ i ∈ Ioc m (n - 1),
      (((1 / (i + 1 : ℕ) : ℝ) : ℂ) - ((1 / (i : ℝ) : ℝ) : ℂ)) *
        (∑ j ∈ Icc 1 i, F j)‖ ≤ 3 * A := by
    calc
      _ ≤ ∑ i ∈ Ioc m (n - 1), A / (m : ℝ) :=
        (norm_sum_le _ _).trans (sum_le_sum hterm)
      _ = ((Ioc m (n - 1)).card : ℝ) * (A / (m : ℝ)) := by simp
      _ ≤ (n : ℝ) * (A / (m : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (div_nonneg hA hmR.le)
        exact_mod_cast (show (Ioc m (n - 1)).card ≤ n by rw [Nat.card_Ioc]; omega)
      _ ≤ (3 * (m : ℝ)) * (A / (m : ℝ)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hn3) (div_nonneg hA hmR.le)
      _ = _ := by field_simp
  rw [mrt_reciprocal_summation_by_parts F hmn']
  apply (norm_sub_le _ _).trans
  calc
    _ ≤ (A + A) + 3 * A :=
      add_le_add ((norm_sub_le _ _).trans (add_le_add htop hbot)) hsum
    _ = 5 * A := by ring

end TwoPointCorrelations

end OAI
