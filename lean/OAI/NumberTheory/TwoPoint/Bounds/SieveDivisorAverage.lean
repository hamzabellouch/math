import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTPrimeSquareMean
import Mathlib.Analysis.PSeries

namespace OAI

/-! Averaging a nonnegative divisor sum by counting its multiples. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma sieve_divisors_filter {N n : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    n.divisors = (Icc 1 N).filter (fun d => d ∣ n) := by
  ext d
  constructor
  · intro hd
    obtain ⟨hdn, _⟩ := Nat.mem_divisors.mp hd
    exact mem_filter.mpr ⟨mem_Icc.mpr
      ⟨Nat.pos_of_mem_divisors hd, (Nat.le_of_dvd hn hdn).trans hnN⟩, hdn⟩
  · intro hd
    exact Nat.mem_divisors.mpr ⟨(mem_filter.mp hd).2, hn.ne'⟩

theorem sieve_divisor_sum_average (N : ℕ) (a : ℕ → ℝ)
    (ha : ∀ d, 0 ≤ a d) :
    (∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, a d) ≤
      (N : ℝ) * ∑ d ∈ Icc 1 N, a d / d := by
  calc
    _ = ∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, if d ∣ n then a d else 0 := by
      apply sum_congr rfl
      intro n hn
      rw [sieve_divisors_filter (mem_Icc.mp hn).1 (mem_Icc.mp hn).2, sum_filter]
    _ = ∑ d ∈ Icc 1 N, ∑ n ∈ Icc 1 N, if d ∣ n then a d else 0 := sum_comm
    _ = ∑ d ∈ Icc 1 N, a d * ((N / d : ℕ) : ℝ) := by
      apply sum_congr rfl
      intro d hd
      have hc := mrt_count_multiples (N := N) (mem_Icc.mp hd).1
      rw [show (∑ n ∈ Icc 1 N, if d ∣ n then a d else 0) =
          a d * (∑ n ∈ Icc 1 N, if d ∣ n then (1 : ℝ) else 0) by
        rw [mul_sum]
        apply sum_congr rfl
        intro n _
        split_ifs <;> simp]
      rw [hc]
    _ ≤ ∑ d ∈ Icc 1 N, a d * ((N : ℝ) / d) := by
      apply sum_le_sum
      intro d _
      exact mul_le_mul_of_nonneg_left Nat.cast_div_le (ha d)
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro d _
      ring

lemma sieve_inverse_sqrt_div {d : ℕ} (hd : 0 < d) :
    (1 / Real.sqrt (d : ℝ)) / d = (d : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  rw [div_div, Real.rpow_neg hdr.le, one_div, Real.sqrt_eq_rpow]
  congr 1
  calc
    (d : ℝ) ^ (1 / 2 : ℝ) * d = (d : ℝ) ^ (1 / 2 : ℝ) * (d : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
    _ = (d : ℝ) ^ (3 / 2 : ℝ) := by rw [← Real.rpow_add hdr]; norm_num

theorem sieve_inverse_sqrt_divisor_average (N : ℕ) :
    (∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, 1 / Real.sqrt (d : ℝ)) ≤
      (N : ℝ) * (∑' d : ℕ, (d : ℝ) ^ (-(3 / 2 : ℝ))) := by
  apply (sieve_divisor_sum_average N (fun d => 1 / Real.sqrt (d : ℝ)) (by intro d; positivity)).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
  calc
    _ = ∑ d ∈ Icc 1 N, (d : ℝ) ^ (-(3 / 2 : ℝ)) := by
      apply sum_congr rfl
      intro d hd
      exact sieve_inverse_sqrt_div (mem_Icc.mp hd).1
    _ ≤ _ := (Real.summable_nat_rpow.mpr (by norm_num : -(3 / 2 : ℝ) < -1)).sum_le_tsum _
      (fun d _ => Real.rpow_nonneg (Nat.cast_nonneg d) _)

end TwoPointCorrelations

end OAI
