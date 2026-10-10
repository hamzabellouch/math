import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter

namespace OrdinaryPrimeSupply
open Finset ArithmeticFunction
theorem prime_log_reciprocal_bound (N : ℕ) (hN : 0 < N) :
    ∑ p ∈ N.primesLE, Real.log p / p ≤ Real.log N + Real.log 4 := by
  have hdiv (n : ℕ) :
      ∑ p ∈ N.primesLE.filter (fun p => p ∣ n + 1), Real.log p ≤ Real.log (n + 1 : ℕ) := by
    calc
      _ = ∑ p ∈ N.primesLE.filter (fun p => p ∣ n + 1), vonMangoldt p := by
        apply sum_congr rfl
        intro p hp
        exact (vonMangoldt_apply_prime (Nat.prime_of_mem_primesLE (mem_filter.mp hp).1)).symm
      _ ≤ ∑ d ∈ (n + 1).divisors, vonMangoldt d := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro p hp
          exact Nat.mem_divisors.mpr ⟨(mem_filter.mp hp).2, by omega⟩
        · intro p _ _
          exact vonMangoldt_nonneg
      _ = _ := vonMangoldt_sum
  have hcount :
      ∑ p ∈ N.primesLE, ((N / p : ℕ) : ℝ) * Real.log p ≤ (N : ℝ) * Real.log N := by
    calc
      _ = ∑ p ∈ N.primesLE, ∑ n ∈ range N, if p ∣ n + 1 then Real.log p else 0 := by
        apply sum_congr rfl
        intro p hp
        rw [← sum_filter, sum_const, Nat.card_multiples, nsmul_eq_mul]
      _ = ∑ n ∈ range N, ∑ p ∈ N.primesLE.filter (fun p => p ∣ n + 1), Real.log p := by
        rw [sum_comm]
        simp only [sum_filter]
      _ ≤ ∑ n ∈ range N, Real.log (n + 1 : ℕ) := sum_le_sum (fun n _ => hdiv n)
      _ ≤ ∑ n ∈ range N, Real.log N := by
        apply sum_le_sum
        intro n hn
        apply Real.log_le_log (by positivity)
        exact_mod_cast (show n + 1 ≤ N by simpa using mem_range.mp hn)
      _ = _ := by simp
  have htheta : ∑ p ∈ N.primesLE, Real.log p ≤ Real.log 4 * N := by
    rw [← Chebyshev.theta_eq_sum_primesLE_log]
    exact Chebyshev.theta_le_log4_mul_x (by positivity)
  have hterm (p : ℕ) (hp : p ∈ N.primesLE) :
      (N : ℝ) * (Real.log p / p) ≤ (((N / p : ℕ) : ℝ) + 1) * Real.log p := by
    have pp := Nat.prime_of_mem_primesLE hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast pp.pos
    have hm : (N : ℝ) < (((N / p : ℕ) : ℝ) + 1) * p := by
      have hmod := Nat.mod_lt N pp.pos
      have hmoddiv := Nat.mod_add_div N p
      have hm' : N < (N / p + 1) * p := by nlinarith
      exact_mod_cast hm'
    have hb : (N : ℝ) / p ≤ ((N / p : ℕ) : ℝ) + 1 :=
      (div_le_iff₀ hp0).mpr hm.le
    have hh := mul_le_mul_of_nonneg_right hb (Real.log_natCast_nonneg p)
    nlinarith [show (N : ℝ) * (Real.log p / p) = ((N : ℝ) / p) * Real.log p by ring]
  have hh := sum_le_sum hterm
  rw [← mul_sum] at hh
  simp_rw [add_mul, one_mul] at hh
  rw [sum_add_distrib] at hh
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  nlinarith

end OrdinaryPrimeSupply

end

end OAI
