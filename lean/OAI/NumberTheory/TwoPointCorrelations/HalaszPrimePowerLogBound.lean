import OAI.NumberTheory.TwoPointCorrelations.HalaszPositiveLog
import OAI.NumberTheory.TwoPointCorrelations.ThetaLogError
import Mathlib.NumberTheory.Chebyshev

namespace OAI

/-! A Chebyshev bound for the prime-power logarithmic kernel appearing in
the positive correction mean. Higher prime powers cost only an absolute
constant times the cutoff. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def halaszPrimePowerLogConstant : ℝ :=
  2 * Real.log 4 + 32 / Real.log 2

lemma halasz_log_sq_sqrt (x : ℝ) (hx : 1 ≤ x) :
    Real.sqrt x * Real.log x ^ 2 ≤ 8 * x := by
  have hs1 : 1 ≤ Real.sqrt x := (Real.le_sqrt (by norm_num) (by linarith)).mpr (by simpa using hx)
  have hh := log_sq_le_two_mul (Real.sqrt x) hs1
  rw [Real.log_sqrt (by linarith : 0 ≤ x)] at hh
  have hm := mul_le_mul_of_nonneg_left hh (Real.sqrt_nonneg x)
  nlinarith [Real.sq_sqrt (by linarith : 0 ≤ x)]

lemma halasz_prime_power_log_term (N n : ℕ) (hN : 1 ≤ N)
    (hn : n ∈ Icc 1 N) :
    halaszPrimePowerLog n ≤ (2 * Real.log N / Real.log 2) * ArithmeticFunction.vonMangoldt n := by
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hnpp : IsPrimePow n
  · have hn1 : n ≠ 1 := (ne_of_gt hnpp.one_lt)
    have hmin : 2 ≤ n.minFac := (Nat.minFac_prime hn1).two_le
    have hΛ : Real.log 2 ≤ ArithmeticFunction.vonMangoldt n := by
      rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left hnpp]
      exact Real.log_le_log (by norm_num) (by exact_mod_cast hmin)
    have hln : Real.log (n : ℝ) ≤ Real.log N :=
      Real.log_le_log (by exact_mod_cast (mem_Icc.mp hn).1) (by exact_mod_cast (mem_Icc.mp hn).2)
    rw [halaszPrimePowerLog, ite_eq_left hnpp]
    have hh := mul_le_mul_of_nonneg_left hΛ (show 0 ≤ 2 * Real.log N / Real.log 2 by positivity)
    have he : (2 * Real.log N / Real.log 2) * Real.log 2 = 2 * Real.log N := by field_simp
    rw [he] at hh
    linarith
  · rw [halaszPrimePowerLog, ite_eq_right hnpp]
    exact mul_nonneg (by positivity) ArithmeticFunction.vonMangoldt_nonneg

lemma halasz_prime_power_log_sum (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Icc 1 N, halaszPrimePowerLog n) ≤ halaszPrimePowerLogConstant * N := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNr
  have hset : Ioc 0 N = Icc 1 N := by ext n; simp only [mem_Ioc, mem_Icc]; omega
  have hsplit : (∑ n ∈ Icc 1 N, halaszPrimePowerLog n) ≤
      2 * Chebyshev.theta N + (2 * Real.log N / Real.log 2) *
        (Chebyshev.psi N - Chebyshev.theta N) := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Chebyshev.theta,
      Nat.floor_natCast, hset, mul_sum, mul_sum, sum_filter, sum_filter, ← sum_add_distrib]
    apply sum_le_sum
    intro n hn
    by_cases hp : n.Prime
    · simp [hp, halaszPrimePowerLog, hp.prime.isPrimePow]
    · simpa only [hp, not_false_eq_true, ite_false, ite_true, zero_add] using
        halasz_prime_power_log_term N n hN hn
  have htheta := Chebyshev.theta_le_log4_mul_x (x := (N : ℝ)) (by positivity)
  have htail := Chebyshev.psi_sub_theta_le hNr
  have hsq := halasz_log_sq_sqrt N hNr
  calc
    _ ≤ 2 * Chebyshev.theta N + (2 * Real.log N / Real.log 2) *
        (Chebyshev.psi N - Chebyshev.theta N) := hsplit
    _ ≤ 2 * (Real.log 4 * N) + (2 * Real.log N / Real.log 2) *
        (2 * Real.sqrt N * Real.log N) := by gcongr
    _ = 2 * (Real.log 4 * N) + (4 / Real.log 2) * (Real.sqrt N * Real.log N ^ 2) := by ring
    _ ≤ 2 * (Real.log 4 * N) + (4 / Real.log 2) * (8 * N) := by gcongr
    _ = _ := by unfold halaszPrimePowerLogConstant; ring

end TwoPointCorrelations

end OAI
