import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic

namespace OAI

namespace SiegelZeros

section

open Finset
open scoped BigOperators

namespace Result.W54

theorem sum_log_eq_log_factorial (n : ℕ) :
    (∑ d ∈ Ioc 0 n, Real.log (d : ℝ)) = Real.log (n.factorial : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_Ioc_succ_top (Nat.zero_le n), ih, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity)]
    ring

theorem log_factorial_eq_sum_vonMangoldt_mul_div (n : ℕ) :
    Real.log (n.factorial : ℝ) =
      ∑ d ∈ Ioc 0 n, ArithmeticFunction.vonMangoldt d * (n / d : ℕ) := by
  rw [← sum_log_eq_log_factorial]
  simpa using ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum ArithmeticFunction.vonMangoldt n

theorem log_factorial_le_mul_vonMangoldt_mass (n : ℕ) :
    Real.log (n.factorial : ℝ) ≤
      (n : ℝ) * ∑ d ∈ Ioc 0 n, ArithmeticFunction.vonMangoldt d / d := by
  rw [log_factorial_eq_sum_vonMangoldt_mul_div, mul_sum]
  refine sum_le_sum fun d hd => ?_
  calc
    ArithmeticFunction.vonMangoldt d * (n / d : ℕ) ≤
        ArithmeticFunction.vonMangoldt d * ((n : ℝ) / d) :=
      mul_le_mul_of_nonneg_left Nat.cast_div_le ArithmeticFunction.vonMangoldt_nonneg
    _ = (n : ℝ) * (ArithmeticFunction.vonMangoldt d / d) := by ring

theorem sum_vonMangoldt_div_lower {n : ℕ} (hn : 1 ≤ n) :
    Real.log (n : ℝ) - 1 ≤
      ∑ d ∈ Ioc 0 n, ArithmeticFunction.vonMangoldt d / d := by
  have hn0 : n ≠ 0 := by omega
  have hnr : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero hn0)
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hpi : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.two_le_pi])
  have hst := Stirling.le_log_factorial_stirling hn0
  have hmass := log_factorial_le_mul_vonMangoldt_mass n
  apply (mul_le_mul_iff_right₀ hnr).mp
  nlinarith

end Result.W54

end

end SiegelZeros

end OAI
