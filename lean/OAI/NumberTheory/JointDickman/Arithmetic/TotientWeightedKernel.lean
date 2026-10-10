import OAI.NumberTheory.JointDickman.Arithmetic.TotientDivisorBound
import OAI.NumberTheory.JointDickman.Arithmetic.DivisorSumReindex

namespace OAI

/-! # Replacing the totient weight by a divisor sum -/
namespace JointDickman
open Finset

theorem totient_weighted_sum_le_divisor_sum (F : ℕ → ℝ)
    (hF : ∀ n, 0 ≤ F n) (X : ℕ) :
    (∑ h ∈ Ioc 0 X, ((h:ℝ)/h.totient)*F h) ≤
      Real.exp 2 * ∑ d ∈ Ioc 0 X, (1/(d:ℝ)) * ∑ k ∈ Ioc 0 (X/d), F (d*k) := by
  have hpoint (h : ℕ) (hh : h ∈ Ioc 0 X) :
      ((h:ℝ)/h.totient)*F h ≤
        Real.exp 2 * ∑ d ∈ h.divisors, (1/(d:ℝ))*F (d*(h/d)) := by
    calc
      _ ≤ (Real.exp 2 * ∑ d ∈ h.divisors, 1/(d:ℝ))*F h :=
        mul_le_mul_of_nonneg_right (totient_ratio_le_divisor_reciprocals (mem_Ioc.mp hh).1) (hF h)
      _ = Real.exp 2 * ∑ d ∈ h.divisors, (1/(d:ℝ))*F (d*(h/d)) := by
        rw [mul_assoc,sum_mul]
        congr 1
        apply sum_congr rfl
        intro d hd
        rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
  calc
    _ ≤ ∑ h ∈ Ioc 0 X, Real.exp 2 * ∑ d ∈ h.divisors, (1/(d:ℝ))*F (d*(h/d)) :=
      sum_le_sum hpoint
    _ = Real.exp 2 * ∑ d ∈ Ioc 0 X, ∑ k ∈ Ioc 0 (X/d), (1/(d:ℝ))*F (d*k) := by
      rw [←mul_sum]
      exact congrArg (fun x : ℝ => Real.exp 2*x)
        (sum_Ioc_divisors_reindex (fun d k => (1/(d:ℝ))*F (d*k)) X)
    _ = _ := by simp only [mul_sum]

end JointDickman

end OAI
