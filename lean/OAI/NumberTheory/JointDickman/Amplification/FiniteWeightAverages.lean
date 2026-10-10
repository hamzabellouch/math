import OAI.NumberTheory.JointDickman.Arithmetic.FinitePrimeWeight

namespace OAI

/-! # Weighted prefix sums as finite sums of dilated unweighted sums -/
namespace JointDickman
open Finset Classical

theorem finitePrimeWeight_sum_expansion {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (t : ℕ → ℝ) (f : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, f n*(finitePrimeWeight P t n : ℂ)) =
      ∑ S ∈ P.powerset, ((∏ p ∈ S, (t p-1) : ℝ) : ℂ)*
        ∑ k ∈ Ioc 0 (N/(∏ p ∈ S,p)), f ((∏ p ∈ S,p)*k) := by
  calc
    _ = ∑ n ∈ Ioc 0 N, ∑ S ∈ P.powerset,
        ((∏ p ∈ S, (t p-1) : ℝ) : ℂ)*(if (∏ p ∈ S,p) ∣ n then f n else 0) := by
      apply sum_congr rfl
      intro n hn
      rw [finitePrimeWeight_expansion hP t (by have hh := (mem_Ioc.mp hn).1; omega)]
      simp only [Complex.ofReal_sum,Complex.ofReal_mul,mul_sum]
      apply sum_congr rfl
      intro S _
      by_cases hd : (∏ p ∈ S,p) ∣ n <;> simp [hd,mul_comm]
    _ = ∑ S ∈ P.powerset, ((∏ p ∈ S, (t p-1) : ℝ) : ℂ)*
        ∑ n ∈ Ioc 0 N, if (∏ p ∈ S,p) ∣ n then f n else 0 := by
      rw [sum_comm]
      simp only [mul_sum]
    _ = _ := by
      apply sum_congr rfl
      intro S hS
      rw [sum_divisible_Ioc f N _ (prod_pos (fun p hp => (hP p (mem_powerset.mp hS hp)).pos))]

end JointDickman

end OAI
