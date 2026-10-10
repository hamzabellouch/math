import OAI.NumberTheory.JointDickman.Arithmetic.PrimeCountChernoff
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

namespace OAI

/-! # Counting the few omitted primes above an addition prefix -/

namespace JointDickman
open Finset Classical

/-- The exponential generating function used for small omission sets. -/
theorem subset_count_exp_sum (P : Finset ℕ) (t : ℝ) :
    (∑ A ∈ P.powerset, Real.exp (-t*(A.card : ℝ))) = (1+Real.exp (-t))^P.card := by
  have hh := Finset.prod_add (s := P) (f := fun _ => Real.exp (-t)) (g := fun _ => (1 : ℝ))
  simp only [prod_const,one_pow,mul_one] at hh
  calc
    _ = ∑ A ∈ P.powerset, (Real.exp (-t))^A.card := by
      apply sum_congr rfl
      intro A _
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ = _ := by rw [← hh]; simp [add_comm]

/-- A real count threshold avoids floor errors in the regularity windows. -/
theorem subset_count_exp_bound (P : Finset ℕ) {t : ℝ} (ht : 0 ≤ t) (r : ℝ) :
    ((P.powerset.filter (fun A => (A.card : ℝ) ≤ r)).card : ℝ) ≤
      Real.exp (t*r)*(1+Real.exp (-t))^P.card := by
  let I := P.powerset.filter (fun A => (A.card : ℝ) ≤ r)
  have he : (I.card : ℝ)*Real.exp (-t*r) ≤ (1+Real.exp (-t))^P.card := by
    calc
      _ = ∑ _A ∈ I, Real.exp (-t*r) := by simp
      _ ≤ ∑ A ∈ I, Real.exp (-t*(A.card : ℝ)) := by
        apply sum_le_sum
        intro A hA
        exact Real.exp_le_exp.mpr (by nlinarith [(mem_filter.mp hA).2])
      _ ≤ ∑ A ∈ P.powerset, Real.exp (-t*(A.card : ℝ)) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)
      _ = _ := subset_count_exp_sum P t
  have hm := mul_le_mul_of_nonneg_left he (Real.exp_pos (t*r)).le
  have hc : Real.exp (t*r)*Real.exp (-t*r) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [mul_left_comm (Real.exp (t*r)) (I.card : ℝ),hc,mul_one] at hm
  exact hm

end JointDickman

end OAI
