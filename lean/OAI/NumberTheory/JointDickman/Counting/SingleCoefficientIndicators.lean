import OAI.NumberTheory.JointDickman.Counting.SingleCoefficientTilt
import OAI.NumberTheory.JointDickman.Amplification.TailViolationSum

namespace OAI

/-! # The actual regularity events for one coefficient -/

namespace JointDickman

open Finset

private theorem indicator_le_of_imp {P Q : Prop} [Decidable P] [Decidable Q] {w : ℝ}
    (hw : 0 ≤ w) (h : P → Q) : (if P then w else 0) ≤ if Q then w else 0 := by
  split_ifs with hp hq hq
  · rfl
  · exact False.elim (hq (h hp))
  · exact hw
  · rfl

open Classical in
theorem single_prefix_upper_indicator {B n : ℕ} (g τ s : ℝ) (hs : 0 < s) :
    (if (g / 2 + τ) * auxiliaryLogLength B < ((primePrefix B g (coefficientPrimeSet B n)).card : ℝ)
      then coefficientWeight B n else 0) ≤
    if s * ((g / 2 + τ) * auxiliaryLogLength B) ≤
      s * primeDivisorCount (primePrefix B g (auxiliaryPrimes B)) n then coefficientWeight B n else 0 := by
  by_cases hn : n = 0
  · simp only [hn, coefficientWeight_zero, ite_self, le_refl]
  · apply indicator_le_of_imp (coefficientWeight_nonneg B n)
    intro h
    rw [← coefficient_prefix_count (B := B) hn g]
    exact mul_le_mul_of_nonneg_left h.le hs.le

open Classical in
theorem single_prefix_lower_indicator {B n : ℕ} (g τ s : ℝ) (hs : 0 < s) :
    (if ((primePrefix B g (coefficientPrimeSet B n)).card : ℝ) < (g / 2 - τ) * auxiliaryLogLength B
      then coefficientWeight B n else 0) ≤
    if (-s) * ((g / 2 - τ) * auxiliaryLogLength B) ≤
      (-s) * primeDivisorCount (primePrefix B g (auxiliaryPrimes B)) n then coefficientWeight B n else 0 := by
  by_cases hn : n = 0
  · simp only [hn, coefficientWeight_zero, ite_self, le_refl]
  · apply indicator_le_of_imp (coefficientWeight_nonneg B n)
    intro h
    rw [← coefficient_prefix_count (B := B) hn g]
    exact mul_le_mul_of_nonpos_left h.le (by linarith only [hs])

open Classical in
theorem single_tail_indicator {B n i : ℕ} (C : ℝ) :
    (if (((coefficientPrimeSet B n).filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)).card : ℝ) <
      (2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C then coefficientWeight B n else 0) ≤
    if (-(1 / 10 : ℝ)) * ((2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C) ≤
      (-(1 / 10 : ℝ)) * primeDivisorCount
        ((auxiliaryPrimes B).filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)) n
      then coefficientWeight B n else 0 := by
  by_cases hn : n = 0
  · simp only [hn, coefficientWeight_zero, ite_self, le_refl]
  · apply indicator_le_of_imp (coefficientWeight_nonneg B n)
    intro h
    rw [← coefficient_tail_count (B := B) hn (primeTailEndpoint B i)]
    exact mul_le_mul_of_nonpos_left h.le (by norm_num)

end JointDickman

end OAI
