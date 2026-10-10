import OAI.NumberTheory.JointDickman.Amplification.WeightedCountTail
import OAI.NumberTheory.JointDickman.Amplification.RegularityUnionBound

namespace OAI

/-! # Comparing regularity violations with the signed count events -/

namespace JointDickman

open Finset

def coefficientForm (k : Fin 3) (j b c : ℕ) : ℕ := ![b, c, b + j * c] k

theorem tripleCoefficientWeight_nonneg (B j b c : ℕ) : 0 ≤ tripleCoefficientWeight B j b c :=
  mul_nonneg (mul_nonneg (coefficientWeight_nonneg _ _) (coefficientWeight_nonneg _ _)) (coefficientWeight_nonneg _ _)

theorem tripleCoefficientWeight_eq_zero {k : Fin 3} {B j b c : ℕ}
    (h : coefficientForm k j b c = 0) : tripleCoefficientWeight B j b c = 0 := by
  fin_cases k <;> simp [coefficientForm] at h <;> simp [tripleCoefficientWeight, h]

open Classical in
theorem prefix_upper_indicator_le {B j b c : ℕ} (k : Fin 3) (g τ s : ℝ) (hs : 0 < s) :
    (if (g / 2 + τ) * auxiliaryLogLength B <
      ((primePrefix B g (coefficientPrimeSet B (coefficientForm k j b c))).card : ℝ)
      then tripleCoefficientWeight B j b c else 0) ≤
    (if s * ((g / 2 + τ) * auxiliaryLogLength B) ≤
      s * triplePrimeCount k (primePrefix B g (auxiliaryPrimes B)) j b c
      then tripleCoefficientWeight B j b c else 0) := by
  by_cases hn : coefficientForm k j b c = 0
  · simp only [tripleCoefficientWeight_eq_zero hn, ite_self, le_refl]
  · have hcount := coefficient_prefix_count (B := B) hn g
    by_cases hbad : (g / 2 + τ) * auxiliaryLogLength B <
        ((primePrefix B g (coefficientPrimeSet B (coefficientForm k j b c))).card : ℝ)
    · have hm : s * ((g / 2 + τ) * auxiliaryLogLength B) ≤
          s * triplePrimeCount k (primePrefix B g (auxiliaryPrimes B)) j b c := by
        change _ ≤ s * (primeDivisorCount (primePrefix B g (auxiliaryPrimes B)) (coefficientForm k j b c) : ℝ)
        rw [← hcount]
        exact mul_le_mul_of_nonneg_left hbad.le hs.le
      simp only [ite_eq_left hbad, ite_eq_left hm, le_refl]
    · rw [ite_eq_right hbad]
      split_ifs
      · exact tripleCoefficientWeight_nonneg _ _ _ _
      · rfl

open Classical in
theorem prefix_lower_indicator_le {B j b c : ℕ} (k : Fin 3) (g τ s : ℝ) (hs : 0 < s) :
    (if ((primePrefix B g (coefficientPrimeSet B (coefficientForm k j b c))).card : ℝ) <
      (g / 2 - τ) * auxiliaryLogLength B then tripleCoefficientWeight B j b c else 0) ≤
    (if (-s) * ((g / 2 - τ) * auxiliaryLogLength B) ≤
      (-s) * triplePrimeCount k (primePrefix B g (auxiliaryPrimes B)) j b c
      then tripleCoefficientWeight B j b c else 0) := by
  by_cases hn : coefficientForm k j b c = 0
  · simp only [tripleCoefficientWeight_eq_zero hn, ite_self, le_refl]
  · have hcount := coefficient_prefix_count (B := B) hn g
    by_cases hbad : ((primePrefix B g (coefficientPrimeSet B (coefficientForm k j b c))).card : ℝ) <
        (g / 2 - τ) * auxiliaryLogLength B
    · have hm : (-s) * ((g / 2 - τ) * auxiliaryLogLength B) ≤
          (-s) * triplePrimeCount k (primePrefix B g (auxiliaryPrimes B)) j b c := by
        change _ ≤ (-s) * (primeDivisorCount (primePrefix B g (auxiliaryPrimes B)) (coefficientForm k j b c) : ℝ)
        rw [← hcount]
        exact mul_le_mul_of_nonpos_left hbad.le (by linarith)
      simp only [ite_eq_left hbad, ite_eq_left hm, le_refl]
    · rw [ite_eq_right hbad]
      split_ifs
      · exact tripleCoefficientWeight_nonneg _ _ _ _
      · rfl

open Classical in
theorem tail_indicator_le {B j b c i : ℕ} (k : Fin 3) (C : ℝ) :
    (if (((coefficientPrimeSet B (coefficientForm k j b c)).filter
        (fun p : ℕ => primeTailEndpoint B i < Real.log p)).card : ℝ) <
      (2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C
      then tripleCoefficientWeight B j b c else 0) ≤
    (if (-(1 / 10 : ℝ)) * ((2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C) ≤
      (-(1 / 10 : ℝ)) * triplePrimeCount k
        ((auxiliaryPrimes B).filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)) j b c
      then tripleCoefficientWeight B j b c else 0) := by
  by_cases hn : coefficientForm k j b c = 0
  · simp only [tripleCoefficientWeight_eq_zero hn, ite_self, le_refl]
  · have hcount := coefficient_tail_count (B := B) hn (primeTailEndpoint B i)
    by_cases hbad : (((coefficientPrimeSet B (coefficientForm k j b c)).filter
        (fun p : ℕ => primeTailEndpoint B i < Real.log p)).card : ℝ) <
        (2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C
    · have hm : (-(1 / 10 : ℝ)) * ((2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C) ≤
          (-(1 / 10 : ℝ)) * triplePrimeCount k
            ((auxiliaryPrimes B).filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)) j b c := by
        change _ ≤ (-(1 / 10 : ℝ)) * (primeDivisorCount
          ((auxiliaryPrimes B).filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)) (coefficientForm k j b c) : ℝ)
        rw [← hcount]
        exact mul_le_mul_of_nonpos_left hbad.le (by norm_num)
      simp only [ite_eq_left hbad, ite_eq_left hm, le_refl]
    · rw [ite_eq_right hbad]
      split_ifs
      · exact tripleCoefficientWeight_nonneg _ _ _ _
      · rfl

end JointDickman

end OAI
