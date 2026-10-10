import OAI.NumberTheory.JointDickman.Arithmetic.SquarefreeQuotientSite
import OAI.NumberTheory.JointDickman.Amplification.WeightedAmplification

namespace OAI

/-! # The divisor weight equals the fair-split model away from square hits -/

namespace JointDickman
open Finset

open Classical in
noncomputable def arithmeticSubsetAmplification (B L : ℕ) (τ C : ℝ)
    (w : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  (1 / (B : ℝ)) * ∑ A ∈ (auxiliaryPrimes B).powerset, ∑ D ∈ (auxiliaryPrimes B).powerset,
    if (∏ p ∈ A, p) ∣ n ∧ (∏ p ∈ D, p) ∣ n + 1 then
      (regularCoefficientWeight B L τ C (∏ p ∈ A, p) *
        regularResidueWeight B L τ C (coefficientPrimeSet B (n / (∏ p ∈ A, p)))) *
      (regularCoefficientWeight B L τ C (∏ p ∈ D, p) *
        regularResidueWeight B L τ C (coefficientPrimeSet B ((n + 1) / (∏ p ∈ D, p)))) *
      w (∏ p ∈ A, p) (∏ p ∈ D, p) else 0

open Classical in
theorem arithmeticSubsetAmplification_eq_model {B L n : ℕ} {τ C : ℝ}
    (hB : 1 < B) (w : ℕ → ℕ → ℝ)
    (hno₁ : ∀ p ∈ auxiliaryPrimes B, ¬ p^2 ∣ n)
    (hno₂ : ∀ p ∈ auxiliaryPrimes B, ¬ p^2 ∣ n + 1) :
    arithmeticSubsetAmplification B L τ C w n =
      independentWeightedAmplification B L τ C w
        (coefficientPrimeSet B n) (coefficientPrimeSet B (n + 1)) := by
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast (by omega : B ≠ 0)
  have hS : coefficientPrimeSet B n ⊆ auxiliaryPrimes B := filter_subset _ _
  have hR : coefficientPrimeSet B (n + 1) ⊆ auxiliaryPrimes B := filter_subset _ _
  unfold arithmeticSubsetAmplification independentWeightedAmplification sitePairSplitAverage
  simp only [mul_sum]
  apply sum_congr rfl
  intro A hA
  apply sum_congr rfl
  intro D hD
  have hAP := mem_powerset.mp hA
  have hDP := mem_powerset.mp hD
  by_cases hd : (∏ p ∈ A, p) ∣ n ∧ (∏ p ∈ D, p) ∣ n + 1
  · rw [ite_eq_left hd,
      coefficientPrimeSet_quotient hAP hd.1 hno₁, coefficientPrimeSet_quotient hDP hd.2 hno₂]
    have hAS := (primeProduct_dvd_site_iff hAP).mp hd.1
    have hDR := (primeProduct_dvd_site_iff hDP).mp hd.2
    rw [regular_arithmetic_split_identity hB hS hAS, regular_arithmetic_split_identity hB hR hDR]
    by_cases h₁ : RegularPrimeSet B L τ C A <;>
    by_cases h₂ : RegularPrimeSet B L τ C D <;>
    by_cases h₃ : RegularPrimeSet B L τ C (coefficientPrimeSet B n \ A) <;>
    by_cases h₄ : RegularPrimeSet B L τ C (coefficientPrimeSet B (n + 1) \ D)
    all_goals simp only [h₁, h₂, h₃, h₄, and_self, and_false, and_true,
      ite_true, ite_false, mul_zero, zero_mul, mul_one]
    field_simp
  · rw [ite_eq_right hd, mul_zero]
    by_cases ha : A ⊆ coefficientPrimeSet B n
    · have hdn : ¬ D ⊆ coefficientPrimeSet B (n + 1) := fun hh =>
        hd ⟨(primeProduct_dvd_site_iff hAP).mpr ha, (primeProduct_dvd_site_iff hDP).mpr hh⟩
      simp only [subsetRetentionMass, hdn, ite_false, mul_zero, zero_mul]
    · simp only [subsetRetentionMass, ha, ite_false, mul_zero, zero_mul]

end JointDickman

end OAI
