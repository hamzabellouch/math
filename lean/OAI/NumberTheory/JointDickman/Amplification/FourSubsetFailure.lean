import OAI.NumberTheory.JointDickman.Probability.FairSplitPairRegularity
import OAI.NumberTheory.JointDickman.Counting.SelectedCoefficientRegularity

namespace OAI

/-! # Finite decomposition of the four regularity failures -/

namespace JointDickman

open Finset

open Classical in
noncomputable def fairFourSubsetFailureAt (B L : ℕ) (τ C : ℝ) (A D : Finset ℕ) : ℝ :=
  ∑ R ∈ (auxiliaryPrimes B).powerset, ∑ Q ∈ (auxiliaryPrimes B).powerset,
    if (RegularPrimeSet B L τ C A ∧ RegularPrimeSet B L τ C D) ∧
        (RegularPrimeSet B L τ C R ∧ RegularPrimeSet B L τ C Q) then 0 else
      fairSelectedRemainingMass (auxiliaryPrimes B) A R *
        fairSelectedRemainingMass (auxiliaryPrimes B) D Q

open Classical in
noncomputable def fairFourSubsetFailure (B L T : ℕ) (τ C : ℝ) : ℝ :=
  ∑ A ∈ (auxiliaryPrimes B).powerset, ∑ D ∈ (auxiliaryPrimes B).powerset,
    if (∏ p ∈ A, p, ∏ p ∈ D, p) ∈ amplificationCoefficientPairs B T then
      fairFourSubsetFailureAt B L τ C A D else 0

theorem fairRemainingPairFailure_nonneg (B L : ℕ) (τ C : ℝ) {A D : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) (hD : D ⊆ auxiliaryPrimes B) :
    0 ≤ fairRemainingPairFailure B L τ C A D := by
  unfold fairRemainingPairFailure
  apply sum_nonneg
  intro R hR
  apply sum_nonneg
  intro Q hQ
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (fairSelectedRemainingMass_nonneg (auxiliaryPrimes_prime B) hA (mem_powerset.mp hR))
      (fairSelectedRemainingMass_nonneg (auxiliaryPrimes_prime B) hD (mem_powerset.mp hQ))

open Classical in
theorem fairFourSubsetFailureAt_union (B L : ℕ) (τ C : ℝ) {A D : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) (hD : D ⊆ auxiliaryPrimes B) :
    fairFourSubsetFailureAt B L τ C A D ≤
      (if RegularPrimeSet B L τ C A ∧ RegularPrimeSet B L τ C D then 0 else
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) A *
          bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) D) +
      fairRemainingPairFailure B L τ C A D := by
  by_cases hreg : RegularPrimeSet B L τ C A ∧ RegularPrimeSet B L τ C D
  · simp only [fairFourSubsetFailureAt, hreg, true_and, ite_true, zero_add, fairRemainingPairFailure]
    exact le_rfl
  · simp only [fairFourSubsetFailureAt, hreg, false_and, ite_false]
    rw [← sum_mul_sum, fairSelectedRemainingMass_sum (auxiliaryPrimes_prime B) hA,
      fairSelectedRemainingMass_sum (auxiliaryPrimes_prime B) hD]
    exact le_add_of_nonneg_right (fairRemainingPairFailure_nonneg B L τ C hA hD)

open Classical in
theorem fairFourSubsetFailure_union (B L T : ℕ) (τ C : ℝ) :
    fairFourSubsetFailure B L T τ C ≤
      (∑ ac ∈ amplificationCoefficientPairs B T, coefficientPairFailureMass B L τ C ac.1 ac.2) +
      ∑ A ∈ (auxiliaryPrimes B).powerset, ∑ D ∈ (auxiliaryPrimes B).powerset,
        if (∏ p ∈ A, p, ∏ p ∈ D, p) ∈ amplificationCoefficientPairs B T then
          fairRemainingPairFailure B L τ C A D else 0 := by
  rw [coefficientPairFailureMass_selected_sum]
  simp only [← sum_add_distrib]
  unfold fairFourSubsetFailure
  apply sum_le_sum
  intro A hA
  apply sum_le_sum
  intro D hD
  by_cases hmem : (∏ p ∈ A, p, ∏ p ∈ D, p) ∈ amplificationCoefficientPairs B T
  · simp only [hmem, ite_true]
    exact fairFourSubsetFailureAt_union B L τ C (mem_powerset.mp hA) (mem_powerset.mp hD)
  · simp only [hmem, ite_false, add_zero, le_refl]

end JointDickman

end OAI
