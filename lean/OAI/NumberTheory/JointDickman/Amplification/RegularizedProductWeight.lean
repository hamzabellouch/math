import OAI.NumberTheory.JointDickman.Probability.CandidateRetentionKernel
import OAI.NumberTheory.JointDickman.Counting.CoefficientRegularization

namespace OAI

/-! # The coefficient-regularized product weight in the candidate mean -/

namespace JointDickman
open Finset

open Classical in
noncomputable def regularizedProductWeight (B L j : ℕ) (τ C : ℝ) (T V : ℕ)
    (a b : ℕ) : ℝ :=
  B*∑ c ∈ Ioc 0 V, if coefficientTripleRegular B L τ C a b c then
    amplificationScalarWeight B j T c b a else 0

open Classical in
theorem regularizedProductWeight_bounds (B L j : ℕ) (τ C : ℝ) (T V a b : ℕ) :
    0 ≤ regularizedProductWeight B L j τ C T V a b ∧
      regularizedProductWeight B L j τ C T V a b ≤ amplificationProductWeight B j T V a b := by
  unfold regularizedProductWeight amplificationProductWeight
  have hterm (c : ℕ) :
      0 ≤ (if coefficientTripleRegular B L τ C a b c then amplificationScalarWeight B j T c b a else 0) ∧
      (if coefficientTripleRegular B L τ C a b c then amplificationScalarWeight B j T c b a else 0) ≤
        amplificationScalarWeight B j T c b a := by
    split_ifs
    · exact ⟨(amplificationScalarWeight_bounds ..).1,le_rfl⟩
    · exact ⟨le_rfl,(amplificationScalarWeight_bounds ..).1⟩
  exact ⟨mul_nonneg (Nat.cast_nonneg _) (sum_nonneg (fun c _ => (hterm c).1)),
    mul_le_mul_of_nonneg_left (sum_le_sum (fun c _ => (hterm c).2)) (Nat.cast_nonneg _)⟩

open Classical in
theorem candidateRetainedWeight_eq_product (B L j : ℕ) (τ C : ℝ) (T V : ℕ)
    {A D : Finset ℕ} (hA : A ⊆ auxiliaryPrimes B) (hD : D ⊆ auxiliaryPrimes B) :
    candidateRetainedWeight B L j τ C T V A D =
      if (∏ p ∈ A,p).Coprime (∏ p ∈ D,p) then
        regularizedProductWeight B L j τ C T V (∏ p ∈ D,p) (∏ p ∈ A,p) else 0 := by
  unfold candidateRetainedWeight regularizedProductWeight regularArithmeticScalar
  simp only [coefficientTripleRegular,coefficientPrimeSet_primeProduct hA,
    coefficientPrimeSet_primeProduct hD]
  by_cases hc : (∏ p ∈ A,p).Coprime (∏ p ∈ D,p)
  · simp_rw [ite_and,ite_eq_left hc]
    by_cases ha : RegularPrimeSet B L τ C A
    all_goals by_cases hd : RegularPrimeSet B L τ C D
    all_goals simp only [ha,hd,ite_true,ite_false,sum_const_zero,mul_zero]
  · simp_rw [ite_and,ite_eq_right hc]
    simp only [sum_const_zero,mul_zero,ite_self]

end JointDickman

end OAI
