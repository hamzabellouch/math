import OAI.NumberTheory.JointDickman.Amplification.RemainderNormalization

namespace OAI

/-! # The two-endpoint law after selecting a first representation -/

namespace JointDickman
open Finset Classical

theorem weighted_endpoint_change_of_measure {B : ℕ} {A : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) (F : Finset ℕ → ℝ) :
    (∑ S ∈ (auxiliaryPrimes B).powerset, if A ⊆ S then
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
        residueBaseWeight B (S \ A)*F S else 0) =
      remainderTiltNormalizer B A/(∏ p ∈ A, p : ℕ)*
        ∑ R ∈ (auxiliaryPrimes B \ A).powerset,
          bernoulliSubsetMass (auxiliaryPrimes B \ A)
            (fun p => 1/(2*(p : ℝ)-1)) R*F (A ∪ R) := by
  have hh := weighted_remainder_change_of_measure hA (fun R => F (A ∪ R))
  rw [← hh]
  apply sum_congr rfl
  intro S _
  split_ifs with hs
  · rw [union_sdiff_of_subset hs]
  · rfl

/-- Exact factorization of the first-representation measure at both
endpoints. The test may depend jointly on both reconstructed site types. -/
theorem weighted_endpoint_pair_change_of_measure {B : ℕ} {A D : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) (hD : D ⊆ auxiliaryPrimes B)
    (F : Finset ℕ → Finset ℕ → ℝ) :
    (∑ S ∈ (auxiliaryPrimes B).powerset, ∑ R ∈ (auxiliaryPrimes B).powerset,
      if A ⊆ S ∧ D ⊆ R then
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*
        residueBaseWeight B (S \ A)*residueBaseWeight B (R \ D)*F S R else 0) =
      (remainderTiltNormalizer B A/(∏ p ∈ A, p : ℕ))*
      (remainderTiltNormalizer B D/(∏ p ∈ D, p : ℕ))*
        ∑ U ∈ (auxiliaryPrimes B \ A).powerset,
          ∑ V ∈ (auxiliaryPrimes B \ D).powerset,
            bernoulliSubsetMass (auxiliaryPrimes B \ A) (fun p => 1/(2*(p : ℝ)-1)) U*
            bernoulliSubsetMass (auxiliaryPrimes B \ D) (fun p => 1/(2*(p : ℝ)-1)) V*
            F (A ∪ U) (D ∪ V) := by
  let G (S : Finset ℕ) := ∑ R ∈ (auxiliaryPrimes B).powerset, if D ⊆ R then
    bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*
      residueBaseWeight B (R \ D)*F S R else 0
  have hfirst : (∑ S ∈ (auxiliaryPrimes B).powerset, ∑ R ∈ (auxiliaryPrimes B).powerset,
      if A ⊆ S ∧ D ⊆ R then
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*
        residueBaseWeight B (S \ A)*residueBaseWeight B (R \ D)*F S R else 0) =
      ∑ S ∈ (auxiliaryPrimes B).powerset, if A ⊆ S then
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
          residueBaseWeight B (S \ A)*G S else 0 := by
    apply sum_congr rfl
    intro S _
    by_cases hs : A ⊆ S
    · rw [ite_eq_left hs]
      dsimp [G]
      rw [mul_sum]
      apply sum_congr rfl
      intro R _
      by_cases hr : D ⊆ R <;> simp only [hs,hr,and_self,true_and,ite_true,ite_false,mul_zero]
      ring
    · simp only [hs,false_and,ite_false,sum_const_zero]
  rw [hfirst,weighted_endpoint_change_of_measure hA G]
  have hsecond (S : Finset ℕ) : G S =
      remainderTiltNormalizer B D/(∏ p ∈ D, p : ℕ)*
        ∑ V ∈ (auxiliaryPrimes B \ D).powerset,
          bernoulliSubsetMass (auxiliaryPrimes B \ D) (fun p => 1/(2*(p : ℝ)-1)) V*
            F S (D ∪ V) := weighted_endpoint_change_of_measure hD (F S)
  simp_rw [hsecond,mul_sum]
  apply sum_congr rfl
  intro U _
  apply sum_congr rfl
  intro V _
  ring

end JointDickman

end OAI
