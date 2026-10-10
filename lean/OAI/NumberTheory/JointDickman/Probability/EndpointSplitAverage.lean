import OAI.NumberTheory.JointDickman.Counting.BlockCandidates
import OAI.NumberTheory.JointDickman.Probability.ArithmeticSplitWeights
import OAI.NumberTheory.JointDickman.Amplification.SubsetThinning

namespace OAI

/-! # Averaging a candidate's coefficient and remaining endpoint weight -/

namespace JointDickman
open Finset

open Classical in
theorem endpoint_split_weight_bound {B L : ℕ} {τ C : ℝ} (hB : 1 < B)
    (S : Finset ℕ) (hS : S ⊆ auxiliaryPrimes B) (F : Finset ℕ → ℝ)
    (hF : ∀ A ⊆ auxiliaryPrimes B, 0 ≤ F A) :
    (∑ A ∈ endpointSplits B L τ C S,
      regularCoefficientWeight B L τ C (∏ p ∈ A, p)*
        regularResidueWeight B L τ C (S \ A)*F A) ≤
      (B : ℝ)*∑ A ∈ (auxiliaryPrimes B).powerset, subsetRetentionMass S A*F A := by
  have hsub : endpointSplits B L τ C S ⊆ (auxiliaryPrimes B).powerset := by
    intro A hA
    exact mem_powerset.mpr ((mem_endpointSplits.mp hA).1.trans hS)
  calc
    _ = (B : ℝ)*∑ A ∈ endpointSplits B L τ C S, subsetRetentionMass S A*F A := by
      rw [mul_sum]
      apply sum_congr rfl
      intro A hA
      obtain ⟨hAS,hreg,hrem⟩ := mem_endpointSplits.mp hA
      rw [regular_arithmetic_split_identity hB hS hAS]
      simp only [hreg,hrem,and_self,ite_true,mul_one,mul_assoc]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg B)
      apply sum_le_sum_of_subset_of_nonneg hsub
      intro A hA _
      apply mul_nonneg _ (hF A (mem_powerset.mp hA))
      unfold subsetRetentionMass
      split_ifs <;> positivity

open Classical in
/-- The independently averaged endpoint split has the exact half-prime
marginal, without dividing by the probability of passing regularity. -/
theorem independent_endpoint_split_average {B L : ℕ} {τ C : ℝ} (hB : 1 < B)
    (F : Finset ℕ → ℝ) (hF : ∀ A ⊆ auxiliaryPrimes B, 0 ≤ F A) :
    (∑ S ∈ (auxiliaryPrimes B).powerset,
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
      ∑ A ∈ endpointSplits B L τ C S,
        regularCoefficientWeight B L τ C (∏ p ∈ A, p)*
          regularResidueWeight B L τ C (S \ A)*F A) ≤
      (B : ℝ)*∑ A ∈ (auxiliaryPrimes B).powerset,
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1/2 : ℝ)/p) A*F A := by
  have hprob (p : ℕ) (hp : p ∈ auxiliaryPrimes B) :
      0 ≤ 1/(p : ℝ) ∧ 1/(p : ℝ) ≤ 1 := by
    have h1 : (1 : ℝ) ≤ p := by exact_mod_cast (auxiliaryPrimes_prime B p hp).one_le
    exact ⟨by positivity,(div_le_one (by linarith)).mpr h1⟩
  calc
    _ ≤ ∑ S ∈ (auxiliaryPrimes B).powerset,
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
        ((B : ℝ)*∑ A ∈ (auxiliaryPrimes B).powerset, subsetRetentionMass S A*F A) := by
      apply sum_le_sum
      intro S hS
      exact mul_le_mul_of_nonneg_left
        (endpoint_split_weight_bound hB S (mem_powerset.mp hS) F hF)
        (bernoulliSubsetMass_nonneg (mem_powerset.mp hS) hprob)
    _ = (B : ℝ)*∑ S ∈ (auxiliaryPrimes B).powerset,
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
        ∑ A ∈ (auxiliaryPrimes B).powerset, subsetRetentionMass S A*F A := by
      rw [mul_sum]
      apply sum_congr rfl
      intro S _
      ring
    _ = _ := by
      rw [subsetRetentionMass_expectation]
      have hq : (fun p : ℕ => (1/(p : ℝ))/2) = (fun p : ℕ => (1/2 : ℝ)/p) := by
        funext p
        ring
      rw [hq]

end JointDickman

end OAI
