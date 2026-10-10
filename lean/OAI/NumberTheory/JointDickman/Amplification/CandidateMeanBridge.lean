import OAI.NumberTheory.JointDickman.Probability.CandidateRetentionKernel
import OAI.NumberTheory.JointDickman.Amplification.SignedProductGcd
import OAI.NumberTheory.JointDickman.Amplification.AmplificationPositiveMass

namespace OAI

/-! # Positive arithmetic mass dominating the candidate remainder error -/

namespace JointDickman
open Finset

open Classical in
theorem candidateSiteKernel_eq_remainderKernel {B L T H M V : ℕ} {τ C : ℝ}
    (hB : 1 < B) (hT : 0 < T) (hV : ⌊Real.exp (2*(B : ℝ))⌋₊ ≤ V)
    (i t : Fin M) (hit : i < t) (hH : H < t.val-i.val) (hjT : t.val-i.val < T)
    {S R : Finset ℕ} (hS : S ⊆ auxiliaryPrimes B) (hR : R ⊆ auxiliaryPrimes B) :
    candidateSiteKernel B L T H M τ C
      (candidateCutoff (amplificationOuterWeight B) (amplificationInnerWeight T)) i t S R =
    independentRootMean B L τ C*
      regularRemainderKernel B L τ C (candidateRetainedWeight B L (t.val-i.val) τ C T V) S R := by
  rw [candidateSiteKernel_eq_regularArithmetic hB hT hV i t hit hH hjT hS hR,
    regularRetainedArithmeticKernel_eq]

open Classical in
theorem amplification_positive_product_mass (B j T U V : ℕ)
    (hU : (∏ p ∈ auxiliaryPrimes B,p) ≤ U) :
    (∑ A ∈ (auxiliaryPrimes B).powerset, ∑ D ∈ (auxiliaryPrimes B).powerset,
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1/2 : ℝ)/p) A*
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1/2 : ℝ)/p) D*
      amplificationProductWeight B j T V (∏ p ∈ D,p) (∏ p ∈ A,p)) =
      amplificationArithmeticSum B j T U V (fun _ => 1) (fun _ => 1) := by
  have hs := amplificationArithmeticSum_eq_fairKernel B j T U V hU (fun _ => 1) (fun _ => 1)
  rw [amplificationFairKernel_product_expectation] at hs
  have htest : subsetSiteTest (auxiliaryPrimes B) (fun _ => (1 : ℝ)) = (fun _ => 1) := rfl
  rw [htest] at hs
  simp_rw [signedSplitProductMass_one] at hs
  rw [hs,primeProductMass_pair_sum_test (auxiliaryPrimes B) (auxiliaryPrimes_prime B)]
  rw [sum_comm]
  apply sum_congr rfl
  intro A _
  apply sum_congr rfl
  intro D _
  ring

open Classical in
theorem candidateRetainedWeight_positive_mass_le (B L j T U V : ℕ) (τ C : ℝ)
    (hU : (∏ p ∈ auxiliaryPrimes B,p) ≤ U) :
    (∑ A ∈ (auxiliaryPrimes B).powerset, ∑ D ∈ (auxiliaryPrimes B).powerset,
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1/2 : ℝ)/p) A*
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1/2 : ℝ)/p) D*
      candidateRetainedWeight B L j τ C T V A D) ≤
      amplificationArithmeticSum B j T U V (fun _ => 1) (fun _ => 1) := by
  rw [← amplification_positive_product_mass B j T U V hU]
  apply sum_le_sum
  intro A hA
  apply sum_le_sum
  intro D hD
  have hq : ∀ p ∈ auxiliaryPrimes B, 0 ≤ (1/2 : ℝ)/p ∧ (1/2 : ℝ)/p ≤ 1 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (auxiliaryPrimes_prime B p hp).two_le
    exact ⟨by positivity,(div_le_one (by linarith)).mpr (by linarith)⟩
  exact mul_le_mul_of_nonneg_left (candidateRetainedWeight_bounds B L j τ C T V A D).2
    (mul_nonneg (bernoulliSubsetMass_nonneg (mem_powerset.mp hA) hq)
      (bernoulliSubsetMass_nonneg (mem_powerset.mp hD) hq))

end JointDickman

end OAI
