import OAI.NumberTheory.JointDickman.Amplification.RegularizedProductWeight
import OAI.NumberTheory.JointDickman.Probability.SubsetKernelProductLaw

namespace OAI

/-! # The candidate mean as the regularized signed product sum -/

namespace JointDickman
open Finset

open Classical in
theorem candidateRetainedMean_eq_product (B L j : ℕ) (τ C : ℝ) (T V : ℕ)
    (g h : Finset ℕ → ℝ) :
    subsetKernelBilinear B g h (retainedSubsetKernel (auxiliaryPrimes B)
      (candidateRetainedWeight B L j τ C T V)) =
    ∑ a ∈ primeSplitProductSupport (auxiliaryPrimes B),
      ∑ b ∈ primeSplitProductSupport (auxiliaryPrimes B),
        if b.Coprime a then signedSplitProductMass (auxiliaryPrimes B) h a*
          signedSplitProductMass (auxiliaryPrimes B) g b*
          regularizedProductWeight B L j τ C T V a b else 0 := by
  have hk : retainedSubsetKernel (auxiliaryPrimes B) (candidateRetainedWeight B L j τ C T V) =
      retainedSubsetKernel (auxiliaryPrimes B) (fun A D =>
        if (∏ p ∈ A,p).Coprime (∏ p ∈ D,p) then
          regularizedProductWeight B L j τ C T V (∏ p ∈ D,p) (∏ p ∈ A,p) else 0) := by
    funext S R
    unfold retainedSubsetKernel
    apply sum_congr rfl
    intro A hA
    apply sum_congr rfl
    intro D hD
    rw [candidateRetainedWeight_eq_product B L j τ C T V (mem_powerset.mp hA) (mem_powerset.mp hD)]
  rw [hk,subsetKernel_product_mean B g h (fun b a =>
    if b.Coprime a then regularizedProductWeight B L j τ C T V a b else 0),sum_comm]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  by_cases hc : b.Coprime a
  · rw [ite_eq_left hc,ite_eq_left hc]
    ring
  · rw [ite_eq_right hc,ite_eq_right hc,mul_zero]

open Classical in
theorem signedProductPair_sum_on (P : Finset ℕ) (g h : Finset ℕ → ℝ)
    (f : ℕ → ℕ → ℝ) (I : Finset ℕ) (hI : primeSplitProductSupport P ⊆ I) :
    (∑ a ∈ I, ∑ b ∈ I, signedSplitProductMass P g a*signedSplitProductMass P h b*f a b) =
    ∑ a ∈ primeSplitProductSupport P, ∑ b ∈ primeSplitProductSupport P,
      signedSplitProductMass P g a*signedSplitProductMass P h b*f a b := by
  symm
  calc
    _ = ∑ a ∈ I, ∑ b ∈ primeSplitProductSupport P,
        signedSplitProductMass P g a*signedSplitProductMass P h b*f a b := by
      apply sum_subset hI
      intro a _ ha
      rw [signedSplitProductMass_zero_off_support P g a ha]
      simp only [zero_mul,sum_const_zero]
    _ = _ := by
      apply sum_congr rfl
      intro a _
      apply sum_subset hI
      intro b _ hb
      rw [signedSplitProductMass_zero_off_support P h b hb]
      simp only [mul_zero,zero_mul]

open Classical in
theorem regularizedAmplificationArithmeticSum_eq_product (B L j : ℕ) (τ C : ℝ)
    (T U V : ℕ) (hU : (∏ p ∈ auxiliaryPrimes B,p) ≤ U)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) :
    regularizedAmplificationArithmeticSum B L j τ C T U V g h =
    ∑ a ∈ primeSplitProductSupport (auxiliaryPrimes B),
      ∑ b ∈ primeSplitProductSupport (auxiliaryPrimes B),
        signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) g) a*
        signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) h) b*
        regularizedProductWeight B L j τ C T V a b := by
  rw [← signedProductPair_sum_on (auxiliaryPrimes B) _ _ _ (Ioc 0 U)
    (primeSplitProductSupport_subset_Ioc (auxiliaryPrimes_prime B) hU)]
  unfold regularizedAmplificationArithmeticSum regularizedProductWeight
  simp_rw [amplificationArithmeticTerm_factor,mul_sum]
  conv_lhs => arg 2; ext c; rw [sum_comm]
  rw [sum_comm]
  conv_lhs => arg 2; ext a; rw [sum_comm]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro c _
  split_ifs <;> ring

end JointDickman

end OAI
