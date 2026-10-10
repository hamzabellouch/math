import OAI.NumberTheory.JointDickman.Probability.RemainderKernelEstimate
import OAI.NumberTheory.JointDickman.Amplification.SignedPairPushforward

namespace OAI

/-! # The finite retention-kernel mean as a signed integer-product law -/

namespace JointDickman
open Finset

open Classical in
theorem subsetKernel_product_mean (B : ℕ) (g h : Finset ℕ → ℝ) (f : ℕ → ℕ → ℝ) :
    subsetKernelBilinear B g h (retainedSubsetKernel (auxiliaryPrimes B)
      (fun A D => f (∏ p ∈ A,p) (∏ p ∈ D,p))) =
    ∑ a ∈ primeSplitProductSupport (auxiliaryPrimes B),
      ∑ b ∈ primeSplitProductSupport (auxiliaryPrimes B),
        signedSplitProductMass (auxiliaryPrimes B) g a*
        signedSplitProductMass (auxiliaryPrimes B) h b*f a b := by
  let P := auxiliaryPrimes B
  let μ := bernoulliSubsetMass P (fun p => 1/(p : ℝ))
  have hone (a : ℕ) :
      (∑ b ∈ primeSplitProductSupport P, signedSplitProductMass P h b*f a b) =
      ∑ R ∈ P.powerset, μ R*h R*∑ D ∈ P.powerset, subsetRetentionMass R D*f a (∏ p ∈ D,p) :=
    signedSplitProductMass_sum P h (f a)
  symm
  calc
    _ = ∑ a ∈ primeSplitProductSupport P, signedSplitProductMass P g a*
        (∑ b ∈ primeSplitProductSupport P, signedSplitProductMass P h b*f a b) := by
      simp only [P,mul_sum,mul_assoc]
    _ = ∑ a ∈ primeSplitProductSupport P, signedSplitProductMass P g a*
        (∑ R ∈ P.powerset, μ R*h R*
          ∑ D ∈ P.powerset, subsetRetentionMass R D*f a (∏ p ∈ D,p)) := by
      simp_rw [hone]
    _ = ∑ S ∈ P.powerset, μ S*g S*
        ∑ A ∈ P.powerset, subsetRetentionMass S A*
          (∑ R ∈ P.powerset, μ R*h R*
            ∑ D ∈ P.powerset, subsetRetentionMass R D*f (∏ p ∈ A,p) (∏ p ∈ D,p)) :=
      signedSplitProductMass_sum P g (fun a =>
        ∑ R ∈ P.powerset, μ R*h R*
          ∑ D ∈ P.powerset, subsetRetentionMass R D*f a (∏ p ∈ D,p))
    _ = _ := by
      unfold subsetKernelBilinear retainedSubsetKernel
      simp_rw [mul_sum]
      conv_lhs => arg 2; ext S; rw [sum_comm]
      apply sum_congr rfl
      intro S _
      apply sum_congr rfl
      intro R _
      apply sum_congr rfl
      intro A _
      apply sum_congr rfl
      intro D _
      dsimp only [μ]
      ring

end JointDickman

end OAI
