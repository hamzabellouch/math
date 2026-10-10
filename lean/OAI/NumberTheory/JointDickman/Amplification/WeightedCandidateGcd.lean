import OAI.NumberTheory.JointDickman.Amplification.WeightedCandidateProduct
import OAI.NumberTheory.JointDickman.Amplification.SignedProductGcd

namespace OAI

/-! # Removing the candidate's coefficient and coprimality restrictions -/

namespace JointDickman
open Finset Filter
open scoped Topology

open Classical in
theorem weightedCandidateMean_coprime_error {B j : ℕ} (hB : 0 < B) (hj : 0 < j)
    (L T U V : ℕ) (τ C : ℝ) (hU : (∏ p ∈ auxiliaryPrimes B,p) ≤ U)
    (q : ℕ → ℕ → ℝ) (hq : ∀ a b, |q a b| ≤ 1)
    (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (hg : ∀ x, |g x| ≤ 1) (hh : ∀ x, |h x| ≤ 1) :
    |subsetKernelBilinear B (subsetSiteTest (auxiliaryPrimes B) g) (subsetSiteTest (auxiliaryPrimes B) h)
        (retainedSubsetKernel (auxiliaryPrimes B) (weightedCandidateRetained B L j τ C T V q))-
      weightedRegularizedArithmeticSum B L j τ C T U V q h g| ≤
      ((B : ℝ)*coefficientScale B)/(4*(auxiliaryCutoff B : ℝ)) := by
  rw [abs_sub_comm,weightedRegularizedArithmeticSum_eq_product B L j τ C T U V hU,
    weightedCandidateRetained_mean]
  have he :
      (∑ a ∈ primeSplitProductSupport (auxiliaryPrimes B),
        ∑ b ∈ primeSplitProductSupport (auxiliaryPrimes B),
          if b.Coprime a then
            signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) h) a*
            signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) g) b*
            (regularizedProductWeight B L j τ C T V a b*q a b) else 0) =
      ∑ a ∈ primeSplitProductSupport (auxiliaryPrimes B),
        ∑ b ∈ primeSplitProductSupport (auxiliaryPrimes B),
          if a.Coprime b then
            signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) h) a*
            signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) g) b*
            (regularizedProductWeight B L j τ C T V a b*q a b) else 0 := by
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro b _
    by_cases hc : a.Coprime b
    · rw [ite_eq_left hc.symm,ite_eq_left hc]
    · rw [ite_eq_right (fun hba => hc hba.symm),ite_eq_right hc]
  rw [he]
  apply signedPrimeProductPair_coprime_error (auxiliaryPrimes B) (auxiliaryPrimes_prime B)
    (show auxiliaryCutoff B ≠ 0 by exact pow_ne_zero _ (Nat.ne_of_gt hB))
    (fun p hp => by exact_mod_cast (mem_filter.mp hp).2) h g hh hg
    (fun a b => regularizedProductWeight B L j τ C T V a b*q a b) (mul_nonneg (Nat.cast_nonneg _) (coefficientScale_nonneg B))
  intro a b
  rw [abs_mul,abs_of_nonneg (regularizedProductWeight_bounds B L j τ C T V a b).1]
  calc
    _ ≤ regularizedProductWeight B L j τ C T V a b := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hq a b)
        (regularizedProductWeight_bounds B L j τ C T V a b).1
    _ ≤ _ := (regularizedProductWeight_bounds B L j τ C T V a b).2.trans
      (amplificationProductWeight_bounds B hj T V a b).2

end JointDickman

end OAI
