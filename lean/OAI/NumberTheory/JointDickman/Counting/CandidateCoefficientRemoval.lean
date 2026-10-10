import OAI.NumberTheory.JointDickman.Amplification.CandidateProductMean
import OAI.NumberTheory.JointDickman.Amplification.SignedProductGcd

namespace OAI

/-! # Removing the candidate's coefficient and coprimality restrictions -/

namespace JointDickman
open Finset Filter
open scoped Topology

open Classical in
theorem candidateRetainedMean_coprime_error {B j : ℕ} (hB : 0 < B) (hj : 0 < j)
    (L T U V : ℕ) (τ C : ℝ) (hU : (∏ p ∈ auxiliaryPrimes B,p) ≤ U)
    (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (hg : ∀ x, |g x| ≤ 1) (hh : ∀ x, |h x| ≤ 1) :
    |subsetKernelBilinear B (subsetSiteTest (auxiliaryPrimes B) g) (subsetSiteTest (auxiliaryPrimes B) h)
        (retainedSubsetKernel (auxiliaryPrimes B) (candidateRetainedWeight B L j τ C T V))-
      regularizedAmplificationArithmeticSum B L j τ C T U V h g| ≤
      ((B : ℝ)*coefficientScale B)/(4*(auxiliaryCutoff B : ℝ)) := by
  rw [abs_sub_comm,regularizedAmplificationArithmeticSum_eq_product B L j τ C T U V hU,
    candidateRetainedMean_eq_product]
  have he :
      (∑ a ∈ primeSplitProductSupport (auxiliaryPrimes B),
        ∑ b ∈ primeSplitProductSupport (auxiliaryPrimes B),
          if b.Coprime a then
            signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) h) a*
            signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) g) b*
            regularizedProductWeight B L j τ C T V a b else 0) =
      ∑ a ∈ primeSplitProductSupport (auxiliaryPrimes B),
        ∑ b ∈ primeSplitProductSupport (auxiliaryPrimes B),
          if a.Coprime b then
            signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) h) a*
            signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) g) b*
            regularizedProductWeight B L j τ C T V a b else 0 := by
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
    (regularizedProductWeight B L j τ C T V) (mul_nonneg (Nat.cast_nonneg _) (coefficientScale_nonneg B))
  intro a b
  rw [abs_of_nonneg (regularizedProductWeight_bounds B L j τ C T V a b).1]
  exact (regularizedProductWeight_bounds B L j τ C T V a b).2.trans
    (amplificationProductWeight_bounds B hj T V a b).2

open Classical in
theorem candidateRetainedMean_arithmetic_comparison
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ L : ℕ, ∀ τ : ℝ, 0 < L → 0 < τ →
      ∃ ε : ℕ → ℝ, (∀ B, 0 ≤ ε B) ∧ Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ B : ℕ in atTop, ∀ T : ℕ, 0 < T → Real.log T ≤ (B : ℝ)/10 →
          ∀ (C : ℝ) (j U V : ℕ), 0 ≤ C → 0 < j → (∏ p ∈ auxiliaryPrimes B,p) ≤ U →
          (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
            ⌊(17/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊ ≤ U) →
          (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
            ⌊(17/4 : ℝ)*(Real.exp ((k : ℝ)*Real.log 2)/T)⌋₊ ≤ V) →
          ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
          (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
          |subsetKernelBilinear B (subsetSiteTest (auxiliaryPrimes B) g) (subsetSiteTest (auxiliaryPrimes B) h)
              (retainedSubsetKernel (auxiliaryPrimes B) (candidateRetainedWeight B L j τ C T V))-
            amplificationArithmeticSum B j T U V h g| ≤
            ((B : ℝ)*coefficientScale B)/(4*(auxiliaryCutoff B : ℝ))+
              K/T*singularFactor 24 j*(ε B+Real.exp (-(1/10 : ℝ)*C)) := by
  obtain ⟨K,hK,hloss⟩ := amplification_coefficient_regularization hFord hM
  refine ⟨K,hK,?_⟩
  intro L τ hL hτ
  obtain ⟨ε,hε0,hε,hloss⟩ := hloss L τ hL hτ
  refine ⟨ε,hε0,hε,?_⟩
  filter_upwards [hloss,eventually_gt_atTop 0] with B hb hB
  intro T hT hlog C j U V hC hj hU hdyU hdyV g h hg hh
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hc := hb T hT1 hlog C j U V hC (Nat.ne_of_gt hj) hdyU hdyV h g hh hg
  rw [abs_sub_comm] at hc
  exact (abs_sub_le _ (regularizedAmplificationArithmeticSum B L j τ C T U V h g) _).trans
    (add_le_add (candidateRetainedMean_coprime_error hB hj L T U V τ C hU g h hg hh) hc)

end JointDickman

end OAI
