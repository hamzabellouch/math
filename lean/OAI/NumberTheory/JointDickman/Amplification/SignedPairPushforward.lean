import OAI.NumberTheory.JointDickman.Probability.SignedChannelMass

namespace OAI

/-! # The exact two-endpoint fair-split pushforward -/

namespace JointDickman
open Finset

open Classical in
theorem signedSplitProductMass_zero_off_support (P : Finset ℕ)
    (g : Finset ℕ → ℝ) (n : ℕ) (hn : n ∉ primeSplitProductSupport P) :
    signedSplitProductMass P g n = 0 := by
  have hprod : ∀ A ∈ P.powerset, (∏ p ∈ A, p) ≠ n := by
    intro A hA he
    exact hn (mem_image.mpr ⟨A,hA,he⟩)
  unfold signedSplitProductMass
  apply sum_eq_zero
  intro S _
  have hz : splitProductMass P S n = 0 := by
    unfold splitProductMass
    apply sum_eq_zero
    intro A hA
    rw [ite_eq_right (hprod A hA),mul_zero]
  rw [hz,mul_zero]

open Classical in
theorem signedSplitProductMass_sum_on (P : Finset ℕ)
    (g : (P → Bool) → ℝ) (F : ℕ → ℝ) (A : Finset ℕ)
    (hA : primeSplitProductSupport P ⊆ A) :
    (∑ n ∈ A, signedSplitProductMass P (subsetSiteTest P g) n*F n) =
      ∑ x : P → Bool, fullPrimeMass P x*g x*
        ∑ y : P → Bool, fairRetentionMass x y*F (retainedPrimeProduct P y) := by
  rw [← signedSplitProductMass_expectation]
  symm
  apply sum_subset hA
  intro n _ hn
  rw [signedSplitProductMass_zero_off_support P _ n hn,zero_mul]

open Classical in
theorem signedSplitProductMass_pair_expectation (P : Finset ℕ)
    (g h : (P → Bool) → ℝ) (F : ℕ → ℕ → ℝ) (A D : Finset ℕ)
    (hA : primeSplitProductSupport P ⊆ A) (hD : primeSplitProductSupport P ⊆ D) :
    (∑ a ∈ A, ∑ d ∈ D,
      signedSplitProductMass P (subsetSiteTest P g) a*
        signedSplitProductMass P (subsetSiteTest P h) d*F a d) =
      ∑ x : P → Bool, ∑ z : P → Bool,
        fullPrimeMass P x*fullPrimeMass P z*g x*h z*
          ∑ y : P → Bool, ∑ w : P → Bool,
            fairRetentionMass x y*fairRetentionMass z w*
              F (retainedPrimeProduct P y) (retainedPrimeProduct P w) := by
  calc
    _ = ∑ a ∈ A, signedSplitProductMass P (subsetSiteTest P g) a*
        (∑ d ∈ D, signedSplitProductMass P (subsetSiteTest P h) d*F a d) := by
      apply sum_congr rfl
      intro a _
      rw [mul_sum]
      apply sum_congr rfl
      intro d _
      ring
    _ = ∑ x : P → Bool, fullPrimeMass P x*g x*
        ∑ y : P → Bool, fairRetentionMass x y*
          (∑ z : P → Bool, fullPrimeMass P z*h z*
            ∑ w : P → Bool, fairRetentionMass z w*
              F (retainedPrimeProduct P y) (retainedPrimeProduct P w)) := by
      rw [signedSplitProductMass_sum_on P g _ A hA]
      simp_rw [signedSplitProductMass_sum_on P h _ D hD]
    _ = _ := by
      simp_rw [mul_sum]
      apply sum_congr rfl
      intro x _
      rw [sum_comm]
      apply sum_congr rfl
      intro z _
      apply sum_congr rfl
      intro y _
      apply sum_congr rfl
      intro w _
      ring

open Classical in
/-- The unsigned law pushed to products, retaining an arbitrary test. -/
theorem primeProductMass_sum_test (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (z : ℝ) (F : ℕ → ℝ) :
    (∑ n ∈ primeSplitProductSupport P, primeProductMass P z n*F n) =
      ∑ A ∈ P.powerset, bernoulliSubsetMass P (fun p => z/p) A*F (∏ p ∈ A,p) := by
  unfold primeSplitProductSupport
  rw [sum_image]
  · apply sum_congr rfl
    intro A hA
    rw [primeProductMass_at_product z hP (mem_powerset.mp hA)]
  · intro A hA D hD he
    exact primeProduct_injective hP (mem_powerset.mp hA) (mem_powerset.mp hD) he

end JointDickman

end OAI
