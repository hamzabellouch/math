import OAI.NumberTheory.JointDickman.Arithmetic.SubsetPrimeModel
import OAI.NumberTheory.JointDickman.Amplification.LatentRowSquareMass

namespace OAI

/-! # The same independent endpoint tests in subset and Boolean coordinates -/
namespace JointDickman
open Finset Classical

noncomputable def extendSubsetTest (B : ℕ) (g : (auxiliaryPrimes B).powerset → ℝ)
    (x : auxiliaryPrimes B → Bool) : ℝ :=
  g ((subsetHitEquiv (auxiliaryPrimes B)).symm x)

theorem extendSubsetTest_subset (B : ℕ) (g : (auxiliaryPrimes B).powerset → ℝ)
    (S : (auxiliaryPrimes B).powerset) :
    subsetSiteTest (auxiliaryPrimes B) (extendSubsetTest B g) S.val = g S := by
  change g ((subsetHitEquiv (auxiliaryPrimes B)).symm (subsetHitEquiv (auxiliaryPrimes B) S)) = g S
  rw [Equiv.symm_apply_apply]

theorem subsetKernelBilinear_eq_expectation (B : ℕ) (g h : Finset ℕ → ℝ)
    (F : Finset ℕ → Finset ℕ → ℝ) :
    subsetKernelBilinear B g h F =
      finiteExpectation (independentPrimeSetMass B) (fun S =>
        finiteExpectation (independentPrimeSetMass B) (fun R => F S.val R.val*g S.val*h R.val)) := by
  rw [independentPrimePair_expectation B (fun S R => F S R*g S*h R)]
  unfold subsetKernelBilinear
  apply sum_congr rfl
  intro S _
  apply sum_congr rfl
  intro R _
  ring

theorem subsetKernelBilinear_sub (B : ℕ) (g h : Finset ℕ → ℝ)
    (F G : Finset ℕ → Finset ℕ → ℝ) :
    subsetKernelBilinear B g h (fun S R => F S R-G S R) =
      subsetKernelBilinear B g h F-subsetKernelBilinear B g h G := by
  simp only [subsetKernelBilinear,mul_sub,sum_sub_distrib]

theorem subset_pair_error_of_boolean_tests (B : ℕ) (F G : Finset ℕ → Finset ℕ → ℝ)
    {ε : ℝ}
    (hFG : ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      |subsetKernelBilinear B (subsetSiteTest (auxiliaryPrimes B) g)
        (subsetSiteTest (auxiliaryPrimes B) h) F-
       subsetKernelBilinear B (subsetSiteTest (auxiliaryPrimes B) g)
        (subsetSiteTest (auxiliaryPrimes B) h) G| ≤ ε)
    (g h : (auxiliaryPrimes B).powerset → ℝ)
    (hg : ∀ S, |g S| ≤ 1) (hh : ∀ S, |h S| ≤ 1) :
    |finiteExpectation (independentPrimeSetMass B) (fun S =>
      finiteExpectation (independentPrimeSetMass B)
        (fun R => (F S.val R.val-G S.val R.val)*g S*h R))| ≤ ε := by
  have hf := hFG (extendSubsetTest B g) (extendSubsetTest B h)
    (fun x => hg _) (fun x => hh _)
  rw [← subsetKernelBilinear_sub,subsetKernelBilinear_eq_expectation] at hf
  simpa only [extendSubsetTest_subset] using hf

end JointDickman

end OAI
