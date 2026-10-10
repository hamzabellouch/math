import OAI.NumberTheory.JointDickman.Probability.SignedChannelMass
import OAI.NumberTheory.JointDickman.Probability.RemainderKernelEstimate

namespace OAI

/-! # Transporting a finite prime-feature model to endpoint subsets -/
namespace JointDickman
open Finset Classical

noncomputable def subsetPrimeModel (B : ℕ)
    (K : (auxiliaryPrimes B → Bool) → (auxiliaryPrimes B → Bool) → ℝ)
    (S R : Finset ℕ) : ℝ :=
  K (fun p => decide (p.val ∈ S)) (fun p => decide (p.val ∈ R))

theorem subsetKernelBilinear_primeModel (B : ℕ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (K : (auxiliaryPrimes B → Bool) → (auxiliaryPrimes B → Bool) → ℝ) :
    subsetKernelBilinear B (subsetSiteTest (auxiliaryPrimes B) g)
      (subsetSiteTest (auxiliaryPrimes B) h) (subsetPrimeModel B K) =
      ∑ x, ∑ y, fullPrimeMass (auxiliaryPrimes B) x*fullPrimeMass (auxiliaryPrimes B) y*
        g x*h y*K x y := by
  rw [← (subsetHitEquiv (auxiliaryPrimes B)).sum_comp]
  simp_rw [← (subsetHitEquiv (auxiliaryPrimes B)).sum_comp
    (fun y => fullPrimeMass (auxiliaryPrimes B) _*fullPrimeMass (auxiliaryPrimes B) y*
      g _*h y*K _ y)]
  simp_rw [fullPrimeMass_subset]
  let F (S R : Finset ℕ) :=
    bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
    bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*
    subsetSiteTest (auxiliaryPrimes B) g S*subsetSiteTest (auxiliaryPrimes B) h R*
    subsetPrimeModel B K S R
  change (∑ S ∈ (auxiliaryPrimes B).powerset, ∑ R ∈ (auxiliaryPrimes B).powerset, F S R) =
    ∑ S : (auxiliaryPrimes B).powerset, ∑ R : (auxiliaryPrimes B).powerset, F S.val R.val
  symm
  exact (sum_coe_sort (auxiliaryPrimes B).powerset
    (fun S => ∑ R : (auxiliaryPrimes B).powerset, F S R.val)).trans
    (sum_congr rfl (fun S _ => sum_coe_sort (auxiliaryPrimes B).powerset (F S)))

end JointDickman

end OAI
