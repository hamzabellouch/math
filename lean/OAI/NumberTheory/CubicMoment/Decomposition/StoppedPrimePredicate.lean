import OAI.NumberTheory.CubicMoment.Decomposition.StoppedPrimeIntervals

namespace OAI

/-! Both actual stopping branches, including failure of the earlier
crossing test. Fixing the selected prime's bin fixes all these tests. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def stoppedSideTest (bin : Eisenstein → ℕ) (ell : ℕ → ℝ)
    (j k h : ℕ) (Z Q : ℝ) (early : Bool) (r d : Eisenstein) : Prop :=
  stoppingSideTest bin ell j k Z r d ∧
    (early = true ∨ norm r*primeSurrogate (primeBinPrefix (primaryPrimeFactors d) bin h) bin ell < Q)

lemma stoppedSideTest_free_prime_same_bin (bin : Eisenstein → ℕ)
    (ell : ℕ → ℝ) (j k h : ℕ) (Z Q : ℝ) (early : Bool) (r : Eisenstein)
    {c p q : Eisenstein} (hc : primary c) (hs : Squarefree c)
    (hp : primaryPrime p) (hq : primaryPrime q) (hpc : ¬p ∣ c) (hqc : ¬q ∣ c)
    (hbin : bin p = bin q) :
    stoppedSideTest bin ell j k h Z Q early r (p*c) ↔
      stoppedSideTest bin ell j k h Z Q early r (q*c) := by
  exact and_congr
    (stoppingSideTest_free_prime_same_bin bin ell j k Z r hc hs hp hq hpc hqc hbin)
    (or_congr Iff.rfl
      (failedStage_free_prime_same_bin bin ell h Q r hc hs hp hq hpc hqc hbin))

theorem sum_stoppedSide_same_bin (S : Finset Eisenstein)
    (bin : Eisenstein → ℕ) (ell : ℕ → ℝ) (j k h : ℕ) (Z Q : ℝ) (early : Bool)
    (r : Eisenstein) {c p₀ : Eisenstein} (hc : primary c) (hsc : Squarefree c)
    (hp₀ : p₀ ∈ S) (hS : ∀ p ∈ S, primaryPrime p)
    (hcop : ∀ p ∈ S, ¬p ∣ c) (hbin : ∀ p ∈ S, bin p = bin p₀)
    (F : Eisenstein → ℂ) :
    (∑ p ∈ S with stoppedSideTest bin ell j k h Z Q early r (p*c), F p) =
      if stoppedSideTest bin ell j k h Z Q early r (p₀*c) then ∑ p ∈ S, F p else 0 := by
  rw [Finset.sum_filter]
  by_cases ht : stoppedSideTest bin ell j k h Z Q early r (p₀*c)
  · rw [ite_eq_left ht]
    apply Finset.sum_congr rfl
    intro p hp
    rw [ite_eq_left ((stoppedSideTest_free_prime_same_bin bin ell j k h Z Q early r hc hsc
      (hS p hp) (hS p₀ hp₀) (hcop p hp) (hcop p₀ hp₀) (hbin p hp)).mpr ht)]
  · rw [ite_eq_right ht]
    apply Finset.sum_eq_zero
    intro p hp
    apply ite_eq_right
    intro h'
    exact ht ((stoppedSideTest_free_prime_same_bin bin ell j k h Z Q early r hc hsc
      (hS p hp) (hS p₀ hp₀) (hcop p hp) (hcop p₀ hp₀) (hbin p hp)).mp h')

theorem stoppedSideTest_free_distinguished_interval
    (bin : Eisenstein → ℕ) (ell : ℕ → ℝ) (j k h : ℕ) (Z Q : ℝ) (early : Bool)
    {c : Eisenstein} (hc : c ≠ 0) (d p : Eisenstein) (hell : 0 < ell j)
    (hS : 0 < primeSurrogate (primaryPrimeFactors d) bin ell)
    (hE : 0 < primeSurrogate (primeBinPrefix (primaryPrimeFactors d) bin h) bin ell) :
    stoppedSideTest bin ell j k h Z Q early (c*p) d ↔
      ((∀ q ∈ primaryPrimeFactors d, bin q ≤ j) ∧
      (primeBin (primaryPrimeFactors d) bin j).card = k ∧
      Z/(norm c*primeSurrogate (primaryPrimeFactors d) bin ell) ≤ norm p ∧
      norm p < Z*ell j/(norm c*primeSurrogate (primaryPrimeFactors d) bin ell)) ∧
      (early = true ∨ norm p < Q/(norm c*
        primeSurrogate (primeBinPrefix (primaryPrimeFactors d) bin h) bin ell)) := by
  unfold stoppedSideTest
  rw [stoppingSideTest_free_distinguished_interval bin ell j k Z hc d p hell hS,
    failedStage_free_distinguished_interval hc hE]

end CubicFirstMoment

end

end OAI
