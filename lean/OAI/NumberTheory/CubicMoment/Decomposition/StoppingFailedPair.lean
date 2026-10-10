import OAI.NumberTheory.CubicMoment.Decomposition.StoppingFailedStage
import OAI.NumberTheory.CubicMoment.Estimates.PrimeStoppingPairs

namespace OAI

/-! The late-stage failure condition is exactly a predicate on the
selected divisor, even before restricting the original support. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma stoppedSideTest_late_boundary (bin : Eisenstein → ℕ) (ell : ℕ → ℝ)
    {j k h : ℕ} {Z Q : ℝ} (hQZ : Q ≤ Z) {r d : Eisenstein}
    (hs : stoppedSideTest bin ell j k h Z Q false r d) : h ≤ j := by
  have hstop : stoppingSideTest bin ell j k Z r d := hs.1
  have hfailed : norm r*primeSurrogate
      (primeBinPrefix (primaryPrimeFactors d) bin h) bin ell < Q := by
    simpa only [Bool.false_eq_true, false_or] using hs.2
  by_contra hh
  have hjh : j < h := by omega
  have hp : primeBinPrefix (primaryPrimeFactors d) bin h = primaryPrimeFactors d := by
    apply Finset.filter_eq_self.mpr
    intro p hp
    exact (hstop.1 p hp).trans_lt hjh
  rw [hp] at hfailed
  exact (not_lt_of_ge (hQZ.trans hstop.2.2.2)) hfailed

theorem stoppedSideTest_failed_pair_iff {d e r : Eisenstein}
    (hd : primary d) (he : primary e) (hs : Squarefree (d*e))
    (bin : Eisenstein → ℕ) (ell : ℕ → ℝ) (hell : ∀ j, 1 ≤ ell j)
    (j k l h : ℕ) (Z Q : ℝ) (hQZ : Q ≤ Z)
    (hrem : stoppingRemainingTest bin j l e) :
    stoppedSideTest bin ell j k h Z Q false r d ↔
      stoppingSideTest bin ell j k Z r d ∧
        norm r*primeSurrogate (primeBinPrefix (primaryPrimeFactors (d*e)) bin h)
          bin ell < Q := by
  constructor
  · intro hlate
    have hstop : stoppingSideTest bin ell j k Z r d := hlate.1
    have hhj := stoppedSideTest_late_boundary bin ell hQZ hlate
    obtain ⟨t,ht,hprod,_,_,_⟩ :=
      stopping_pair_reconstruction hd he hs bin ell j k l Z hstop hrem
    have hp : ∀ p ∈ primaryPrimeFactors (d*e), primaryPrime p :=
      fun p hp => (primaryPrimeFactor_spec (primary_mul hd he) hp).1
    have hf := stoppedSideTest_selected_failed_prefix (primaryPrimeFactors (d*e))
      hp bin ell (h := h) (j := j) (k := k) hhj (Finset.mem_powersetCard.mp ht).1 Z Q r
    rw [hprod] at hf
    exact hf.mp hlate
  · rintro ⟨hstop,hfailed⟩
    obtain ⟨t,ht,hprod,_,_,_⟩ :=
      stopping_pair_reconstruction hd he hs bin ell j k l Z hstop hrem
    have hp : ∀ p ∈ primaryPrimeFactors (d*e), primaryPrime p :=
      fun p hp => (primaryPrimeFactor_spec (primary_mul hd he) hp).1
    have hf := stoppedSideTest_selected_of_failed_prefix (primaryPrimeFactors (d*e))
      hp bin ell hell (h := h) (j := j) (k := k) (Finset.mem_powersetCard.mp ht).1 Z Q r hfailed hQZ
    rw [hprod] at hf
    exact hf.mpr hstop

end CubicFirstMoment

end

end OAI
