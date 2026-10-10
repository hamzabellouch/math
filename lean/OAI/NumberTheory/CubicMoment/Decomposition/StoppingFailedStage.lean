import OAI.NumberTheory.CubicMoment.Estimates.PrimeStoppingLabels
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedPrimePredicate

namespace OAI

/-! The failed first stage of an ordinary stop is a condition on the
selected divisor alone; this identifies it with the original prefix. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma selected_crossing_after_failed_prefix (s : Finset Eisenstein)
    (bin : Eisenstein → ℕ) (ell : ℕ → ℝ) (hell : ∀ j, 1 ≤ ell j)
    {R Z Q : ℝ} (hR : 0 ≤ R) {h j : ℕ} {t : Finset Eisenstein}
    (ht : t ⊆ primeBin s bin j)
    (hfailed : R*primeSurrogate (primeBinPrefix s bin h) bin ell < Q)
    (hQZ : Q ≤ Z)
    (hhit : Z ≤ R*primeSurrogate (stoppingSelected s bin j t) bin ell) : h ≤ j := by
  by_contra hhj
  have hjh : j < h := by omega
  have hsub : stoppingSelected s bin j t ⊆ primeBinPrefix s bin h := by
    intro p hp
    exact Finset.mem_filter.mpr ⟨stoppingSelected_subset ht hp,
      (stoppingSelected_bins_le ht hp).trans_lt hjh⟩
  have hsur : primeSurrogate (stoppingSelected s bin j t) bin ell ≤
      primeSurrogate (primeBinPrefix s bin h) bin ell := by
    exact Finset.prod_le_prod_of_subset_of_one_le₀ hsub
      (fun p _ => zero_le_one.trans (hell (bin p)))
      (fun p _ _ => hell (bin p))
  have hle := hhit.trans (mul_le_mul_of_nonneg_left hsur hR)
  exact (not_lt_of_ge hle) (hfailed.trans_le hQZ)

lemma stoppedSideTest_selected_failed_prefix (s : Finset Eisenstein)
    (hs : ∀ p ∈ s, primaryPrime p) (bin : Eisenstein → ℕ) (ell : ℕ → ℝ)
    {h j k : ℕ} (hhj : h ≤ j) {t : Finset Eisenstein}
    (ht : t ⊆ primeBin s bin j) (Z Q : ℝ) (r : Eisenstein) :
    stoppedSideTest bin ell j k h Z Q false r (∏ p ∈ stoppingSelected s bin j t, p) ↔
      stoppingSideTest bin ell j k Z r (∏ p ∈ stoppingSelected s bin j t, p) ∧
        norm r*primeSurrogate (primeBinPrefix s bin h) bin ell < Q := by
  have hp : ∀ p ∈ stoppingSelected s bin j t, primaryPrime p :=
    fun p hp => hs p (stoppingSelected_subset ht hp)
  have hprefix : primeBinPrefix
      (primaryPrimeFactors (∏ p ∈ stoppingSelected s bin j t, p)) bin h =
      primeBinPrefix s bin h := by
    rw [primaryPrimeFactors_finset_prod _ hp]
    exact stoppingSelected_earlier_prefix hhj ht
  simp only [stoppedSideTest,Bool.false_eq_true,false_or,hprefix]

/-- On an original term which failed the first threshold, every later
crossing automatically satisfies the selected-side failure predicate. -/
lemma stoppedSideTest_selected_of_failed_prefix (s : Finset Eisenstein)
    (hs : ∀ p ∈ s, primaryPrime p) (bin : Eisenstein → ℕ) (ell : ℕ → ℝ)
    (hell : ∀ j, 1 ≤ ell j) {h j k : ℕ} {t : Finset Eisenstein}
    (ht : t ⊆ primeBin s bin j) (Z Q : ℝ) (r : Eisenstein)
    (hfailed : norm r*primeSurrogate (primeBinPrefix s bin h) bin ell < Q)
    (hQZ : Q ≤ Z) :
    stoppedSideTest bin ell j k h Z Q false r (∏ p ∈ stoppingSelected s bin j t, p) ↔
      stoppingSideTest bin ell j k Z r (∏ p ∈ stoppingSelected s bin j t, p) := by
  constructor
  · exact And.left
  · intro hstop
    have hp : ∀ p ∈ stoppingSelected s bin j t, primaryPrime p :=
      fun p hp => hs p (stoppingSelected_subset ht hp)
    have htest : stoppingPrimeSetTest (stoppingSelected s bin j t) bin ell j k Z r := by
      simpa only [stoppingSideTest,primaryPrimeFactors_finset_prod _ hp] using hstop
    have hhj := selected_crossing_after_failed_prefix s bin ell hell (norm_nonneg r)
      ht hfailed hQZ htest.2.2.2
    exact (stoppedSideTest_selected_failed_prefix s hs bin ell hhj ht Z Q r).mpr
      ⟨hstop,hfailed⟩

end CubicFirstMoment

end

end OAI
