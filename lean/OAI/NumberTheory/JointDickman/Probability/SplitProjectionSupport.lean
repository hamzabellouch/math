import OAI.NumberTheory.JointDickman.Probability.SplitSupport
import OAI.NumberTheory.JointDickman.Probability.OrientedSplitBound

namespace OAI

/-! # Projecting a native oriented split event to the low-prime test -/

namespace JointDickman

open Finset

theorem retained_high_projection {B : ℕ} {Y : ℝ} {A R I U : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) (hR : R ⊆ auxiliaryPrimes B)
    (hd : Disjoint A R) (hI : I ⊆ A) (hU : U ⊆ R)
    (hno : ∀ p ∈ symmDiff A (I ∪ U), Real.log p ≤ Y) :
    I ∩ upperAdditionPrimes B Y = A ∩ upperAdditionPrimes B Y ∧
      U ∩ upperAdditionPrimes B Y = ∅ := by
  obtain ⟨hi, hu⟩ := no_high_changes_retained_added hd hI hU hno
  rw [selected_upperAdditionPrimes (hI.trans hA), selected_upperAdditionPrimes hA,
    selected_upperAdditionPrimes (hU.trans hR)]
  exact ⟨hi, hu⟩

theorem retained_low_high_union {B : ℕ} {Y : ℝ} {A I : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) (hI : I ⊆ A)
    (hhigh : I ∩ upperAdditionPrimes B Y = A ∩ upperAdditionPrimes B Y) :
    (I ∩ (A ∩ additionPrimes B Y)) ∪ (A ∩ upperAdditionPrimes B Y) = I := by
  have hi : I ∩ (A ∩ additionPrimes B Y) = I ∩ additionPrimes B Y := by
    ext p
    simp only [mem_inter]
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hI h.1, h.2⟩⟩
  rw [hi, ← hhigh]
  exact selected_additionPrimeRanges_union (hI.trans hA)

theorem added_low_projection {B : ℕ} {Y : ℝ} {U : Finset ℕ}
    (hU : U ⊆ auxiliaryPrimes B) (hhigh : U ∩ upperAdditionPrimes B Y = ∅) :
    U ∩ additionPrimes B Y = U := by
  have hh := selected_additionPrimeRanges_union hU (Y := Y)
  rwa [hhigh, union_empty] at hh

/-- The native size-and-ratio event with an oriented changed prime implies
the precise low-addition test used in the conditional small-ball estimate. -/
theorem native_oriented_ratio_test {B T : ℕ} {Y : ℝ}
    {A D R Q I J U V : Finset ℕ}
    (hB : 0 < B) (hA : A ⊆ auxiliaryPrimes B) (hD : D ⊆ auxiliaryPrimes B)
    (hR : R ⊆ auxiliaryPrimes B) (hQ : Q ⊆ auxiliaryPrimes B)
    (hAR : Disjoint A R) (hDQ : Disjoint D Q)
    (hI : I ⊆ A) (hJ : J ⊆ D) (hU : U ⊆ R) (hV : V ⊆ Q)
    (hnoA : ∀ p ∈ symmDiff A (I ∪ U), Real.log p ≤ Y)
    (hnoD : ∀ p ∈ symmDiff D (J ∪ V), Real.log p ≤ Y)
    (hpair : (∏ p ∈ I ∪ U, p, ∏ p ∈ J ∪ V, p) ∈ amplificationCoefficientPairs B T)
    (hadd : ∃ p ∈ (I ∪ U) \ A, Y / 2 < Real.log p) :
    additionRatioTest Y T
      (∏ p ∈ (I ∩ (A ∩ additionPrimes B Y)) ∪ (A ∩ upperAdditionPrimes B Y), p : ℕ)
      (∏ p ∈ (J ∩ (D ∩ additionPrimes B Y)) ∪ (D ∩ upperAdditionPrimes B Y), p : ℕ)
      (U ∩ additionPrimes B Y) (V ∩ additionPrimes B Y) = 1 := by
  classical
  obtain ⟨hIA, hUhi⟩ := retained_high_projection hA hR hAR hI hU hnoA
  obtain ⟨hJD, hVhi⟩ := retained_high_projection hD hQ hDQ hJ hV hnoD
  rw [retained_low_high_union hA hI hIA, retained_low_high_union hD hJ hJD,
    added_low_projection (hU.trans hR) hUhi, added_low_projection (hV.trans hQ) hVhi]
  have hIU : Disjoint I U := hAR.mono hI hU
  have hJV : Disjoint J V := hDQ.mono hJ hV
  obtain ⟨_, _, hlo, hhi⟩ := (mem_amplificationCoefficientPairs hB).mp hpair
  have hlo' : (T : ℝ) * ((∏ p ∈ J, p : ℕ) * (∏ p ∈ V, p : ℕ)) ≤
      (∏ p ∈ I, p : ℕ) * (∏ p ∈ U, p : ℕ) := by
    rw [prod_union hIU, prod_union hJV] at hlo
    exact_mod_cast hlo
  have hhi' : (∏ p ∈ I, p : ℕ) * (∏ p ∈ U, p : ℕ) ≤
      2 * ((T : ℝ) * ((∏ p ∈ J, p : ℕ) * (∏ p ∈ V, p : ℕ))) := by
    rw [prod_union hIU, prod_union hJV] at hhi
    have hh : (∏ p ∈ I, p : ℕ) * (∏ p ∈ U, p : ℕ) <
        2 * (T : ℝ) * ((∏ p ∈ J, p : ℕ) * (∏ p ∈ V, p : ℕ)) := by exact_mod_cast hhi
    nlinarith only [hh]
  have hlarge := addition_product_log_large (auxiliaryPrimes_prime B) (hU.trans hR) hadd hI
  unfold additionRatioTest
  rw [ite_eq_left ⟨hlo', hhi', hlarge.le⟩]

end JointDickman

end OAI
