import OAI.NumberTheory.JointDickman.Probability.SplitChangeEvents
import OAI.NumberTheory.JointDickman.Arithmetic.AmplificationPrimeRanges

namespace OAI

/-! # Supports of retained and newly added prime subsets -/

namespace JointDickman

open Finset

theorem remainingSubsetMass_eq_zero {P A R : Finset ℕ} (hd : ¬ Disjoint A R) :
    bernoulliSubsetMass P (remainingPrimeParameter A) R = 0 := by
  classical
  obtain ⟨p, hpA, hpR⟩ := not_disjoint_iff.mp hd
  unfold bernoulliSubsetMass
  have hz : (∏ p ∈ R, remainingPrimeParameter A p) = 0 :=
    prod_eq_zero hpR (by simp only [remainingPrimeParameter, hpA, ite_true])
  rw [hz, zero_mul]

/-- No high coefficient changes force all old high coefficient primes to
be kept and prohibit any high additions. -/
theorem no_high_changes_retained_added {A R I U : Finset ℕ} {Y : ℝ}
    (hd : Disjoint A R) (hI : I ⊆ A) (hU : U ⊆ R)
    (hno : ∀ p ∈ symmDiff A (I ∪ U), Real.log p ≤ Y) :
    highPrimePart Y I = highPrimePart Y A ∧ highPrimePart Y U = ∅ := by
  classical
  constructor
  · ext p
    simp only [highPrimePart, mem_filter]
    constructor
    · rintro ⟨hp, hy⟩
      exact ⟨hI hp, hy⟩
    · rintro ⟨hp, hy⟩
      refine ⟨?_, hy⟩
      by_contra hn
      have hnu : p ∉ U := fun hu => disjoint_left.mp hd hp (hU hu)
      have hm : p ∈ symmDiff A (I ∪ U) :=
        mem_symmDiff.mpr (Or.inl ⟨hp, by simpa only [mem_union, not_or] using And.intro hn hnu⟩)
      exact (not_le_of_gt hy) (hno p hm)
  · apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨hpu, hy⟩ := mem_filter.mp hp
    have hna : p ∉ A := fun ha => disjoint_left.mp hd ha (hU hpu)
    have hm : p ∈ symmDiff A (I ∪ U) :=
      mem_symmDiff.mpr (Or.inr ⟨mem_union_right I hpu, hna⟩)
    exact (not_le_of_gt hy) (hno p hm)

/-- A newly added prime in the top half of the shell forces the whole
addition product to have logarithm greater than Y/2. -/
theorem addition_product_log_large {P A I U : Finset ℕ} {Y : ℝ}
    (hP : ∀ p ∈ P, p.Prime) (hU : U ⊆ P)
    (hadd : ∃ p ∈ (I ∪ U) \ A, Y / 2 < Real.log p) (hI : I ⊆ A) :
    Y / 2 < Real.log (∏ p ∈ U, p : ℕ) := by
  obtain ⟨p, hp, hy⟩ := hadd
  obtain ⟨hpIU, hpA⟩ := mem_sdiff.mp hp
  have hpU : p ∈ U := (mem_union.mp hpIU).elim (fun h => False.elim (hpA (hI h))) id
  have hn : 0 < ∏ p ∈ U, p := prod_pos (fun q hq => (hP q (hU hq)).pos)
  have hle : p ≤ ∏ p ∈ U, p := Nat.le_of_dvd hn (dvd_prod_of_mem (fun p : ℕ => p) hpU)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p (hU hpU)).pos
  exact hy.trans_le (Real.log_le_log hp0 (by exact_mod_cast hle))

end JointDickman

end OAI
