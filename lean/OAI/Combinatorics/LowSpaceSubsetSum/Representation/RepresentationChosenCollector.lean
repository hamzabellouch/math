import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationBucketCapacity
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.ParentPrefixSearch

namespace OAI

/-! # Chosen entries in the completed arrays on the actual prefix path -/

noncomputable section

namespace LowSpaceSubsetSum

namespace MaskRestriction

variable {n : ℕ}

theorem mem_follow_ones (P : MaskRestriction n) (order : List (Fin n))
    (S : Finset (Fin n)) (i : Fin n) :
    i ∈ (P.follow order S).ones ↔ i ∈ P.ones ∨ i ∈ order ∧ i ∈ S := by
  induction order generalizing P with
  | nil => simp [follow]
  | cons j order ih =>
    change i ∈ ((P.force j (decide (j ∈ S))).follow order S).ones ↔ _
    rw [ih]
    by_cases hij : i = j
    · subst i
      by_cases hj : j ∈ S <;> simp [hj, force]
    · by_cases hj : j ∈ S <;> simp [hj, force, hij]

theorem mem_follow_zeros (P : MaskRestriction n) (order : List (Fin n))
    (S : Finset (Fin n)) (i : Fin n) :
    i ∈ (P.follow order S).zeros ↔ i ∈ P.zeros ∨ i ∈ order ∧ i ∉ S := by
  induction order generalizing P with
  | nil => simp [follow]
  | cons j order ih =>
    change i ∈ ((P.force j (decide (j ∈ S))).follow order S).zeros ↔ _
    rw [ih]
    by_cases hij : i = j
    · subst i
      by_cases hj : j ∈ S <;> simp [hj, force]
    · by_cases hj : j ∈ S <;> simp [hj, force, hij]

/-- After all domain coordinates have been forced, a compatible mask is
exactly the mask defining the path. Repeated coordinates cause no problem. -/
theorem follow_compatible_eq (P : MaskRestriction n) (order : List (Fin n))
    (A S T : Finset (Fin n)) (hcover : ∀ i ∈ A, i ∈ order)
    (hS : S ⊆ A) (hT : T ⊆ A) (hc : (P.follow order S).Compatible A T) : T = S := by
  apply Finset.Subset.antisymm
  · intro i hi
    by_contra hn
    exact Finset.disjoint_left.mp hc.2
      ((mem_follow_zeros P order S i).mpr (Or.inr ⟨hcover i (hT hi), hn⟩)) hi
  · intro i hi
    exact hc.1 (Finset.mem_inter.mpr
      ⟨(mem_follow_ones P order S i).mpr (Or.inr ⟨hcover i (hS hi), hi⟩), hS hi⟩)

/-- Following the membership bits of a mask preserves its compatibility. -/
theorem follow_compatible (P : MaskRestriction n) (order : List (Fin n))
    (A S : Finset (Fin n)) (hP : P.Compatible A S) :
    (P.follow order S).Compatible A S := by
  induction order generalizing P with
  | nil => exact hP
  | cons i order ih =>
    exact ih (P.force i (decide (i ∈ S))) (P.force_compatible A S hP i)

end MaskRestriction

namespace RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

def chosenEntry (h : R.PrimeHistory) (r : R.Residues h.2) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000) (j : Fin 2) :
    Entry (Fin n) :=
  RepresentationUniverse.entry (R.signedWeights h.1.1.1) (R.chosenRawParent h r hn hlog j)

theorem chosenEntry_mask_subset (h : R.PrimeHistory) (r : R.Residues h.2) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hr : R.ResidueSuccess (R.actualOffsets (R.allocatedChildAssignment hn hlog)) h r) (j : Fin 2) :
    (R.chosenEntry h r hn hlog j).mask ⊆ R.orderedMixers h.1.1.1 0 :=
  (R.rawEntry_mask_spec _ _ _ _ j _
    (R.chosenLowEntries_subset h r hn hlog j (R.chosenEntry_lowEntries h r hn hlog hr j))).1

/-- Completion, rather than any unproved universe-cardinality estimate,
suffices for exact membership at an intermediate compatible prefix. -/
theorem chosenEntry_mem_completed (h : R.PrimeHistory) (r : R.Residues h.2)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hr : R.ResidueSuccess (R.actualOffsets (R.allocatedChildAssignment hn hlog)) h r)
    (j : Fin 2) (P : ℤ) (hP : 0 < P) (B : ℕ) (restriction : MaskRestriction n)
    (hcompat : restriction.Compatible (R.orderedMixers h.1.1.1 0)
      (R.chosenEntry h r hn hlog j).mask)
    (hc : ((R.chosenParentData h r hn hlog j P hP (compressionDictionaryCapacity n)
      restriction).collect B).state.user.keys.overflow = false) :
    R.chosenEntry h r hn hlog j ∈ ((R.chosenParentData h r hn hlog j P hP
      (compressionDictionaryCapacity n) restriction).entries B).toList := by
  let D := R.chosenParentData h r hn hlog j P hP (compressionDictionaryCapacity n) restriction
  apply (D.entries_mem_iff_of_complete B hc ?_ _).mpr
  · apply R.chosenEntry_rawEntries h r hn hlog hr j P hP _ restriction
    simpa only [chosenEntry, RepresentationUniverse.entry, R.chosenRawParent_topMask h r hn hlog hr j]
      using hcompat
  · intro e he
    exact R.raw_validEntries_bounded _ _ _ _ j e
      (Finset.mem_filter.mp (R.chosenParent_rawEntries_subset h r hn hlog j P hP _ restriction e he)).1

/-- The fully forced right task emits only the designated full mask, so its
capacity is bounded by the actual full-mask bucket from the extra-prime lemma. -/
theorem chosenRight_full_follow_fits (h : R.PrimeHistory) (r : R.Residues h.2)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hr : R.ResidueSuccess (R.actualOffsets (R.allocatedChildAssignment hn hlog)) h r)
    (q : ℕ) (hP : 0 < (prefixModulus h.2.val 0 : ℤ) * q) (B : ℕ)
    (order : List (Fin n)) (hcover : ∀ i ∈ R.orderedMixers h.1.1.1 0, i ∈ order)
    (hcap : ((R.chosenParentBucket h r hn hlog 1 ((prefixModulus h.2.val 0 : ℤ) * q)).filter
      (fun e => e.mask = (R.chosenEntry h r hn hlog 1).mask)).card ≤
        compressionDictionaryCapacity n) :
    ((R.chosenParentData h r hn hlog 1 ((prefixModulus h.2.val 0 : ℤ) * q) hP
      (compressionDictionaryCapacity n)
      (MaskRestriction.empty.follow order (R.chosenEntry h r hn hlog 1).mask)).collect B).state.user.keys.overflow = false := by
  let S := (R.chosenEntry h r hn hlog 1).mask
  let restriction := MaskRestriction.empty.follow order S
  let D := R.chosenParentData h r hn hlog 1 ((prefixModulus h.2.val 0 : ℤ) * q) hP
    (compressionDictionaryCapacity n) restriction
  let U := (R.chosenParentBucket h r hn hlog 1 ((prefixModulus h.2.val 0 : ℤ) * q)).filter
    (fun e => e.mask = S)
  apply (D.collect_fits B U hcap ?_).1
  intro e he
  have hu := R.chosenParent_rawEntries_subset h r hn hlog 1
    ((prefixModulus h.2.val 0 : ℤ) * q) hP _ restriction e he
  apply Finset.mem_filter.mpr
  refine ⟨hu, ?_⟩
  have he_top := (R.rawEntry_mask_spec _ _ _ _ 1 e (Finset.mem_filter.mp hu).1).1
  have hcompatible : restriction.Compatible (R.orderedMixers h.1.1.1 0) e.mask := by
    obtain ⟨x, hx, rfl⟩ := (D.rawEntries_mem e).mp he
    simpa only [D, chosenParentData, R.rawLeaf_topDomain, RepresentationUniverse.entry] using
      D.streams_compatible x.1 x.2 hx.1 hx.2.1
  exact MaskRestriction.follow_compatible_eq MaskRestriction.empty order
    (R.orderedMixers h.1.1.1 0) S e.mask hcover
    (R.chosenEntry_mask_subset h r hn hlog hr 1) he_top hcompatible

end RepresentationSetup
end LowSpaceSubsetSum

end

end OAI
