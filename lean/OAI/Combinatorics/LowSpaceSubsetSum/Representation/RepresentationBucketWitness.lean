import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationPrimeTrial
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationSeparatorParameters
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationBucketProgram

namespace OAI

/-! # The actual designated bucket accepts a covered surviving representation -/

noncomputable section

namespace LowSpaceSubsetSum

private theorem representation_dictionary_pair_size (n : ℕ) (hn : 10 ≤ n) :
    compressionDictionaryCapacity n + 1 + (compressionDictionaryCapacity n + 1) ≤ 2 ^ n := by
  have hC : 0 < compressionDictionaryCapacity n := by
    unfold compressionDictionaryCapacity
    positivity
  have hk : 199 * n / 1000 + 2 ≤ n := by omega
  have hp : 4 * compressionDictionaryCapacity n ≤ 2 ^ n := by
    calc
      _ = 2 ^ (199 * n / 1000 + 2) := by
        rw [pow_add]
        unfold compressionDictionaryCapacity
        ring
      _ ≤ _ := Nat.pow_le_pow_right (by decide) hk
  omega

namespace RepresentationBucketData

/-- Checker completeness over opaque arrays. The stream implementation is
not reduced while applying the separator's fixed-pair theorem. -/
theorem check_finds_fixed_pair {n g : ℕ} (D : RepresentationBucketData n g)
    (families : Fin 4 → Array (Finset (Fin g))) (left right : Array (Entry (Fin n)))
    (hsize : left.toList.length + right.toList.length ≤ 2 ^ n)
    (x y : Entry (Fin n)) (hx : x ∈ left.toList) (hy : y ∈ right.toList)
    (hw : x.value + y.value = D.target)
    (hc : SeparatorCheck.Covered families (D.coordinates.encodeEntry x)
      (D.coordinates.encodeEntry y)) : D.check families left right = true := by
  exact D.coordinates.finds_fixed_pair families D.target left.toList right.toList
    hsize x y hx hy hw hc

/-- Generic prefix completion keeps the implementation opaque while the
application supplies its actual chosen records and capacity bounds. -/
theorem run_complete_of_pair {n g : ℕ} (D : RepresentationBucketData n g)
    (B : ℕ) (families : Fin 4 → Array (Finset (Fin g)))
    (domain : Finset (Fin n)) (x y : Entry (Fin n))
    (hleft : (D.left.collect B).state.user.keys.overflow = false)
    (hx : x ∈ (D.left.entries B).toList)
    (hfull : ({ D.right with maskRestriction :=
      MaskRestriction.empty.follow D.topOrder y.mask }.collect B).state.user.keys.overflow = false)
    (hy : ∀ P, P.Compatible domain y.mask →
      ({ D.right with maskRestriction := P }.collect B).state.user.keys.overflow = false →
        y ∈ ({ D.right with maskRestriction := P }.entries B).toList)
    (hsize : ∀ P, (D.left.entries B).toList.length +
      ({ D.right with maskRestriction := P }.entries B).toList.length ≤ 2 ^ n)
    (hw : x.value + y.value = D.target)
    (hcovered : SeparatorCheck.Covered families (D.coordinates.encodeEntry x)
      (D.coordinates.encodeEntry y)) : D.run B families = true := by
  have hnonempty : (D.left.collect B).state.user.records.isEmpty = false := by
    apply Array.isEmpty_eq_false_iff_exists_mem.mpr
    exact ⟨x, by simpa only [RepresentationParentData.entries, Array.mem_toList_iff] using hx⟩
  let callback : Array (Entry (Fin n)) → Bool := D.check families (D.left.entries B)
  have hfind (P : MaskRestriction n) (hcompat : P.Compatible domain y.mask)
      (hcomplete : ({ D.right with maskRestriction := P }.collect B).state.user.keys.overflow = false) :
      callback ({ D.right with maskRestriction := P }.entries B) = true := by
    have hs := hsize P
    have hyy := hy P hcompat hcomplete
    dsimp only [callback]
    generalize hL : D.left.entries B = left at hx hs ⊢
    generalize hR : ({ D.right with maskRestriction := P }.entries B) = right at hyy hs ⊢
    exact D.check_finds_fixed_pair families left right hs x y hx hyy hw hcovered

  have hsearch := D.right.searchRight_complete B callback domain y.mask hfind
    D.topOrder MaskRestriction.empty (MaskRestriction.empty_compatible _ _) hfull
  simpa only [run, hleft, hnonempty, Bool.false_eq_true, ite_false,
    RepresentationParentData.entries, callback] using hsearch

end RepresentationBucketData

namespace RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

/-- This is one bucket visited by the real residue loop, with the designated
normalized residue used only to name that iteration in the analysis. -/
def chosenBucketData (h : R.PrimeHistory) (r : R.Residues h.2) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (q : ℕ) (hP : 0 < (prefixModulus h.2.val 0 : ℤ) * q) :
    RepresentationBucketData n (2 * blockHalf n 0) where
  left := R.chosenParentData h r hn hlog 0 ((prefixModulus h.2.val 0 : ℤ) * q) hP
    (compressionDictionaryCapacity n) MaskRestriction.empty
  right := R.chosenParentData h r hn hlog 1 ((prefixModulus h.2.val 0 : ℤ) * q) hP
    (compressionDictionaryCapacity n) MaskRestriction.empty
  coordinates := R.topCoordinates h.1.1.1 h.1.2
  topOrder := (R.orderedMixers h.1.1.1 0).sort (· ≤ ·)

theorem chosenBucketData_topOrder (h : R.PrimeHistory) (r : R.Residues h.2)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (q : ℕ) (hP : 0 < (prefixModulus h.2.val 0 : ℤ) * q) :
    (R.chosenBucketData h r hn hlog q hP).topOrder =
      (R.orderedMixers h.1.1.1 0).sort (· ≤ ·) := rfl

theorem chosenBucketData_right_restrict (h : R.PrimeHistory) (r : R.Residues h.2)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (q : ℕ) (hP : 0 < (prefixModulus h.2.val 0 : ℤ) * q) (P : MaskRestriction n) :
    { (R.chosenBucketData h r hn hlog q hP).right with maskRestriction := P } =
      R.chosenParentData h r hn hlog 1 ((prefixModulus h.2.val 0 : ℤ) * q) hP
        (compressionDictionaryCapacity n) P := rfl

/-- The left collector and right prefix recursion both reach the covered
chosen pair. Early completion of a right prefix is sufficient. -/
theorem chosenBucket_accepts (h : R.PrimeHistory) (r : R.Residues h.2)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hr : R.ResidueSuccess (R.actualOffsets (R.allocatedChildAssignment hn hlog)) h r)
    (q : ℕ) (hP : 0 < (prefixModulus h.2.val 0 : ℤ) * q) (B : ℕ)
    (families : Fin 4 → Array (Finset (Fin (2 * blockHalf n 0))))
    (hleft : (R.chosenParentBucket h r hn hlog 0 ((prefixModulus h.2.val 0 : ℤ) * q)).card ≤
      compressionDictionaryCapacity n)
    (hright : ((R.chosenParentBucket h r hn hlog 1 ((prefixModulus h.2.val 0 : ℤ) * q)).filter
      (fun e => e.mask = (R.chosenEntry h r hn hlog 1).mask)).card ≤
        compressionDictionaryCapacity n)
    (hcovered : SeparatorCheck.Covered families
      ((R.topCoordinates h.1.1.1 h.1.2).encodeEntry (R.chosenEntry h r hn hlog 0))
      ((R.topCoordinates h.1.1.1 h.1.2).encodeEntry (R.chosenEntry h r hn hlog 1))) :
    (R.chosenBucketData h r hn hlog q hP).run B families = true := by
  let D := R.chosenBucketData h r hn hlog q hP
  let x := R.chosenEntry h r hn hlog 0
  let y := R.chosenEntry h r hn hlog 1
  have hleftFacts := R.chosenEntry_collected h r hn hlog hr 0
    ((prefixModulus h.2.val 0 : ℤ) * q) hP (compressionDictionaryCapacity n) B
    MaskRestriction.empty (MaskRestriction.empty_compatible _ _) hleft
  apply D.run_complete_of_pair B families (R.orderedMixers h.1.1.1 0) x y
    hleftFacts.1 hleftFacts.2
  · have hfull := R.chosenRight_full_follow_fits h r hn hlog hr q hP B
      ((R.orderedMixers h.1.1.1 0).sort (· ≤ ·))
      (fun i hi => (Finset.mem_sort (· ≤ ·)).mpr hi) hright
    dsimp only [D, y]
    rw [R.chosenBucketData_topOrder, R.chosenBucketData_right_restrict]
    exact hfull
  · intro P hcompat hcomplete
    dsimp only [D] at hcomplete ⊢
    simp only [R.chosenBucketData_right_restrict h r hn hlog q hP P] at hcomplete ⊢
    exact R.chosenEntry_mem_completed h r hn hlog hr 1
      ((prefixModulus h.2.val 0 : ℤ) * q) hP B P hcompat hcomplete
  · intro P
    simp only [Array.length_toList]
    apply (Nat.add_le_add (D.left.storage B).1
      ({ D.right with maskRestriction := P }.storage B).1).trans
    exact representation_dictionary_pair_size n (by omega)
  · exact (R.chosenEntries_match h r hn hlog hr).1
  · exact hcovered

/-- Every chosen exact key has the actual local cardinalities used by the
rounded separator parameter constructor. -/
theorem chosenEntry_separator_count (h : R.PrimeHistory) (r : R.Residues h.2)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hr : R.ResidueSuccess (R.actualOffsets (R.allocatedChildAssignment hn hlog)) h r)
    (j : Fin 2) (i : Fin 4) :
    (SeparatorCheck.localMask i ((R.topCoordinates h.1.1.1 h.1.2).encodeEntry
      (R.chosenEntry h r hn hlog j)).mask).card =
      if j = 0 then (separatorParameters h.1.1.2 (by omega)).c i
      else (2 * blockHalf n 0) / 2 - (separatorParameters h.1.1.2 (by omega)).c i := by
  have hc := R.rawEntry_local_count h.1.1.1 h.1.1.2 h.1.2
    (R.allocatedBackground h.1.1.1 h.1.1.2 hn hlog) j (R.signedWeights h.1.1.1)
    (R.chosenEntry h r hn hlog j)
    (R.chosenLowEntries_subset h r hn hlog j (R.chosenEntry_lowEntries h r hn hlog hr j)) i
  simpa [separatorParameters, SeparatorParameters.rounded] using hc

end RepresentationSetup
end LowSpaceSubsetSum

end

end OAI
