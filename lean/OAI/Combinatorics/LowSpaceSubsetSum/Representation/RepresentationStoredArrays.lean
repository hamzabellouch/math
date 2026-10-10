import OAI.Combinatorics.LowSpaceSubsetSum.Storage.StoredPrefixFilter
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationRecordSort

namespace OAI

/-! # Measured stored-array preparation with concrete prefix predicates -/

namespace LowSpaceSubsetSum
namespace IndexedMask

variable {n : ℕ}

def measuredDomain (V : Finset (Fin n)) : IndexedMask n × ℕ :=
  let r := RepresentationLeaf.domainSort V
  (⟨r.1, by rw [RepresentationLeaf.domainSort_length]; simpa using Finset.card_le_univ V⟩, r.2)

theorem measuredDomain_semantic (V : Finset (Fin n)) :
    (measuredDomain V).1.semantic = V := by
  simp only [measuredDomain, semantic, RepresentationLeaf.domainSort_value, Finset.sort_toFinset]

theorem measuredDomain_work (V : Finset (Fin n)) :
    (measuredDomain V).2 ≤ 8 * (n + 1) ^ 2 := RepresentationLeaf.domainSort_work V

end IndexedMask

namespace RepresentationLeaf

variable {n : ℕ}

def measuredStoredArray (L : RepresentationLeaf (Fin n))
    (ones zeros domain : IndexedMask n) : Array (LeafRecord n) × ℕ :=
  let r := L.measuredStoredRecords
  let a := MeasuredFilter.array (fun x => IndexedMask.compatible ones zeros domain x.top) r.1
  (a.1, r.2 + a.2)

theorem measuredStoredArray_value (L : RepresentationLeaf (Fin n))
    (ones zeros domain : IndexedMask n) :
    (L.measuredStoredArray ones zeros domain).1 =
      (L.storedRecords.filter (fun x =>
        (MaskRestriction.mk ones.semantic zeros.semantic).accept domain.semantic x.top.semantic)).toArray := by
  simp only [measuredStoredArray, MeasuredFilter.array_value, measuredStoredRecords_value,
    IndexedMask.compatible_value]

theorem measuredStoredArray_size (L : RepresentationLeaf (Fin n))
    (ones zeros domain : IndexedMask n) :
    (L.measuredStoredArray ones zeros domain).1.size ≤ L.occurrences.card := by
  rw [measuredStoredArray_value]
  simpa only [List.size_toArray, storedRecords_length] using
    List.length_filter_le (fun x =>
      (MaskRestriction.mk ones.semantic zeros.semantic).accept domain.semantic x.top.semantic)
      L.storedRecords

theorem measuredStoredArray_work (I : Instance n) (L : RepresentationLeaf (Fin n))
    (ones zeros domain : IndexedMask n) (hn : 10000 ≤ n) :
    (L.measuredStoredArray ones zeros domain).2 ≤ inputScale I ^ 4 * (L.occurrences.card + 1) := by
  have hg := L.measuredStoredRecords_scale I hn
  have hf := MeasuredFilter.array_work
    (fun x : LeafRecord n => IndexedMask.compatible ones zeros domain x.top)
    (inputScale I ^ 3) (fun x => IndexedMask.compatible_scale I ones zeros domain x.top hn)
    L.measuredStoredRecords.1
  have hl : L.measuredStoredRecords.1.length = L.occurrences.card := by
    rw [measuredStoredRecords_value, storedRecords_length]
  rw [hl] at hf
  have hu : 10000 ≤ inputScale I := by unfold inputScale; omega
  have hp : 3 * inputScale I ^ 3 ≤ inputScale I ^ 4 := by
    calc
      _ ≤ inputScale I * inputScale I ^ 3 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' _ _).symm
  have h5 : 5 ≤ inputScale I ^ 3 := by
    have := Nat.pow_le_pow_left hu 3
    omega
  have ht := Nat.mul_le_mul_right (L.occurrences.card + 1) hp
  change _ + _ ≤ _
  nlinarith only [hg, hf, ht, h5]

end RepresentationLeaf

namespace RepresentationStoredArrays

variable {n : ℕ}

/-- Shared arrays are returned once. The caller retains them through row
initialization and all later reads. The mask equalities are proof arguments. -/
def prepare (D : RepresentationParentData n) (F ones zeros : IndexedMask n) (j : Fin 2) :
    (Array (LeafRecord n) × Array (LeafRecord n)) × ℕ :=
  let dl := IndexedMask.measuredDomain (D.pair j).left.top
  let dr := IndexedMask.measuredDomain (D.pair j).right.top
  let l := (D.pair j).left.measuredStoredArray ones zeros dl.1
  let r := (D.pair j).right.measuredStoredArray ones zeros dr.1
  let s := RepresentationKeys.sort D.input F D.lowModulus D.modulus r.1
  ((l.1, s.1), dl.2 + dr.2 + l.2 + r.2 + s.2)

private theorem left_value (D : RepresentationParentData n) (ones zeros : IndexedMask n)
    (hones : ones.semantic = D.maskRestriction.ones)
    (hzeros : zeros.semantic = D.maskRestriction.zeros) (j : Fin 2) :
    ((D.pair j).left.measuredStoredArray ones zeros
      (IndexedMask.measuredDomain (D.pair j).left.top).1).1 = (D.pair j).leftRecords := by
  rw [RepresentationLeaf.measuredStoredArray_value, IndexedMask.measuredDomain_semantic, hones, hzeros]
  rfl

private theorem right_value (D : RepresentationParentData n) (ones zeros : IndexedMask n)
    (hones : ones.semantic = D.maskRestriction.ones)
    (hzeros : zeros.semantic = D.maskRestriction.zeros) (j : Fin 2) :
    ((D.pair j).right.measuredStoredArray ones zeros
      (IndexedMask.measuredDomain (D.pair j).right.top).1).1 = (D.pair j).rawRightRecords := by
  rw [RepresentationLeaf.measuredStoredArray_value, IndexedMask.measuredDomain_semantic, hones, hzeros]
  rfl

theorem prepare_value (D : RepresentationParentData n) (F ones zeros : IndexedMask n)
    (hF : F.semantic = D.signs) (hones : ones.semantic = D.maskRestriction.ones)
    (hzeros : zeros.semantic = D.maskRestriction.zeros) (j : Fin 2) :
    (prepare D F ones zeros j).1 = ((D.pair j).leftRecords, (D.pair j).rightRecords) := by
  simp only [prepare, left_value D ones zeros hones hzeros j,
    right_value D ones zeros hones hzeros j, RepresentationKeys.sort_value, hF]
  rfl

theorem prepare_sizes (D : RepresentationParentData n) (F ones zeros : IndexedMask n) (j : Fin 2) :
    (prepare D F ones zeros j).1.1.size ≤ (D.pair j).left.occurrences.card ∧
      (prepare D F ones zeros j).1.2.size ≤ (D.pair j).right.occurrences.card := by
  constructor
  · exact (D.pair j).left.measuredStoredArray_size ones zeros
      (IndexedMask.measuredDomain (D.pair j).left.top).1
  · simpa only [prepare, RepresentationKeys.sort_value, ResidueSort.size] using
      (D.pair j).right.measuredStoredArray_size ones zeros
        (IndexedMask.measuredDomain (D.pair j).right.top).1

theorem prepare_work (D : RepresentationParentData n) (F ones zeros : IndexedMask n)
    (j : Fin 2) (C : ℕ) (hn : 10000 ≤ n)
    (hl : (D.pair j).left.occurrences.card ≤ C)
    (hr : (D.pair j).right.occurrences.card ≤ C) (hC : C ≤ 2 ^ n) :
    (prepare D F ones zeros j).2 ≤ inputScale D.input ^ 6 * (C + 1) := by
  let L := (D.pair j).left
  let R := (D.pair j).right
  let dl := (IndexedMask.measuredDomain L.top).1
  let dr := (IndexedMask.measuredDomain R.top).1
  have hdl := IndexedMask.measuredDomain_work L.top
  have hdr := IndexedMask.measuredDomain_work R.top
  have hal := L.measuredStoredArray_work D.input ones zeros dl hn
  have har := R.measuredStoredArray_work D.input ones zeros dr hn
  have hs := RepresentationKeys.sort_scale D.input F D.lowModulus D.modulus
    (R.measuredStoredArray ones zeros dr).1 hn
    ((R.measuredStoredArray_size ones zeros dr).trans hr) hC
  have hnu : n + 1 ≤ inputScale D.input := by unfold inputScale; omega
  have hu : 10000 ≤ inputScale D.input := by omega
  have hp2 := Nat.pow_le_pow_left hnu 2
  have hp25 : inputScale D.input ^ 2 ≤ inputScale D.input ^ 5 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have hp45 : inputScale D.input ^ 4 ≤ inputScale D.input ^ 5 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have h6 : 20 * inputScale D.input ^ 5 ≤ inputScale D.input ^ 6 := by
    calc
      _ ≤ inputScale D.input * inputScale D.input ^ 5 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' _ _).symm
  have hla := hal.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right hl 1))
  have hra := har.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right hr 1))
  have ht := Nat.mul_le_mul_right (C + 1) h6
  have h45C := Nat.mul_le_mul_right (C + 1) hp45
  have hpos : 1 ≤ C + 1 := by omega
  have hconst := Nat.mul_le_mul_left (16 * inputScale D.input ^ 5) hpos
  change _ + _ + _ + _ + _ ≤ _
  nlinarith only [hdl, hdr, hs, hla, hra, hp2, hp25, h45C, ht, hconst]

end RepresentationStoredArrays
end LowSpaceSubsetSum

end OAI
