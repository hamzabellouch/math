import OAI.Combinatorics.LowSpaceSubsetSum.Storage.StoredRecordCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.MeasuredFilterCells
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationKeyCells
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationStoredArrays

namespace OAI

/-! # Prefix filtering while retaining bounded stored records

Membership tests scan the existing index lists. The filter uses the actual
tail accumulator; its input, output, and final array share record payloads.
The cell annotation also bounds a copying implementation of those payloads.
-/

namespace LowSpaceSubsetSum.StoredArrayCells

variable {n : ℕ}

def compatibleAcc (ones zeros domain selected : IndexedMask n) :
    List (Fin n) → (Bool × ℕ) × ℕ
  | [] => ((true, 1), 4)
  | i :: xs =>
    let o := RepresentationKeyCells.member i ones.indices
    let z := RepresentationKeyCells.member i zeros.indices
    let d := RepresentationKeyCells.member i domain.indices
    let s := RepresentationKeyCells.member i selected.indices
    let r := compatibleAcc ones zeros domain selected xs
    let value := ((!(o.1.1 && d.1.1) || s.1.1) && !(z.1.1 && s.1.1)) && r.1.1
    ((value, o.1.2 + z.1.2 + d.1.2 + s.1.2 + r.1.2 + 8),
      max o.2 (max (z.2+4) (max (d.2+8) (max (s.2+12) (r.2+16)))))

theorem compatibleAcc_value (ones zeros domain selected : IndexedMask n) (xs : List (Fin n)) :
    (compatibleAcc ones zeros domain selected xs).1 =
      IndexedMask.compatibleAcc ones zeros domain selected xs := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    simp only [compatibleAcc, IndexedMask.compatibleAcc, RepresentationKeyCells.member_value, ih]

theorem compatibleAcc_cells (ones zeros domain selected : IndexedMask n) (xs : List (Fin n)) :
    (compatibleAcc ones zeros domain selected xs).2 ≤ 16*xs.length + 2*n + 20 := by
  induction xs with
  | nil => simp [compatibleAcc]
  | cons i xs ih =>
    have ho := RepresentationKeyCells.member_cells i ones.indices
    have hz := RepresentationKeyCells.member_cells i zeros.indices
    have hd := RepresentationKeyCells.member_cells i domain.indices
    have hs := RepresentationKeyCells.member_cells i selected.indices
    have h₁ := ones.length_le
    have h₂ := zeros.length_le
    have h₃ := domain.length_le
    have h₄ := selected.length_le
    simp only [compatibleAcc, List.length_cons]
    omega

def compatible (ones zeros domain selected : IndexedMask n) : (Bool × ℕ) × ℕ :=
  let r := compatibleAcc ones zeros domain selected (List.finRange n)
  ((r.1.1, r.1.2+n+1), r.2+2*n+4)

theorem compatible_value (ones zeros domain selected : IndexedMask n) :
    (compatible ones zeros domain selected).1 = IndexedMask.compatible ones zeros domain selected := by
  simp only [compatible, IndexedMask.compatible, compatibleAcc_value]

theorem compatible_cells (ones zeros domain selected : IndexedMask n) :
    (compatible ones zeros domain selected).2 ≤ 20*n+24 := by
  have h := compatibleAcc_cells ones zeros domain selected (List.finRange n)
  simp only [List.length_finRange] at h
  change _+2*n+4 ≤ _
  omega

def array (L : RepresentationLeaf (Fin n)) (ones zeros domain : IndexedMask n) :
    (Array (LeafRecord n) × ℕ) × ℕ :=
  let r := StoredRecordCells.run L
  let a := MeasuredFilterCells.run (fun x => compatible ones zeros domain x.top) r.1.1
  ((a.1.1.toArray, r.1.2+a.1.2+a.1.1.length),
    r.2+a.2+(6*n+12)*(r.1.1.length+1)+16*(n+1))

theorem array_value (L : RepresentationLeaf (Fin n)) (ones zeros domain : IndexedMask n) :
    (array L ones zeros domain).1 = L.measuredStoredArray ones zeros domain := by
  simp only [array, StoredRecordCells.run_value, MeasuredFilterCells.run_value,
    compatible_value, RepresentationLeaf.measuredStoredArray, MeasuredFilter.array]
  congr 1; omega

theorem array_cells (I : Instance n) (L : RepresentationLeaf (Fin n))
    (ones zeros domain : IndexedMask n) (hn : 10000 ≤ n) :
    (array L ones zeros domain).2 ≤ inputScale I ^ 6 * (L.occurrences.card+1) := by
  have hg := StoredRecordCells.run_cells I L hn
  have hf := MeasuredFilterCells.run_cells
    (fun x : LeafRecord n => compatible ones zeros domain x.top) (20*n+24)
    (fun x => compatible_cells ones zeros domain x.top) (StoredRecordCells.run L).1.1
  have hl : (StoredRecordCells.run L).1.1.length = L.occurrences.card := by
    rw [StoredRecordCells.run_value, RepresentationLeaf.measuredStoredRecords_value,
      RepresentationLeaf.storedRecords_length]
  rw [hl] at hf
  have hu : n+2 ≤ inputScale I := by unfold inputScale; omega
  have hu0 : 10000 ≤ inputScale I := by omega
  have hp2 : 44*inputScale I ≤ inputScale I^5 := by
    have hsq : 44 ≤ inputScale I^4 := by
      have h := Nat.pow_le_pow_left hu0 4
      omega
    calc
      _ ≤ inputScale I^4 * inputScale I := Nat.mul_le_mul_right _ hsq
      _ = _ := by rw [← pow_succ]
  have hsmall : 2*L.occurrences.card+20*n+28+(6*n+12)*(L.occurrences.card+1)+16*(n+1) ≤
      44*inputScale I*(L.occurrences.card+1) := by
    have h := Nat.mul_le_mul_right (L.occurrences.card+1) hu
    nlinarith
  have hcoef : 2*inputScale I^5 ≤ inputScale I^6 := by
    calc
      _ ≤ inputScale I * inputScale I^5 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' _ _).symm
  have hmid := Nat.mul_le_mul_right (L.occurrences.card+1) hp2
  have hlast := Nat.mul_le_mul_right (L.occurrences.card+1) hcoef
  change (StoredRecordCells.run L).2+_+_+_ ≤ _
  rw [hl]
  nlinarith only [hg, hf, hsmall, hmid, hlast]

end LowSpaceSubsetSum.StoredArrayCells

end OAI
