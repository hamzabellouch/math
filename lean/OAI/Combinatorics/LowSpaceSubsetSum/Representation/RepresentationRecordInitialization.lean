import OAI.Combinatorics.LowSpaceSubsetSum.Streams.MeasuredRow
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationRecordSort

namespace OAI

/-! # Concrete measured row initialization for bounded representation records -/

namespace LowSpaceSubsetSum.RepresentationKeys

variable {n : ℕ}

def row (I : Instance n) (F : IndexedMask n) (right : Array (LeafRecord n))
    (p P c : ℤ)
    (hs : FilteredRow.PrimarySorted right (fun x => (leafWeight I F x).1) p)
    (mode : FilteredStream.Mode) (x : LeafRecord n) :
    PairCursor.State (LeafRecord n) right.size × ℕ :=
  FilteredStream.measuredRow right (leafWeight I F) (leafWeight I F) p P c hs mode x

theorem row_value (I : Instance n) (F : IndexedMask n) (right : Array (LeafRecord n))
    (p P c : ℤ)
    (hs : FilteredRow.PrimarySorted right (fun x => (leafWeight I F x).1) p)
    (mode : FilteredStream.Mode) (x : LeafRecord n) :
    (row I F right p P c hs mode x).1 =
      FilteredStream.row right (fun x => (leafWeight I F x).1)
        (fun x => (leafWeight I F x).1) p P c hs mode x :=
  FilteredStream.measuredRow_value _ _ _ _ _ _ _ _ _

private theorem leaf_scale (I : Instance n) (F : IndexedMask n)
    (x : LeafRecord n) (hn : 10000 ≤ n) :
    (leafWeight I F x).2 ≤ inputScale I ^ 3 := by
  have hnu : n + 1 ≤ inputScale I := by unfold inputScale; omega
  have hu : 10000 ≤ inputScale I := by omega
  have hs := Nat.pow_le_pow_left hnu 2
  have hm := Nat.mul_le_mul_right (inputScale I ^ 2) (show 32 ≤ inputScale I by omega)
  have hp : 32 * (n + 1) ^ 2 ≤ inputScale I ^ 3 := by nlinarith only [hs, hm]
  exact (leafWeight_work I F x).trans hp

private theorem row_polynomial {n u : ℕ} (hn : n + 1 ≤ u) (hu : 10000 ≤ u) :
    3 * (u ^ 3 + 12) * (n + 1) + u ^ 3 + 16 ≤ u ^ 5 := by
  have hp : 12 ≤ u ^ 3 := by
    calc
      12 ≤ 10000 ^ 3 := by norm_num
      _ ≤ u ^ 3 := Nat.pow_le_pow_left hu 3
  have hmul := Nat.mul_le_mul (show 3 * (u ^ 3 + 12) ≤ 6 * u ^ 3 by omega) hn
  have hu3 : u ^ 3 ≤ u ^ 4 := by
    calc
      _ = u ^ 3 * 1 := by omega
      _ ≤ u ^ 3 * u := Nat.mul_le_mul_left _ (by omega)
      _ = _ := (pow_succ u 3).symm
  have h16 : 16 ≤ u ^ 4 := by
    calc
      16 ≤ 10000 ^ 4 := by norm_num
      _ ≤ u ^ 4 := Nat.pow_le_pow_left hu 4
  have hpow : 8 * u ^ 4 ≤ u ^ 5 := by
    calc
      _ ≤ u * u ^ 4 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' u 4).symm
  have heq : 6 * u ^ 3 * u = 6 * u ^ 4 := by ring
  rw [heq] at hmul
  omega

theorem row_scale (I : Instance n) (F : IndexedMask n) (right : Array (LeafRecord n))
    (p P c : ℤ)
    (hs : FilteredRow.PrimarySorted right (fun x => (leafWeight I F x).1) p)
    (mode : FilteredStream.Mode) (x : LeafRecord n)
    (hn : 10000 ≤ n) (hsize : right.size ≤ 2 ^ n) :
    (row I F right p P c hs mode x).2 ≤ inputScale I ^ 5 := by
  have hw := FilteredStream.measuredRow_work right (leafWeight I F) (leafWeight I F)
    p P c hs mode x (inputScale I ^ 3) (fun y => leaf_scale I F y hn)
    (fun y => leaf_scale I F y hn)
  have hsteps := FilteredStream.steps_le_index_bits right.size n hsize
  have hb := Nat.mul_le_mul_left (3 * (inputScale I ^ 3 + 12)) hsteps
  have hnu : n + 1 ≤ inputScale I := by unfold inputScale; omega
  have hp := row_polynomial hnu (show 10000 ≤ inputScale I by omega)
  exact hw.trans ((Nat.add_le_add_right (Nat.add_le_add_right hb _) _).trans hp)

theorem parent_leafWeight_value (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (j : Fin 2) (x : LeafRecord n) :
    (leafWeight D.input F x).1 = (D.pair j).wl x.semantic := by
  rw [leafWeight_value, hF]
  rfl

def parentRow (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (j : Fin 2) (x : LeafRecord n) :
    PairCursor.State (LeafRecord n) (D.pair j).rightRecords.size × ℕ :=
  have hs : FilteredRow.PrimarySorted (D.pair j).rightRecords
      (fun x => (leafWeight D.input F x).1) D.lowModulus := by
    simpa only [parent_leafWeight_value D F hF j, RepresentationPairData.rightRecords, RepresentationParentData.pair] using
      (ResidueSort.primary (D.pair j).rawRightRecords
        (fun x => (D.pair j).wl x.semantic) D.lowModulus D.modulus)
  row D.input F (D.pair j).rightRecords D.lowModulus D.modulus
    ((D.pair j).residue) hs ((D.pair j).mode) x

theorem parentRow_value (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (j : Fin 2) (x : LeafRecord n) :
    (parentRow D F hF j x).1 = FilteredStream.row (D.pair j).rightRecords
      (fun x => (D.pair j).wl x.semantic) (fun x => (D.pair j).wl x.semantic)
      D.lowModulus D.modulus ((D.pair j).residue)
      (ResidueSort.primary (D.pair j).rawRightRecords
        (fun x => (D.pair j).wl x.semantic) D.lowModulus D.modulus)
      ((D.pair j).mode) x := by
  simp only [parentRow, row_value, parent_leafWeight_value D F hF j]

theorem parentRow_scale (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (j : Fin 2) (x : LeafRecord n)
    (hn : 10000 ≤ n) (hsize : (D.pair j).rightRecords.size ≤ 2 ^ n) :
    (parentRow D F hF j x).2 ≤ inputScale D.input ^ 5 := by
  exact row_scale _ _ _ _ _ _ _ _ _ hn hsize

end LowSpaceSubsetSum.RepresentationKeys

end OAI
