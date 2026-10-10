import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationInitializationCells
import OAI.Combinatorics.LowSpaceSubsetSum.Search.PreparedReaderContext
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.ParentLiveBounds

namespace OAI

/-! # A prepared shared-array context with its initialization peak -/

namespace LowSpaceSubsetSum.PreparedContextCells

variable {n : ℕ}

private theorem key_eq (I : Instance n) (F : IndexedMask n) (P : ℤ)
    (mode : FilteredStream.Mode) :
    FilteredStream.key (fun x => (RepresentationKeys.leafWeight I F x).1)
      (fun x => (RepresentationKeys.leafWeight I F x).1) P mode =
      (fun x => (RepresentationKeys.pairKey I F P mode x).1) := by
  funext x
  cases mode <;> rfl

def fromArrays (I : Instance n) (F : IndexedMask n) (left right : Array (LeafRecord n))
    (p P c : ℤ)
    (hs : FilteredRow.PrimarySorted right (fun x => (RepresentationKeys.leafWeight I F x).1) p)
    (ht : FilteredRow.SecondarySorted right (fun x => (RepresentationKeys.leafWeight I F x).1) p P)
    (hP : 0 < P) (mode : FilteredStream.Mode) :
    (PreparedReaderContext.Context I F P mode × ℕ) × ℕ :=
  let out := RepresentationInitializationCells.start I F left right p P c hs ht hP mode
  ((⟨right, Nat.clog 2 left.size, MergedReader.rekey (key_eq I F P mode) out.1.1⟩, out.1.2),
    out.2 + ParentLiveState.sharedArrays left right + 32)

theorem fromArrays_value (I : Instance n) (F : IndexedMask n) (left right : Array (LeafRecord n))
    (p P c : ℤ)
    (hs : FilteredRow.PrimarySorted right (fun x => (RepresentationKeys.leafWeight I F x).1) p)
    (ht : FilteredRow.SecondarySorted right (fun x => (RepresentationKeys.leafWeight I F x).1) p P)
    (hP : 0 < P) (mode : FilteredStream.Mode) :
    (fromArrays I F left right p P c hs ht hP mode).1 =
      PreparedReaderContext.fromArrays I F left right p P c hs ht hP mode := by
  simp only [fromArrays, RepresentationInitializationCells.start_value, PreparedReaderContext.fromArrays]

theorem fromArrays_cells (I : Instance n) (F : IndexedMask n) (left right : Array (LeafRecord n))
    (p P c : ℤ)
    (hs : FilteredRow.PrimarySorted right (fun x => (RepresentationKeys.leafWeight I F x).1) p)
    (ht : FilteredRow.SecondarySorted right (fun x => (RepresentationKeys.leafWeight I F x).1) p P)
    (hP : 0 < P) (mode : FilteredStream.Mode) (C : ℕ) (hn : 10000 ≤ n)
    (hL : left.size ≤ C) (hR : right.size ≤ C) (hC : C ≤ 2 ^ n) :
    (fromArrays I F left right p P c hs ht hP mode).2 ≤ inputScale I ^ 7 * (C + 1) := by
  have hi := RepresentationInitializationCells.start_cells I F left right p P c hs ht hP mode C hn hL hC
  have hs := ParentLiveBounds.shared_le I C left right hL hR
  have hu : 10000 ≤ inputScale I := by unfold inputScale; omega
  have hsmall : 8 * inputScale I + 32 ≤ inputScale I ^ 6 := by
    have h : inputScale I ≤ inputScale I ^ 5 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ inputScale I) (by decide : 1 ≤ 5)
    have hm := Nat.mul_le_mul_right (inputScale I) h
    nlinarith only [h, hm, hu]
  have hm : 2 * inputScale I ^ 6 ≤ inputScale I ^ 7 := by
    calc
      _ ≤ inputScale I * inputScale I ^ 6 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' _ _).symm
  have ha := Nat.mul_le_mul_right (C + 1) hsmall
  have hb := Nat.mul_le_mul_right (C + 1) hm
  change _ + _ + 32 ≤ _
  nlinarith only [hi, hs, ha, hb]

end LowSpaceSubsetSum.PreparedContextCells

end OAI
