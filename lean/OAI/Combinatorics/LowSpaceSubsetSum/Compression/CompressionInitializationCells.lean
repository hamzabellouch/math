import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionRowCells
import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionReaderCells
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationInitializationCells

namespace OAI

/-! # Compression tournament construction with live storage

The already-built left and right arrays are retained by the caller. The
initializer reads them by index and creates only the padded tournament;
there is no row-array copy for an individual tournament leaf.
-/

namespace LowSpaceSubsetSum.CompressionInitializationCells

open RepresentationInitializationCells (index)

def front (left right : Array ℤ) (P : ℤ)
    (hs : FilteredRow.PrimarySorted right id 1) (mode : FilteredStream.Mode)
    (d : ℕ) (path : RowMerge.Path d) :
    (Option (RowMerge.Front d (ℤ × ℤ)
      (FilteredStream.Cursor (α := ℤ) right)) × ℕ) × ℕ :=
  let i := index d path
  if h : i.1.1 < left.size then
    let row := CompressionRowCells.run right P hs mode left[i.1.1]
    let out := CompressionReaderCells.rowRead right (some row.1.1)
    ((out.1.1.map (fun z => ⟨path,z.1,z.2⟩),i.1.2+row.1.2+out.1.2+6),
      max i.2 (max row.2 out.2)+32)
  else ((none,i.1.2+2),i.2+16)

theorem front_value (left right : Array ℤ) (P : ℤ)
    (hs : FilteredRow.PrimarySorted right id 1) (mode : FilteredStream.Mode)
    (d : ℕ) (path : RowMerge.Path d) :
    (front left right P hs mode d path).1 = FilteredStream.measuredFront left right
      (CompressionInitialization.row right P hs mode) d path := by
  simp only [front, FilteredStream.measuredFront, RepresentationInitializationCells.index_value]
  split <;> simp only [CompressionRowCells.value, CompressionReaderCells.rowRead_value]

theorem front_cells (left right : Array ℤ) (P : ℤ)
    (hs : FilteredRow.PrimarySorted right id 1) (mode : FilteredStream.Mode)
    (d : ℕ) (path : RowMerge.Path d) :
    (front left right P hs mode d path).2 ≤ 300*(d+1) := by
  have hi := RepresentationInitializationCells.index_cells d path
  unfold front
  dsimp only
  split
  · have hr := CompressionRowCells.cells right P hs mode left[(index d path).1.1]
    have hq := CompressionReaderCells.rowRead_cells right
      (some (CompressionRowCells.run right P hs mode left[(index d path).1.1]).1.1)
    change max _ (max _ _) + 32 ≤ _
    omega
  · dsimp only; omega

def tree (left right : Array ℤ) (P : ℤ)
    (hs : FilteredRow.PrimarySorted right id 1) (mode : FilteredStream.Mode) :=
  MeasuredBuildCells.run 32 (fun x => CompressionReaderCells.pairKey P mode x.value)
    (Nat.clog 2 left.size) (front left right P hs mode (Nat.clog 2 left.size))

theorem tree_value (left right : Array ℤ) (P : ℤ)
    (hs : FilteredRow.PrimarySorted right id 1) (mode : FilteredStream.Mode) :
    (tree left right P hs mode).1 = CompressionInitialization.tree left right P hs mode := by
  rw [tree, MeasuredBuildCells.run_value]
  have hk : (fun x : RowMerge.Front (Nat.clog 2 left.size) (ℤ × ℤ)
      (FilteredStream.Cursor (α := ℤ) right) =>
      (CompressionReaderCells.pairKey P mode x.value).1) =
      (fun x => CompressionReader.key P mode x.value) := rfl
  have hf : (fun path => (front left right P hs mode (Nat.clog 2 left.size) path).1) =
      FilteredStream.measuredFront left right (CompressionInitialization.row right P hs mode)
        (Nat.clog 2 left.size) := funext (front_value left right P hs mode _)
  rw [hk,hf]
  rfl

private theorem padded_pow (R : ℕ) : 2^(Nat.clog 2 R+1) ≤ 4*(R+1) := by
  have h := Tournament.padded_nodes_le R
    (Tournament.build (fun _ : Unit => (0 : ℤ)) (Nat.clog 2 R) (fun _ => none))
  simpa only [Tournament.nodes_exact] using h

theorem tree_cells {n : ℕ} (I : Instance n) (hn : 10000 ≤ n)
    (left right : Array ℤ) (P : ℤ)
    (hs : FilteredRow.PrimarySorted right id 1) (mode : FilteredStream.Mode)
    (C : ℕ) (hL : left.size ≤ C) (hC : C ≤ 2^n) :
    (tree left right P hs mode).2 ≤ inputScale I^4*(C+1) := by
  let d := Nat.clog 2 left.size
  let u := inputScale I
  have hd : d ≤ n := Nat.clog_le_of_le_pow (hL.trans hC)
  have hu : n+1 ≤ u := by unfold u inputScale; omega
  have ht : 2^(d+1) ≤ 4*(C+1) :=
    (padded_pow left.size).trans (Nat.mul_le_mul_left 4 (Nat.add_le_add_right hL 1))
  have h := @MeasuredBuildCells.run_cells
    (RowMerge.Front d (ℤ × ℤ) (FilteredStream.Cursor (α := ℤ) right))
    32 (fun x => CompressionReaderCells.pairKey P mode x.value) 8 (300*(d+1))
    (fun _ => le_rfl) d (front left right P hs mode d)
    (front_cells left right P hs mode d)
  change (tree left right P hs mode).2 ≤ _ at h
  have hcoef : 4*(32*2^(d+1))+8+300*(d+1)+64 ≤ 884*u*(C+1) := by
    have hh := Nat.mul_le_mul_left 128 ht
    nlinarith only [hh,hu,hd,hn]
  have hm := Nat.mul_le_mul (show d+1 ≤ u by omega) hcoef
  have hp : 884*u^2 ≤ u^4 := by
    have hl : 884 ≤ u^2 := by nlinarith only [hu,hn]
    have hh := Nat.mul_le_mul_right (u^2) hl
    simpa only [←pow_add] using hh
  change (tree left right P hs mode).2 ≤ u^4*(C+1)
  calc
    _ ≤ (d+1)*(4*(32*2^(d+1))+8+300*(d+1)+64) := h
    _ ≤ u*(884*u*(C+1)) := hm
    _ = 884*u^2*(C+1) := by ring
    _ ≤ _ := Nat.mul_le_mul_right (C+1) hp

def start (left right : Array ℤ) (P : ℤ)
    (hs : FilteredRow.PrimarySorted right id 1)
    (ht : FilteredRow.SecondarySorted right id 1 P) (hP : 0 < P)
    (mode : FilteredStream.Mode) :
    (CompressionReader.State P mode right (Nat.clog 2 left.size) × ℕ) × ℕ :=
  let out := tree left right P hs mode
  let source := FilteredStream.start left right id id 1 P 0 hs ht hP mode
  have he : out.1.1 = source.tree :=
    (congrArg Prod.fst (tree_value left right P hs mode)).trans
      (CompressionInitialization.tree_value left right P hs ht hP mode)
  ((⟨out.1.1,he.symm ▸ source.valid,he.symm ▸ source.aligned,he.symm ▸ source.sorted⟩,
    out.1.2),out.2+16)

theorem start_value (left right : Array ℤ) (P : ℤ)
    (hs : FilteredRow.PrimarySorted right id 1)
    (ht : FilteredRow.SecondarySorted right id 1 P) (hP : 0 < P)
    (mode : FilteredStream.Mode) :
    (start left right P hs ht hP mode).1 =
      CompressionInitialization.start left right P hs ht hP mode := by
  have h := tree_value left right P hs mode
  unfold start CompressionInitialization.start
  simp only [h]

theorem start_cells {n : ℕ} (I : Instance n) (hn : 10000 ≤ n)
    (left right : Array ℤ) (P : ℤ)
    (hs : FilteredRow.PrimarySorted right id 1)
    (ht : FilteredRow.SecondarySorted right id 1 P) (hP : 0 < P)
    (mode : FilteredStream.Mode) (C : ℕ) (hL : left.size ≤ C) (hC : C ≤ 2^n) :
    (start left right P hs ht hP mode).2 ≤ inputScale I^5*(C+1) := by
  have h := tree_cells I hn left right P hs mode C hL hC
  have hu : 10000 ≤ inputScale I := by unfold inputScale; omega
  have hp : 16 ≤ inputScale I^4 := by
    have : inputScale I ≤ inputScale I^4 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (show 1 ≤ inputScale I by omega)
        (by decide : 1 ≤ 4)
    omega
  have hm : 2*inputScale I^4 ≤ inputScale I^5 := by
    calc
      _ ≤ inputScale I*inputScale I^4 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' _ _).symm
  have hb := Nat.mul_le_mul_right (C+1) hm
  change _+16 ≤ _
  nlinarith only [h,hp,hb]

end LowSpaceSubsetSum.CompressionInitializationCells

end OAI
