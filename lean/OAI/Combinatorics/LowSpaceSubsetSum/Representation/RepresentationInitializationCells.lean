import OAI.Combinatorics.LowSpaceSubsetSum.Storage.MeasuredBuildCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.MeasuredRowCells
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationArrayInitialization
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationReaderCells

namespace OAI

/-! # Live cells of shared-array row tournament initialization -/

namespace LowSpaceSubsetSum.RepresentationInitializationCells

variable {n : ℕ}

def index : (d : ℕ) → RowMerge.Path d → (ℕ × ℕ) × ℕ
  | 0, _ => ((0, 1), 8)
  | d + 1, p =>
    let t := index d (fun i => p i.succ)
    (((if p 0 then 1 else 0) + 2 * t.1.1, t.1.2 + 2 * d + 6), t.2 + 8)

theorem index_value (d : ℕ) (p : RowMerge.Path d) : (index d p).1 = PaddedRows.measuredIndex d p := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [index, PaddedRows.measuredIndex, ih]

theorem index_cells (d : ℕ) (p : RowMerge.Path d) : (index d p).2 = 8 * (d + 1) := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [index, ih]; omega

def front (I : Instance n) (F : IndexedMask n) (left right : Array (LeafRecord n))
    (p P c : ℤ)
    (hs : FilteredRow.PrimarySorted right (fun x => (RepresentationKeys.leafWeight I F x).1) p)
    (mode : FilteredStream.Mode) (d : ℕ) (path : RowMerge.Path d) :
    (Option (RowMerge.Front d (LeafRecord n × LeafRecord n)
      (FilteredStream.Cursor (α := LeafRecord n) right)) × ℕ) × ℕ :=
  let i := index d path
  if h : i.1.1 < left.size then
    let r := MeasuredRowCells.row I F right p P c hs mode left[i.1.1]
    let q := RepresentationReaderCells.rowRead right (some r.1.1)
    ((q.1.1.map (fun z => ⟨path, z.1, z.2⟩), i.1.2 + r.1.2 + q.1.2 + 6),
      max i.2 (max r.2 q.2) + 12 * n + 48)
  else ((none, i.1.2 + 2), i.2 + 16)

theorem front_value (I : Instance n) (F : IndexedMask n) (left right : Array (LeafRecord n))
    (p P c : ℤ)
    (hs : FilteredRow.PrimarySorted right (fun x => (RepresentationKeys.leafWeight I F x).1) p)
    (mode : FilteredStream.Mode) (d : ℕ) (path : RowMerge.Path d) :
    (front I F left right p P c hs mode d path).1 = FilteredStream.measuredFront left right
      (RepresentationKeys.row I F right p P c hs mode) d path := by
  simp only [front, FilteredStream.measuredFront, index_value]
  split <;> simp only [MeasuredRowCells.row_value, RepresentationReaderCells.rowRead_value]

theorem front_cells (I : Instance n) (F : IndexedMask n) (left right : Array (LeafRecord n))
    (p P c : ℤ)
    (hs : FilteredRow.PrimarySorted right (fun x => (RepresentationKeys.leafWeight I F x).1) p)
    (mode : FilteredStream.Mode) (d : ℕ) (path : RowMerge.Path d) (hd : d ≤ n) :
    (front I F left right p P c hs mode d path).2 ≤ 300 * inputScale I := by
  have hi := index_cells d path
  have hu : n + 1 ≤ inputScale I := by unfold inputScale; omega
  unfold front
  dsimp only
  split
  · rename_i h
    have hr := MeasuredRowCells.row_cells I F right p P c hs mode left[(index d path).1.1]
    have hq := RepresentationReaderCells.rowRead_cells right
      (some (MeasuredRowCells.row I F right p P c hs mode left[(index d path).1.1]).1.1)
    change max _ (max _ _) + 12 * n + 48 ≤ _
    omega
  · dsimp only; omega

def tree (I : Instance n) (F : IndexedMask n) (left right : Array (LeafRecord n))
    (p P c : ℤ)
    (hs : FilteredRow.PrimarySorted right (fun x => (RepresentationKeys.leafWeight I F x).1) p)
    (mode : FilteredStream.Mode) :=
  MeasuredBuildCells.run (12 * n + 32)
    (fun x => RepresentationKeyCells.pairKey I F P mode x.value) (Nat.clog 2 left.size)
    (front I F left right p P c hs mode (Nat.clog 2 left.size))

theorem tree_value (I : Instance n) (F : IndexedMask n) (left right : Array (LeafRecord n))
    (p P c : ℤ)
    (hs : FilteredRow.PrimarySorted right (fun x => (RepresentationKeys.leafWeight I F x).1) p)
    (mode : FilteredStream.Mode) :
    (tree I F left right p P c hs mode).1 = RepresentationArrayInitialization.tree I F left right p P c hs mode := by
  rw [tree, MeasuredBuildCells.run_value]
  have hkey : (fun x : RowMerge.Front (Nat.clog 2 left.size) (LeafRecord n × LeafRecord n)
      (FilteredStream.Cursor (α := LeafRecord n) right) =>
      (RepresentationKeyCells.pairKey I F P mode x.value).1) =
        (fun x => RepresentationKeys.pairKey I F P mode x.value) := by
    funext x
    exact RepresentationKeyCells.pairKey_value I F P mode x.value
  have hfront : (fun path => (front I F left right p P c hs mode (Nat.clog 2 left.size) path).1) =
      FilteredStream.measuredFront left right (RepresentationKeys.row I F right p P c hs mode)
        (Nat.clog 2 left.size) := by
    funext path
    exact front_value I F left right p P c hs mode _ path
  rw [hkey, hfront]
  rfl

private theorem scale (n u C d a : ℕ) (hn : 10000 ≤ n) (hu : n + 1 ≤ u) (hd : d ≤ n)
    (ht : 2 ^ (d + 1) ≤ 4 * (C + 1))
    (ha : a ≤ (d + 1) * (4 * ((12 * n + 32) * 2 ^ (d + 1)) + (12 * n + 32) + 300 * u + 64)) :
    a ≤ u ^ 5 * (C + 1) := by
  have hN : 12 * n + 32 ≤ 44 * u := by omega
  have hnodes := Nat.mul_le_mul hN ht
  have hp : 1 ≤ u := by omega
  have hcoeff : 4 * ((12 * n + 32) * 2 ^ (d + 1)) + (12 * n + 32) + 300 * u + 64 ≤
      1112 * u * (C + 1) := by nlinarith only [hnodes, hN, hp]
  have hm := ha.trans (Nat.mul_le_mul (show d + 1 ≤ u by omega) hcoeff)
  have hpower : 1112 * u ^ 2 ≤ u ^ 5 := by
    have hlow : 1112 ≤ u ^ 3 := by
      have h : u ≤ u ^ 3 := by simpa only [pow_one] using Nat.pow_le_pow_right hp (by decide : 1 ≤ 3)
      omega
    calc
      _ ≤ u ^ 3 * u ^ 2 := Nat.mul_le_mul_right _ hlow
      _ = _ := by rw [← pow_add]
  exact hm.trans (by nlinarith only [Nat.mul_le_mul_right (C + 1) hpower])

private theorem padded_pow (R : ℕ) : 2 ^ (Nat.clog 2 R + 1) ≤ 4 * (R + 1) := by
  have h := Tournament.padded_nodes_le R
    (Tournament.build (fun _ : Unit => (0 : ℤ)) (Nat.clog 2 R) (fun _ => none))
  simpa only [Tournament.nodes_exact] using h

private theorem tree_cells_raw (I : Instance n) (F : IndexedMask n) (left right : Array (LeafRecord n))
    (p P c : ℤ)
    (hs : FilteredRow.PrimarySorted right (fun x => (RepresentationKeys.leafWeight I F x).1) p)
    (mode : FilteredStream.Mode) (hd : Nat.clog 2 left.size ≤ n) :
    (tree I F left right p P c hs mode).2 ≤ (Nat.clog 2 left.size + 1) *
      (4 * ((12 * n + 32) * 2 ^ (Nat.clog 2 left.size + 1)) + (12 * n + 32) + 300 * inputScale I + 64) := by
  exact @MeasuredBuildCells.run_cells
    (RowMerge.Front (Nat.clog 2 left.size) (LeafRecord n × LeafRecord n)
      (FilteredStream.Cursor (α := LeafRecord n) right))
    (12 * n + 32) (fun x => RepresentationKeyCells.pairKey I F P mode x.value)
    (12 * n + 32) (300 * inputScale I)
    (fun x => RepresentationKeyCells.pairKey_cells I F P mode x.value) (Nat.clog 2 left.size)
    (front I F left right p P c hs mode (Nat.clog 2 left.size))
    (fun path => front_cells I F left right p P c hs mode _ path hd)

theorem tree_cells (I : Instance n) (F : IndexedMask n) (left right : Array (LeafRecord n))
    (p P c : ℤ)
    (hs : FilteredRow.PrimarySorted right (fun x => (RepresentationKeys.leafWeight I F x).1) p)
    (mode : FilteredStream.Mode) (C : ℕ) (hn : 10000 ≤ n) (hL : left.size ≤ C) (hC : C ≤ 2 ^ n) :
    (tree I F left right p P c hs mode).2 ≤ inputScale I ^ 5 * (C + 1) := by
  have hd := Nat.clog_le_of_le_pow (hL.trans hC)
  have ht : 2 ^ (Nat.clog 2 left.size + 1) ≤ 4 * (C + 1) :=
    (padded_pow left.size).trans (Nat.mul_le_mul_left 4 (Nat.add_le_add_right hL 1))
  have hb := tree_cells_raw I F left right p P c hs mode hd
  exact scale n (inputScale I) C (Nat.clog 2 left.size)
    (tree I F left right p P c hs mode).2 hn (by unfold inputScale; omega) hd ht hb


def start (I : Instance n) (F : IndexedMask n) (left right : Array (LeafRecord n))
    (p P c : ℤ)
    (hs : FilteredRow.PrimarySorted right (fun x => (RepresentationKeys.leafWeight I F x).1) p)
    (ht : FilteredRow.SecondarySorted right (fun x => (RepresentationKeys.leafWeight I F x).1) p P)
    (hP : 0 < P) (mode : FilteredStream.Mode) :
    (MergedReader.State
      (FilteredStream.key (fun x => (RepresentationKeys.leafWeight I F x).1)
        (fun x => (RepresentationKeys.leafWeight I F x).1) P mode)
      (FilteredStream.view right) (Nat.clog 2 left.size) × ℕ) × ℕ :=
  let out := tree I F left right p P c hs mode
  let source := FilteredStream.start left right (fun x => (RepresentationKeys.leafWeight I F x).1)
    (fun x => (RepresentationKeys.leafWeight I F x).1) p P c hs ht hP mode
  have he : out.1.1 = source.tree :=
    (congrArg Prod.fst (tree_value I F left right p P c hs mode)).trans
      (RepresentationArrayInitialization.tree_value I F left right p P c hs ht hP mode)
  ((⟨out.1.1, he.symm ▸ source.valid, he.symm ▸ source.aligned, he.symm ▸ source.sorted⟩,
    out.1.2), out.2 + 16)

theorem start_value (I : Instance n) (F : IndexedMask n) (left right : Array (LeafRecord n))
    (p P c : ℤ)
    (hs : FilteredRow.PrimarySorted right (fun x => (RepresentationKeys.leafWeight I F x).1) p)
    (ht : FilteredRow.SecondarySorted right (fun x => (RepresentationKeys.leafWeight I F x).1) p P)
    (hP : 0 < P) (mode : FilteredStream.Mode) :
    (start I F left right p P c hs ht hP mode).1 =
      RepresentationArrayInitialization.start I F left right p P c hs ht hP mode := by
  have he := tree_value I F left right p P c hs mode
  unfold start RepresentationArrayInitialization.start
  simp only [he]

theorem start_cells (I : Instance n) (F : IndexedMask n) (left right : Array (LeafRecord n))
    (p P c : ℤ)
    (hs : FilteredRow.PrimarySorted right (fun x => (RepresentationKeys.leafWeight I F x).1) p)
    (ht : FilteredRow.SecondarySorted right (fun x => (RepresentationKeys.leafWeight I F x).1) p P)
    (hP : 0 < P) (mode : FilteredStream.Mode) (C : ℕ) (hn : 10000 ≤ n)
    (hL : left.size ≤ C) (hC : C ≤ 2 ^ n) :
    (start I F left right p P c hs ht hP mode).2 ≤ inputScale I ^ 6 * (C + 1) := by
  have h := tree_cells I F left right p P c hs mode C hn hL hC
  have hu : 10000 ≤ inputScale I := by unfold inputScale; omega
  have hp : 16 ≤ inputScale I ^ 5 := by
    have hl : inputScale I ≤ inputScale I ^ 5 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ inputScale I) (by decide : 1 ≤ 5)
    omega
  have hm : 2 * inputScale I ^ 5 ≤ inputScale I ^ 6 := by
    calc
      _ ≤ inputScale I * inputScale I ^ 5 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' _ _).symm
  have hb := Nat.mul_le_mul_right (C + 1) hm
  change _ + 16 ≤ _
  nlinarith only [h, hp, hb]

end LowSpaceSubsetSum.RepresentationInitializationCells

end OAI
