import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionReader
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.MeasuredReaderCells
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationSnapshotCells

namespace OAI

/-! # Concrete compression reader and snapshot storage

Each tournament front contains two scalar weights and one bounded cursor.
The shared right array is retained by the caller and is never copied by a
read or a snapshot.
-/

namespace LowSpaceSubsetSum.CompressionReaderCells

def rowRead (right : Array ℤ) : FilteredStream.Cursor (α := ℤ) right →
    (Option ((ℤ × ℤ) × FilteredStream.Cursor (α := ℤ) right) × ℕ) × ℕ
  | none => ((none,2),8)
  | some s =>
    let q := PairCursor.countedNext right s
    ((q.1.map (fun z => (z.1,some z.2)),q.2+4),32)

theorem rowRead_value (right : Array ℤ) (s : FilteredStream.Cursor (α := ℤ) right) :
    (rowRead right s).1 = FilteredStream.countedRead right s := by
  cases s <;> rfl

theorem rowRead_cells (right : Array ℤ) (s : FilteredStream.Cursor (α := ℤ) right) :
    (rowRead right s).2 ≤ 32 := by
  cases s <;> simp only [rowRead] <;> omega

def pairKey (P : ℤ) (mode : FilteredStream.Mode) (x : ℤ × ℤ) : (ℤ × ℕ) × ℕ :=
  (CompressionReader.key P mode x,8)

private theorem reader (right : Array ℤ) :
    RowMerge.IsReader (fun s => (FilteredStream.countedRead (α := ℤ) right s).1)
      (FilteredStream.view (α := ℤ) right) := by
  simpa only [FilteredStream.countedRead_value] using FilteredStream.reader (α := ℤ) right

def read (P : ℤ) (mode : FilteredStream.Mode) (right : Array ℤ) {d : ℕ}
    (s : CompressionReader.State P mode right d) :=
  let out := MeasuredReaderCells.next 32 (CompressionReader.key P mode)
    (FilteredStream.countedRead right) (pairKey P mode) (rowRead right)
    (fun _ => rfl) (rowRead_value right) (FilteredStream.view right) (reader right) s
  ((out.1.1.map (fun p => (p.1.1+p.1.2,p.2)),out.1.2+2),out.2+16)

theorem read_value (P : ℤ) (mode : FilteredStream.Mode) (right : Array ℤ) {d : ℕ}
    (s : CompressionReader.State P mode right d) :
    (read P mode right s).1 = CompressionReader.read P mode right s := by
  have h := MeasuredReaderCells.next_value 32 (CompressionReader.key P mode)
    (FilteredStream.countedRead right) (pairKey P mode) (rowRead right)
    (fun _ => rfl) (rowRead_value right) (FilteredStream.view right) (reader right) s
  have hv := congrArg Prod.fst h
  have hw := congrArg Prod.snd h
  simp only [read, CompressionReader.read, hv, hw]

def stateCells {P : ℤ} {mode : FilteredStream.Mode} {right : Array ℤ} {d : ℕ}
    (s : CompressionReader.State P mode right d) : ℕ := 32*(Tournament.nodes s.tree+1)

theorem stateCells_exact {P : ℤ} {mode : FilteredStream.Mode} {right : Array ℤ} {d : ℕ}
    (s : CompressionReader.State P mode right d) : stateCells s = 32*2^(d+1) := by
  simp only [stateCells,Tournament.nodes_exact]

theorem read_cells (P : ℤ) (mode : FilteredStream.Mode) (right : Array ℤ) {d : ℕ}
    (s : CompressionReader.State P mode right d) :
    (read P mode right s).2 ≤ (d+2)*(192*2^(d+1)+140)+24 := by
  have h := MeasuredReaderCells.next_cells 32 (CompressionReader.key P mode)
    (FilteredStream.countedRead right) (pairKey P mode) (rowRead right)
    (fun _ => rfl) (rowRead_value right) (FilteredStream.view right) (reader right) s
    8 32 (fun _ => le_rfl) (rowRead_cells right)
  change _+16 ≤ _
  convert Nat.add_le_add_right h 16 using 1; ring

theorem read_scale {n : ℕ} (I : Instance n) (hn : 10000 ≤ n)
    (P : ℤ) (mode : FilteredStream.Mode) (right : Array ℤ) {d : ℕ}
    (s : CompressionReader.State P mode right d) (C : ℕ)
    (hd : d ≤ n) (ht : 2^(d+1) ≤ 4*(C+1)) :
    (read P mode right s).2 ≤ inputScale I^4*(C+1) := by
  let u := inputScale I
  have hu : n+1 ≤ u := by unfold u inputScale; omega
  have hbound : 192*2^(d+1)+140 ≤ 908*(C+1) := by omega
  have hd' : d+2 ≤ 2*u := by omega
  have hm := Nat.mul_le_mul hd' hbound
  have hr := read_cells P mode right s
  have hsmall : (read P mode right s).2 ≤ 1840*u*(C+1) := by
    nlinarith only [hm,hr,hu]
  have hp : u ≤ u^3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (show 1 ≤ u by omega) (by decide : 1 ≤ 3)
  have hlarge : 1840*u ≤ u^4 := by
    have hx : 1840 ≤ u^3 := by omega
    simpa only [pow_succ] using Nat.mul_le_mul_right u hx
  exact hsmall.trans (Nat.mul_le_mul_right (C+1) hlarge)

def scalarKey (P : ℤ) (mode : FilteredStream.Mode) (x : ℤ) : (ℤ × ℕ) × ℕ :=
  (CompressionReader.scalarKey P mode x,8)

def snapshot (P : ℤ) (mode : FilteredStream.Mode) (right : Array ℤ) {d : ℕ}
    (s : CompressionReader.State P mode right d) :
    (CompressionReader.State P mode right d × ℕ) × ℕ :=
  let out := RepresentationSnapshotCells.copy 10 s.tree
  have he : out.1.1 = s.tree :=
    (congrArg Prod.fst (RepresentationSnapshotCells.copy_value 10 s.tree)).trans
      (Tournament.countedCopy_value _ _)
  ((⟨out.1.1,he.symm ▸ s.valid,he.symm ▸ s.aligned,he.symm ▸ s.sorted⟩,out.1.2),out.2+8)

theorem snapshot_value (P : ℤ) (mode : FilteredStream.Mode) (right : Array ℤ) {d : ℕ}
    (s : CompressionReader.State P mode right d) :
    (snapshot P mode right s).1 = CompressionReader.snapshot P mode right s := by
  simp only [snapshot,CompressionReader.snapshot,RepresentationSnapshotCells.copy_value]

theorem snapshot_cells (P : ℤ) (mode : FilteredStream.Mode) (right : Array ℤ) {d : ℕ}
    (s : CompressionReader.State P mode right d) :
    (snapshot P mode right s).2 ≤ 20*2^(d+1)+16*(d+1)+8 := by
  exact Nat.add_le_add_right (RepresentationSnapshotCells.copy_cells 10 s.tree) 8

end LowSpaceSubsetSum.CompressionReaderCells

end OAI
