import OAI.Combinatorics.LowSpaceSubsetSum.Storage.MeasuredReaderCells
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.ParentLiveState

namespace OAI

/-! # Scratch of a concrete representation reader

The array cursor performs one indexed load. Tournament replacement uses the
measured list-mask key and retains the shared right array without copying it.
Every output includes the unchanged work counter as well as the live trace.
-/

namespace LowSpaceSubsetSum.RepresentationReaderCells

variable {n : ℕ}

def rowRead (right : Array (LeafRecord n)) : FilteredStream.Cursor (α := LeafRecord n) right →
    (Option ((LeafRecord n × LeafRecord n) ×
      FilteredStream.Cursor (α := LeafRecord n) right) × ℕ) × ℕ
  | none => ((none, 2), 8)
  | some s =>
    let q := PairCursor.countedNext right s
    ((q.1.map (fun z => (z.1, some z.2)), q.2 + 4), 12 * n + 64)

theorem rowRead_value (right : Array (LeafRecord n))
    (s : FilteredStream.Cursor (α := LeafRecord n) right) :
    (rowRead right s).1 = FilteredStream.countedRead right s := by
  cases s <;> rfl

theorem rowRead_cells (right : Array (LeafRecord n))
    (s : FilteredStream.Cursor (α := LeafRecord n) right) :
    (rowRead right s).2 ≤ 12 * n + 64 := by
  cases s <;> simp only [rowRead] <;> omega

private theorem reader (right : Array (LeafRecord n)) :
    RowMerge.IsReader (fun s => (FilteredStream.countedRead (α := LeafRecord n) right s).1)
      (FilteredStream.view (α := LeafRecord n) right) := by
  simpa only [FilteredStream.countedRead_value] using FilteredStream.reader (α := LeafRecord n) right

def read (I : Instance n) (F : IndexedMask n) (P : ℤ) (mode : FilteredStream.Mode)
    (right : Array (LeafRecord n)) {d : ℕ} (s : CountedParentJoin.State I F P mode right d) :=
  MeasuredReaderCells.next (12 * n + 32)
    (RepresentationKeys.pairKey I F P mode) (FilteredStream.countedRead right)
    (RepresentationKeyCells.pairKey I F P mode) (rowRead right)
    (RepresentationKeyCells.pairKey_value I F P mode) (rowRead_value right)
    (FilteredStream.view right) (reader right) s

theorem read_value (I : Instance n) (F : IndexedMask n) (P : ℤ) (mode : FilteredStream.Mode)
    (right : Array (LeafRecord n)) {d : ℕ} (s : CountedParentJoin.State I F P mode right d) :
    (read I F P mode right s).1 = RepresentationKeys.read I F P mode right s :=
  MeasuredReaderCells.next_value (12 * n + 32)
    (RepresentationKeys.pairKey I F P mode) (FilteredStream.countedRead right)
    (RepresentationKeyCells.pairKey I F P mode) (rowRead right)
    (RepresentationKeyCells.pairKey_value I F P mode) (rowRead_value right)
    (FilteredStream.view right) (reader right) s

theorem read_cells (I : Instance n) (F : IndexedMask n) (P : ℤ) (mode : FilteredStream.Mode)
    (right : Array (LeafRecord n)) {d : ℕ} (s : CountedParentJoin.State I F P mode right d) :
    (read I F P mode right s).2 ≤
      (d + 2) * (6 * ((12 * n + 32) * 2 ^ (d + 1)) + (12 * n + 64) + (12 * n + 32) + 100) + 8 :=
  MeasuredReaderCells.next_cells (12 * n + 32)
    (RepresentationKeys.pairKey I F P mode) (FilteredStream.countedRead right)
    (RepresentationKeyCells.pairKey I F P mode) (rowRead right)
    (RepresentationKeyCells.pairKey_value I F P mode) (rowRead_value right)
    (FilteredStream.view right) (reader right) s (12 * n + 32) (12 * n + 64)
    (RepresentationKeyCells.pairKey_cells I F P mode) (rowRead_cells right)

theorem read_scale (I : Instance n) (F : IndexedMask n) (P : ℤ) (mode : FilteredStream.Mode)
    (right : Array (LeafRecord n)) {d : ℕ} (s : CountedParentJoin.State I F P mode right d)
    (C : ℕ) (hn : 10000 ≤ n) (hd : d ≤ n) (ht : 2 ^ (d + 1) ≤ 4 * (C + 1)) :
    (read I F P mode right s).2 ≤ inputScale I ^ 4 * (C + 1) := by
  let u := inputScale I
  have hu : n + 1 ≤ u := by unfold u inputScale; omega
  have hu0 : 1 ≤ u := by omega
  have hc : 12 * n + 32 ≤ 44 * u := by omega
  have hm := Nat.mul_le_mul hc ht
  have ha : 6 * ((12 * n + 32) * 2 ^ (d + 1)) + (12 * n + 64) + (12 * n + 32) + 100 ≤
      1300 * u * (C + 1) := by nlinarith only [hm, hu]
  have hdepth : d + 2 ≤ 2 * u := by omega
  have hb := Nat.mul_le_mul hdepth ha
  have hbase := read_cells I F P mode right s
  have hsmall : (read I F P mode right s).2 ≤ 2608 * u ^ 2 * (C + 1) := by
    have h8 : 8 ≤ 8 * u ^ 2 * (C + 1) := by nlinarith only [hu0]
    nlinarith only [hbase, hb, h8]
  have hpow : 2608 ≤ u ^ 2 := by nlinarith only [hu, hn]
  have hmul := Nat.mul_le_mul_right (u ^ 2 * (C + 1)) hpow
  apply hsmall.trans
  change 2608 * u ^ 2 * (C + 1) ≤ u ^ 4 * (C + 1)
  nlinarith only [hmul]

end LowSpaceSubsetSum.RepresentationReaderCells

end OAI
