import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationReportCells
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationReaderCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.BudgetedReplayCells

namespace OAI

/-! # Concrete bounded-space replay of a parent tie suffix

Only the current reader and the safe dictionary survive the tail iteration.
The query, report, halt, remaining-budget and work fields are preserved.
The bound is independent of suffix length and remains valid on budget failure.
-/

namespace LowSpaceSubsetSum.RepresentationReplayCells

variable {n : ℕ}

def run (I : Instance n) (F : IndexedMask n) (P : ℤ) (mode : FilteredStream.Mode)
    (right : Array (LeafRecord n)) {d : ℕ} (C charge : ℕ) (K : ℤ)
    (x : LeafRecord n × LeafRecord n) (fuel : ℕ)
    (s : CountedParentJoin.State I F P mode right d) (r : StoredEntry.Dictionary I C)
    (q reports budget : ℕ) :=
  BudgetedReplayCells.run charge (RepresentationReaderCells.read I F P mode right)
    (RepresentationKeyCells.pairKey I F P mode) K (RepresentationReportCells.report I F C x)
    ParentLiveState.reader ParentLiveState.dictionary CountedParentJoin.cells
    fuel s r q reports budget

theorem run_value (I : Instance n) (F : IndexedMask n) (P : ℤ) (mode : FilteredStream.Mode)
    (right : Array (LeafRecord n)) {d : ℕ} (C charge : ℕ) (K : ℤ)
    (x : LeafRecord n × LeafRecord n) (fuel : ℕ)
    (s : CountedParentJoin.State I F P mode right d) (r : StoredEntry.Dictionary I C)
    (q reports budget : ℕ) :
    (run I F P mode right C charge K x fuel s r q reports budget).1 =
      BudgetedReplay.execute charge (RepresentationKeys.read I F P mode right)
        (RepresentationKeys.pairKey I F P mode) K
        (StoredEntry.report I C (CountedRepresentationEmit.emit I F) x)
        fuel s r q reports budget := by
  rw [run, BudgetedReplayCells.run_value]
  have hr : (fun s : CountedParentJoin.State I F P mode right d =>
      (RepresentationReaderCells.read I F P mode right s).1) =
      RepresentationKeys.read I F P mode right := funext (RepresentationReaderCells.read_value I F P mode right)
  have hk : (fun y => (RepresentationKeyCells.pairKey I F P mode y).1) =
      RepresentationKeys.pairKey I F P mode := funext (RepresentationKeyCells.pairKey_value I F P mode)
  have hp : (fun y r => (RepresentationReportCells.report I F C x y r).1) =
      StoredEntry.report I C (CountedRepresentationEmit.emit I F) x := by
    funext y r
    exact RepresentationReportCells.report_value I F C x y r
  rw [hr, hk, hp]

theorem run_cells (I : Instance n) (F : IndexedMask n) (P : ℤ) (mode : FilteredStream.Mode)
    (right : Array (LeafRecord n)) {d : ℕ} (C charge : ℕ) (K : ℤ)
    (x : LeafRecord n × LeafRecord n) (fuel : ℕ)
    (s : CountedParentJoin.State I F P mode right d) (r : StoredEntry.Dictionary I C)
    (q reports budget : ℕ) (hn : 10000 ≤ n) (ht : 2 ^ (d + 1) ≤ 4 * (C + 1)) (hd : d ≤ n) :
    (run I F P mode right C charge K x fuel s r q reports budget).2 ≤
      inputScale I ^ 5 * (C + 1) := by
  let u := inputScale I
  have hu : n + 1 ≤ u := by unfold u inputScale; omega
  have hc : 12 * n + 32 ≤ 44 * u := by omega
  have hm := Nat.mul_le_mul hc ht
  have hs : ∀ st : CountedParentJoin.State I F P mode right d,
      ParentLiveState.reader st ≤ 176 * u * (C + 1) := by
    intro st
    rw [ParentLiveState.reader_exact]
    nlinarith only [hm]
  have hl : ∀ y, (RepresentationKeyCells.pairKey I F P mode y).2 ≤ 44 * u := by
    intro y
    exact (RepresentationKeyCells.pairKey_cells I F P mode y).trans hc
  have h := BudgetedReplayCells.run_cells charge (RepresentationReaderCells.read I F P mode right)
    (RepresentationKeyCells.pairKey I F P mode) K (RepresentationReportCells.report I F C x)
    ParentLiveState.reader ParentLiveState.dictionary CountedParentJoin.cells
    (176 * u * (C + 1)) (18 * u * (C + 1) + 8) (6 * n + 4)
    (u ^ 4 * (C + 1)) (44 * u) (u ^ 2 * (C + 1)) hs
    (ParentLiveState.dictionary_scale I C) CountedParentJoin.cells_le
    (fun st => RepresentationReaderCells.read_scale I F P mode right st C hn hd ht) hl
    (fun y r => RepresentationReportCells.report_scale I F C x y r hn)
    fuel s r q reports budget
  change (run I F P mode right C charge K x fuel s r q reports budget).2 ≤ _ at h
  have hsmall : (run I F P mode right C charge K x fuel s r q reports budget).2 ≤
      (u ^ 4 + u ^ 2 + 500 * u) * (C + 1) := by nlinarith only [h, hu, hn]
  have hu2 : 500 * u ≤ u ^ 2 := by nlinarith only [hu, hn]
  have hu4 : 2 * u ^ 2 ≤ u ^ 4 := by
    have hbase : 2 ≤ u ^ 2 := by nlinarith only [hu, hn]
    have hmul := Nat.mul_le_mul_right (u ^ 2) hbase
    simpa only [← pow_add] using hmul
  have hu5 : 2 * u ^ 4 ≤ u ^ 5 := by
    calc
      _ ≤ u * u ^ 4 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' _ _).symm
  change (run I F P mode right C charge K x fuel s r q reports budget).2 ≤ u ^ 5 * (C + 1)
  exact hsmall.trans (Nat.mul_le_mul_right (C + 1) (by omega))

end LowSpaceSubsetSum.RepresentationReplayCells

end OAI
