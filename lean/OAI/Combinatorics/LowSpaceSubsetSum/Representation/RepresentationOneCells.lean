import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationReplayCells
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationSnapshotCells

namespace OAI

/-! # Live cells of one buffered parent report

The completed tie buffer and saved cursor remain shared while replaying its
records. A long group clones the saved tournament before replaying the suffix.
Every return, including each budget failure, preserves the measured
join-one result and has a bound independent of the suffix length.
-/

namespace LowSpaceSubsetSum.RepresentationOneCells

variable {n : ℕ}

private def bufferRead (buffer : Array (LeafRecord n × LeafRecord n)) (i : ℕ) :=
  ((BufferReplay.read buffer i, 4), 8)

def buffer (I : Instance n) (F : IndexedMask n) (P : ℤ) (mode : FilteredStream.Mode)
    (C charge : ℕ) (K : ℤ) (x : LeafRecord n × LeafRecord n)
    (xs : Array (LeafRecord n × LeafRecord n)) (r : StoredEntry.Dictionary I C) (budget : ℕ) :=
  BudgetedReplayCells.run charge (bufferRead xs) (RepresentationKeyCells.pairKey I F P mode) K
    (RepresentationReportCells.report I F C x) (fun _ => 1) ParentLiveState.dictionary
    CountedParentJoin.cells xs.size 0 r 0 0 budget

theorem buffer_value (I : Instance n) (F : IndexedMask n) (P : ℤ) (mode : FilteredStream.Mode)
    (C charge : ℕ) (K : ℤ) (x : LeafRecord n × LeafRecord n)
    (xs : Array (LeafRecord n × LeafRecord n)) (r : StoredEntry.Dictionary I C) (budget : ℕ) :
    (buffer I F P mode C charge K x xs r budget).1 =
      BudgetedReplay.execute charge (fun i => (BufferReplay.read xs i, 4))
        (RepresentationKeys.pairKey I F P mode) K
        (StoredEntry.report I C (CountedRepresentationEmit.emit I F) x)
        xs.size 0 r 0 0 budget := by
  rw [buffer, BudgetedReplayCells.run_value]
  have hk : (fun y => (RepresentationKeyCells.pairKey I F P mode y).1) =
      RepresentationKeys.pairKey I F P mode := funext (RepresentationKeyCells.pairKey_value I F P mode)
  have hp : (fun y r => (RepresentationReportCells.report I F C x y r).1) =
      StoredEntry.report I C (CountedRepresentationEmit.emit I F) x := by
    funext y r
    exact RepresentationReportCells.report_value I F C x y r
  rw [hk, hp]
  rfl

theorem buffer_cells (I : Instance n) (F : IndexedMask n) (P : ℤ) (mode : FilteredStream.Mode)
    (C charge : ℕ) (K : ℤ) (x : LeafRecord n × LeafRecord n)
    (xs : Array (LeafRecord n × LeafRecord n)) (r : StoredEntry.Dictionary I C) (budget : ℕ)
    (hn : 10000 ≤ n) :
    (buffer I F P mode C charge K x xs r budget).2 ≤ inputScale I ^ 5 * (C + 1) := by
  let u := inputScale I
  have hu : n + 1 ≤ u := by unfold u inputScale; omega
  have hk : ∀ y, (RepresentationKeyCells.pairKey I F P mode y).2 ≤ 44 * u := by
    intro y
    exact (RepresentationKeyCells.pairKey_cells I F P mode y).trans (by omega)
  have h := BudgetedReplayCells.run_cells charge (bufferRead xs)
    (RepresentationKeyCells.pairKey I F P mode) K (RepresentationReportCells.report I F C x)
    (fun _ => 1) ParentLiveState.dictionary CountedParentJoin.cells
    1 (18 * u * (C + 1) + 8) (6 * n + 4) 8 (44 * u) (u ^ 2 * (C + 1))
    (fun _ => le_rfl) (ParentLiveState.dictionary_scale I C) CountedParentJoin.cells_le
    (fun _ => le_rfl) hk (fun y r => RepresentationReportCells.report_scale I F C x y r hn)
    xs.size 0 r 0 0 budget
  change (buffer I F P mode C charge K x xs r budget).2 ≤ _ at h
  have hsmall : (buffer I F P mode C charge K x xs r budget).2 ≤
      (u ^ 2 + 200 * u) * (C + 1) := by nlinarith only [h, hu, hn]
  have hm : 200 * u ≤ u ^ 2 := by nlinarith only [hu, hn]
  have hu2 : 2 ≤ u ^ 3 := by
    calc
      2 ≤ 2 ^ 3 := by norm_num
      _ ≤ u ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hp := Nat.mul_le_mul_right (u ^ 2) hu2
  have hpow : 2 * u ^ 2 ≤ u ^ 5 := by simpa only [← pow_add] using hp
  change (buffer I F P mode C charge K x xs r budget).2 ≤ u ^ 5 * (C + 1)
  exact hsmall.trans (Nat.mul_le_mul_right (C + 1) (by omega))

def run (I : Instance n) (F : IndexedMask n) (P : ℤ) (mode : FilteredStream.Mode)
    (right : Array (LeafRecord n)) {d : ℕ} (C charge copyCharge : ℕ) (K : ℤ)
    (x : LeafRecord n × LeafRecord n) (xs : Array (LeafRecord n × LeafRecord n))
    (saved : CountedParentJoin.State I F P mode right d) (long : Bool) (fuel : ℕ)
    (r : StoredEntry.Dictionary I C) (budget : ℕ) :
    (Option (TieReplay.Result (CountedParentJoin.State I F P mode right d) (StoredEntry.Dictionary I C) × ℕ) × ℕ) × ℕ :=
  let retained := (6 * n + 5) * xs.size + ParentLiveState.reader saved + ParentLiveState.dictionary r + 32
  if 6 ≤ budget then
    let first := buffer I F P mode C charge K x xs r (budget - 6)
    let peak := retained + first.2 + 16
    match first.1.1 with
    | none => ((none, first.1.2 + 6), peak)
    | some (out, left) =>
      if out.halted then
        ((some (⟨saved, out.state, out.queries, out.reports, false, true⟩, left), first.1.2 + 6), peak)
      else if long then
        if copyCharge ≤ left then
          let copied := RepresentationSnapshotCells.snapshot I F P mode right saved
          let rest := RepresentationReplayCells.run I F P mode right C charge K x fuel copied.1.1
            out.state 0 0 (left - copyCharge)
          ((rest.1.1.map (fun (tail, remaining) =>
              (⟨tail.cursor, tail.state, out.queries + tail.queries,
                out.reports + tail.reports, tail.complete, tail.halted⟩, remaining)),
            first.1.2 + copied.1.2 + rest.1.2 + 6),
            max peak (max (retained + ParentLiveState.dictionary out.state + copied.2 + 16)
              (retained + ParentLiveState.dictionary out.state + rest.2 + 32)))
        else ((none, first.1.2 + 7), peak)
      else ((some (⟨saved, out.state, out.queries, out.reports, true, false⟩, left), first.1.2 + 6), peak)
  else ((none, 1), retained)

theorem run_value (I : Instance n) (F : IndexedMask n) (P : ℤ) (mode : FilteredStream.Mode)
    (right : Array (LeafRecord n)) {d : ℕ} (C charge copyCharge : ℕ) (K : ℤ)
    (x : LeafRecord n × LeafRecord n) (xs : Array (LeafRecord n × LeafRecord n))
    (saved : CountedParentJoin.State I F P mode right d) (long : Bool) (fuel : ℕ)
    (r : StoredEntry.Dictionary I C) (budget : ℕ) :
    (run I F P mode right C charge copyCharge K x xs saved long fuel r budget).1 =
      BudgetedJoinOne.execute charge copyCharge (RepresentationKeys.read I F P mode right)
        (RepresentationKeys.pairKey I F P mode) K
        (StoredEntry.report I C (CountedRepresentationEmit.emit I F) x)
        (CountedParentJoin.snapshot I F P mode right) xs saved long fuel r budget := by
  unfold run BudgetedJoinOne.execute
  dsimp only
  split
  · simp only [buffer_value]
    cases hfirst : (BudgetedReplay.execute charge (fun i => (BufferReplay.read xs i, 4))
        (RepresentationKeys.pairKey I F P mode) K
        (StoredEntry.report I C (CountedRepresentationEmit.emit I F) x)
        xs.size 0 r 0 0 (budget - 6)).1 with
    | none => rfl
    | some p =>
      rcases p with ⟨out, left⟩
      dsimp only
      by_cases hh : out.halted = true
      · simp only [hh, ↓reduceIte]
      · simp only [hh, Bool.false_eq_true, ↓reduceIte]
        by_cases hl : long = true
        · simp only [hl, ↓reduceIte]
          by_cases hc : copyCharge ≤ left
          · simp only [hc, ↓reduceIte, RepresentationSnapshotCells.snapshot_value,
              RepresentationReplayCells.run_value]
          · simp only [hc, ↓reduceIte]
        · simp only [hl, Bool.false_eq_true, ↓reduceIte]
  · rfl

theorem run_cells (I : Instance n) (F : IndexedMask n) (P : ℤ) (mode : FilteredStream.Mode)
    (right : Array (LeafRecord n)) {d : ℕ} (C charge copyCharge : ℕ) (K : ℤ)
    (x : LeafRecord n × LeafRecord n) (xs : Array (LeafRecord n × LeafRecord n))
    (saved : CountedParentJoin.State I F P mode right d) (long : Bool) (fuel : ℕ)
    (r : StoredEntry.Dictionary I C) (budget : ℕ) (hn : 10000 ≤ n)
    (hd : d ≤ n) (ht : 2 ^ (d + 1) ≤ 4 * (C + 1)) (hxs : xs.size ≤ C) :
    (run I F P mode right C charge copyCharge K x xs saved long fuel r budget).2 ≤
      inputScale I ^ 6 * (C + 1) := by
  let u := inputScale I
  have hu : n + 1 ≤ u := by unfold u inputScale; omega
  have hc : 12 * n + 32 ≤ 44 * u := by omega
  have hm := Nat.mul_le_mul hc ht
  have hs : ParentLiveState.reader saved ≤ 176 * u * (C + 1) := by
    rw [ParentLiveState.reader_exact]
    nlinarith only [hm]
  have hdr := ParentLiveState.dictionary_scale I C r
  have hbuf := Nat.mul_le_mul_left (6 * n + 5) hxs
  have hret : (6 * n + 5) * xs.size + ParentLiveState.reader saved + ParentLiveState.dictionary r + 32 ≤
      300 * u * (C + 1) := by nlinarith only [hu, hn, hs, hdr, hbuf]
  have hfirst := buffer_cells I F P mode C charge K x xs r (budget - 6) hn
  change _ ≤ u ^ 5 * (C + 1) at hfirst
  have hcopy := RepresentationSnapshotCells.snapshot_cells I F P mode right saved C hd ht
  change _ ≤ 400 * u * (C + 1) at hcopy
  have hfinal : 2 * (u ^ 5 * (C + 1)) + 800 * u * (C + 1) + 100 ≤ u ^ 6 * (C + 1) := by
    have hl : 800 * u + 100 ≤ u ^ 5 := by
      have hp : u ≤ u ^ 4 := by
        simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ u) (by decide : 1 ≤ 4)
      have hp2 := Nat.mul_le_mul_left u hp
      have hbig : 900 ≤ u := by omega
      nlinarith only [hp2, hbig]
    have hm := Nat.mul_le_mul_right (C + 1) hl
    have hp : 3 * u ^ 5 ≤ u ^ 6 := by
      calc
        _ ≤ u * u ^ 5 := Nat.mul_le_mul_right _ (by omega)
        _ = _ := (pow_succ' _ _).symm
    have hq := Nat.mul_le_mul_right (C + 1) hp
    nlinarith only [hm, hq]
  change (run I F P mode right C charge copyCharge K x xs saved long fuel r budget).2 ≤ u ^ 6 * (C + 1)
  unfold run
  dsimp only
  split
  · cases hfirstOut : (buffer I F P mode C charge K x xs r (budget - 6)).1.1 with
    | none => dsimp only; nlinarith only [hret, hfirst, hfinal]
    | some p =>
      rcases p with ⟨out, left⟩
      have hdo := ParentLiveState.dictionary_scale I C out.state
      change _ ≤ 18 * u * (C + 1) + 8 at hdo
      dsimp only
      split
      · nlinarith only [hret, hfirst, hfinal]
      · split
        · split
          · have hrest := RepresentationReplayCells.run_cells I F P mode right C charge K x fuel
              (RepresentationSnapshotCells.snapshot I F P mode right saved).1.1
              out.state 0 0 (left - copyCharge) hn ht hd
            change _ ≤ u ^ 5 * (C + 1) at hrest
            dsimp only
            apply max_le
            · nlinarith only [hret, hfirst, hfinal]
            · apply max_le
              · nlinarith only [hret, hdo, hcopy, hfirst, hfinal]
              · nlinarith only [hret, hdo, hrest, hfinal]
          · nlinarith only [hret, hfirst, hfinal]
        · nlinarith only [hret, hfirst, hfinal]
  · dsimp only
    nlinarith only [hret, hfirst, hcopy, hfinal]

end LowSpaceSubsetSum.RepresentationOneCells

end OAI
