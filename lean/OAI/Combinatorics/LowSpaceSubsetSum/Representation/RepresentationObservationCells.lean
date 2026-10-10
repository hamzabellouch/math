import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationFillCells
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationSnapshotCells

namespace OAI

/-! # Lookahead, conditional snapshots and the exact fill capacity

Lookahead may construct a next reader state, which is discarded afterward.
Both that state and the original reader are included in the live trace.
-/

namespace LowSpaceSubsetSum.RepresentationObservationCells

variable {n : ℕ}

private theorem fillAcc_size {α σ : Type*} (read : σ → Option (α × σ) × ℕ)
    (key : α → ℤ × ℕ) (cells : α → ℕ) (K : ℤ) (fuel : ℕ) (s : σ) (buf : Array α) (q : ℕ) :
    (CountedFill.fillAcc read key cells K fuel s buf q).1.buffer.size ≤ buf.size + fuel := by
  induction fuel generalizing s buf q with
  | zero => simp only [CountedFill.fillAcc]; omega
  | succ fuel ih =>
    rw [CountedFill.fillAcc]
    dsimp only
    cases hr : (read s).1 with
    | none => dsimp only; omega
    | some p =>
      rcases p with ⟨x, s'⟩
      dsimp only
      split
      · have h := ih s' (buf.push x) (q + 1)
        simpa only [Array.size_push, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
      · dsimp only; omega

theorem fill_capacity (I : Instance n) (F : IndexedMask n) (P : ℤ) (mode : FilteredStream.Mode)
    (right : Array (LeafRecord n)) {d : ℕ} (charge : ℕ) (K : ℤ) (B : ℕ)
    (s : CountedParentJoin.State I F P mode right d) (budget : ℕ)
    (out : TieBuffer.Result (LeafRecord n × LeafRecord n) (CountedParentJoin.State I F P mode right d))
    (left : ℕ)
    (h : (RepresentationFillCells.run I F P mode right charge K B s budget).1.1 = some (out, left)) :
    out.buffer.size ≤ B := by
  have he := congrArg Prod.fst (RepresentationFillCells.run_value I F P mode right charge K B s budget)
  have hv := BudgetedFill.execute_value charge (RepresentationKeys.read I F P mode right)
    (RepresentationKeys.pairKey I F P mode) CountedParentJoin.cells K B s #[] 0 budget out left
    (he.symm.trans h)
  rw [hv.1]
  simpa only [Array.size_empty, Nat.zero_add] using fillAcc_size
    (RepresentationKeys.read I F P mode right) (RepresentationKeys.pairKey I F P mode)
    CountedParentJoin.cells K B s #[] 0

def hasKey (I : Instance n) (F : IndexedMask n) (P : ℤ) (mode : FilteredStream.Mode)
    (right : Array (LeafRecord n)) {d : ℕ} (K : ℤ) (s : CountedParentJoin.State I F P mode right d) :
    (Bool × ℕ) × ℕ :=
  let fetched := RepresentationReaderCells.read I F P mode right s
  match fetched.1.1 with
  | none => ((false, fetched.1.2 + 3), ParentLiveState.reader s + fetched.2 + 8)
  | some (x, s') =>
    let found := RepresentationKeyCells.pairKey I F P mode x
    ((decide (found.1.1 = K), fetched.1.2 + found.1.2 + 4),
      max (ParentLiveState.reader s + fetched.2 + 8)
        (ParentLiveState.reader s + ParentLiveState.reader s' + CountedParentJoin.cells x + found.2 + 16))

theorem hasKey_value (I : Instance n) (F : IndexedMask n) (P : ℤ) (mode : FilteredStream.Mode)
    (right : Array (LeafRecord n)) {d : ℕ} (K : ℤ) (s : CountedParentJoin.State I F P mode right d) :
    (hasKey I F P mode right K s).1 = CountedFill.hasKey
      (RepresentationKeys.read I F P mode right) (RepresentationKeys.pairKey I F P mode) K s := by
  simp only [hasKey, CountedFill.hasKey, RepresentationReaderCells.read_value,
    RepresentationKeyCells.pairKey_value]
  cases hr : (RepresentationKeys.read I F P mode right s).1 <;> rfl

theorem hasKey_cells (I : Instance n) (F : IndexedMask n) (P : ℤ) (mode : FilteredStream.Mode)
    (right : Array (LeafRecord n)) {d : ℕ} (K : ℤ) (s : CountedParentJoin.State I F P mode right d)
    (C : ℕ) (hn : 10000 ≤ n) (hd : d ≤ n) (ht : 2 ^ (d + 1) ≤ 4 * (C + 1)) :
    (hasKey I F P mode right K s).2 ≤ inputScale I ^ 5 * (C + 1) := by
  let u := inputScale I
  have hu : n + 1 ≤ u := by unfold u inputScale; omega
  have hc : 12 * n + 32 ≤ 44 * u := by omega
  have hm := Nat.mul_le_mul hc ht
  have hs : ∀ st : CountedParentJoin.State I F P mode right d,
      ParentLiveState.reader st ≤ 176 * u * (C + 1) := by
    intro st
    rw [ParentLiveState.reader_exact]
    nlinarith only [hm]
  have hr := RepresentationReaderCells.read_scale I F P mode right s C hn hd ht
  change _ ≤ u ^ 4 * (C + 1) at hr
  have hs₀ := hs s
  have hcoef : u ^ 4 + 500 * u ≤ u ^ 5 := by
    have hsmall : 500 * u ≤ u ^ 4 := by
      have hpow : u ≤ u ^ 3 := by
        simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ u) (by decide : 1 ≤ 3)
      have hp := Nat.mul_le_mul_left u hpow
      nlinarith only [hp, hu, hn]
    have hmul := Nat.mul_le_mul_right (u ^ 4) (by omega : 2 ≤ u)
    nlinarith only [hsmall, hmul]
  have hfinal := Nat.mul_le_mul_right (C + 1) hcoef
  change _ ≤ u ^ 5 * (C + 1)
  unfold hasKey
  dsimp only
  cases hout : (RepresentationReaderCells.read I F P mode right s).1.1 with
  | none => dsimp only; nlinarith only [hs₀, hr, hfinal, hu, hn]
  | some p =>
    rcases p with ⟨x, s'⟩
    have hs₁ := hs s'
    have hx := CountedParentJoin.cells_le x
    have hk := RepresentationKeyCells.pairKey_cells I F P mode x
    dsimp only
    apply max_le <;> nlinarith only [hs₀, hs₁, hr, hx, hk, hfinal, hu, hn]

def snapshot (I : Instance n) (F : IndexedMask n) (P : ℤ) (mode : FilteredStream.Mode)
    (right : Array (LeafRecord n)) {d : ℕ} (charge : ℕ) (needed : Bool)
    (s : CountedParentJoin.State I F P mode right d) (budget : ℕ) :
    (Option (CountedParentJoin.State I F P mode right d × ℕ) × ℕ) × ℕ :=
  if needed then
    if charge ≤ budget then
      let out := RepresentationSnapshotCells.snapshot I F P mode right s
      ((some (out.1.1, budget - charge), out.1.2), out.2 + 8)
    else ((none, 1), 8)
  else ((some (s, budget), 0), 8)

theorem snapshot_value (I : Instance n) (F : IndexedMask n) (P : ℤ) (mode : FilteredStream.Mode)
    (right : Array (LeafRecord n)) {d : ℕ} (charge : ℕ) (needed : Bool)
    (s : CountedParentJoin.State I F P mode right d) (budget : ℕ) :
    (snapshot I F P mode right charge needed s budget).1 =
      BudgetedSnapshot.execute charge (CountedParentJoin.snapshot I F P mode right) needed s budget := by
  simp only [snapshot, BudgetedSnapshot.execute, RepresentationSnapshotCells.snapshot_value]
  split
  · split <;> rfl
  · rfl

theorem snapshot_cells (I : Instance n) (F : IndexedMask n) (P : ℤ) (mode : FilteredStream.Mode)
    (right : Array (LeafRecord n)) {d : ℕ} (charge : ℕ) (needed : Bool)
    (s : CountedParentJoin.State I F P mode right d) (budget C : ℕ)
    (hn : 10000 ≤ n) (hd : d ≤ n) (ht : 2 ^ (d + 1) ≤ 4 * (C + 1)) :
    (snapshot I F P mode right charge needed s budget).2 ≤ inputScale I ^ 5 * (C + 1) := by
  have hs := RepresentationSnapshotCells.snapshot_cells I F P mode right s C hd ht
  have hu : n + 1 ≤ inputScale I := by unfold inputScale; omega
  have hbound : 400 * inputScale I + 8 ≤ inputScale I ^ 5 := by
    have hp : inputScale I ≤ inputScale I ^ 4 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ inputScale I) (by decide : 1 ≤ 4)
    have hm := Nat.mul_le_mul_left (inputScale I) hp
    nlinarith only [hm, hu, hn]
  have hm := Nat.mul_le_mul_right (C + 1) hbound
  unfold snapshot
  split
  · split <;> dsimp only <;> nlinarith only [hs, hm, hu, hn]
  · dsimp only; nlinarith only [hm, hu, hn]

end LowSpaceSubsetSum.RepresentationObservationCells

end OAI
