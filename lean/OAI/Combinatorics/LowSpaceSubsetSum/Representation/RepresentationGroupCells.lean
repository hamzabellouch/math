import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationTieOuterCells
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationObservationCells

namespace OAI

/-! # A concrete tie-group execution retaining its shared buffer

The trace includes the incoming pair of readers and dictionary, the completed
buffer, lookahead scratch, optional snapshot, and the actual outer replay.
Only the result state survives after this call returns.
-/

namespace LowSpaceSubsetSum.RepresentationGroupCells

variable {n : ℕ}

abbrev Left (I : Instance n) (F : IndexedMask n) (P : ℤ)
    (right : Array (LeafRecord n)) (d : ℕ) := CountedParentJoin.State I F P .direct right d

abbrev Right (I : Instance n) (F : IndexedMask n) (P t : ℤ)
    (right : Array (LeafRecord n)) (d : ℕ) := CountedParentJoin.State I F P (.complementary t) right d

def run (I : Instance n) (F : IndexedMask n) (P t : ℤ)
    (right₁ right₂ : Array (LeafRecord n)) {d₁ d₂ : ℕ}
    (C frontCharge fillCharge outerCharge charge copyCharge : ℕ) (K : ℤ)
    (B fuel₁ fuel₂ : ℕ) (s₁ : Left I F P right₁ d₁) (s₂ : Right I F P t right₂ d₂)
    (r : StoredEntry.Dictionary I C) (budget : ℕ) :
    (Option (TieGroup.Result (Left I F P right₁ d₁) (Right I F P t right₂ d₂)
      (StoredEntry.Dictionary I C) × ℕ) × ℕ) × ℕ :=
  let retained := ParentLiveState.reader s₁ + ParentLiveState.reader s₂ + ParentLiveState.dictionary r + 32
  if frontCharge ≤ budget then
    let filled := RepresentationFillCells.run I F P (.complementary t) right₂ fillCharge K B s₂
      (budget - frontCharge)
    let peak := retained + filled.2 + 16
    match filled.1.1 with
    | none => ((none, filled.1.2 + 1), peak)
    | some (f, left) =>
      let bufferCells := (6 * n + 5) * f.buffer.size + 1
      let long := RepresentationObservationCells.hasKey I F P (.complementary t) right₂ K f.cursor
      let present := RepresentationObservationCells.hasKey I F P .direct right₁ K s₁
      let snap := RepresentationObservationCells.snapshot I F P (.complementary t) right₂ copyCharge
        (long.1.1 && present.1.1) f.cursor left
      let peak := max peak (retained + bufferCells + ParentLiveState.reader f.cursor +
        long.2 + present.2 + snap.2 + 32)
      match snap.1.1 with
      | none => ((none, filled.1.2 + long.1.2 + present.1.2 + snap.1.2 + 8), peak)
      | some (saved, remaining) =>
        let out := RepresentationTieOuterCells.run I F P t right₁ right₂ C outerCharge charge copyCharge K
          f.buffer saved long.1.1 fuel₁ fuel₂ s₁ ⟨f.cursor, r, 0, 0, 0⟩ remaining
        ((out.1.1.map (fun (outer, rest) =>
          (⟨outer, f.queries, f.buffer.size, long.1.1 && present.1.1⟩, rest)),
          filled.1.2 + long.1.2 + present.1.2 + snap.1.2 + out.1.2 + 8),
          max peak (retained + bufferCells + ParentLiveState.reader f.cursor + out.2 + 32))
  else ((none, 1), retained)

theorem run_value (I : Instance n) (F : IndexedMask n) (P t : ℤ)
    (right₁ right₂ : Array (LeafRecord n)) {d₁ d₂ : ℕ}
    (C frontCharge fillCharge outerCharge charge copyCharge : ℕ) (K : ℤ)
    (B fuel₁ fuel₂ : ℕ) (s₁ : Left I F P right₁ d₁) (s₂ : Right I F P t right₂ d₂)
    (r : StoredEntry.Dictionary I C) (budget : ℕ) :
    (run I F P t right₁ right₂ C frontCharge fillCharge outerCharge charge copyCharge K
      B fuel₁ fuel₂ s₁ s₂ r budget).1 =
      BudgetedTieGroup.execute frontCharge fillCharge outerCharge charge copyCharge
        (RepresentationKeys.read I F P .direct right₁) (RepresentationKeys.pairKey I F P .direct)
        (RepresentationKeys.read I F P (.complementary t) right₂)
        (RepresentationKeys.pairKey I F P (.complementary t)) CountedParentJoin.cells K
        (StoredEntry.report I C (CountedRepresentationEmit.emit I F))
        (CountedParentJoin.snapshot I F P (.complementary t) right₂)
        B fuel₁ fuel₂ s₁ s₂ r budget := by
  unfold run BudgetedTieGroup.execute
  dsimp only
  split
  · simp only [RepresentationFillCells.run_value]
    cases hf : (BudgetedFill.execute fillCharge (RepresentationKeys.read I F P (.complementary t) right₂)
        (RepresentationKeys.pairKey I F P (.complementary t)) CountedParentJoin.cells K
        B s₂ #[] 0 (budget - frontCharge)).1 with
    | none => rfl
    | some p =>
      rcases p with ⟨f, left⟩
      dsimp only
      simp only [RepresentationObservationCells.hasKey_value, RepresentationObservationCells.snapshot_value]
      cases hs : (BudgetedSnapshot.execute copyCharge
          (CountedParentJoin.snapshot I F P (.complementary t) right₂)
          ((CountedFill.hasKey (RepresentationKeys.read I F P (.complementary t) right₂)
            (RepresentationKeys.pairKey I F P (.complementary t)) K f.cursor).1 &&
            (CountedFill.hasKey (RepresentationKeys.read I F P .direct right₁)
              (RepresentationKeys.pairKey I F P .direct) K s₁).1) f.cursor left).1 with
      | none => rfl
      | some p =>
        rcases p with ⟨saved, remaining⟩
        dsimp only
        simp only [RepresentationTieOuterCells.run_value]
  · rfl

private theorem peak_scale (u C : ℕ) (hu : 16 ≤ u) :
    16 * (u ^ 8 * (C + 1)) ≤ u ^ 9 * (C + 1) := by
  calc
    _ = (16 * u ^ 8) * (C + 1) := by ac_rfl
    _ ≤ (u * u ^ 8) * (C + 1) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hu)
    _ = _ := by rw [← pow_succ']

theorem run_cells (I : Instance n) (F : IndexedMask n) (P t : ℤ)
    (right₁ right₂ : Array (LeafRecord n)) {d₁ d₂ : ℕ}
    (C frontCharge fillCharge outerCharge charge copyCharge : ℕ) (K : ℤ)
    (B fuel₁ fuel₂ : ℕ) (s₁ : Left I F P right₁ d₁) (s₂ : Right I F P t right₂ d₂)
    (r : StoredEntry.Dictionary I C) (budget : ℕ) (hn : 10000 ≤ n)
    (hd₁ : d₁ ≤ n) (hd₂ : d₂ ≤ n)
    (ht₁ : 2 ^ (d₁ + 1) ≤ 4 * (C + 1)) (ht₂ : 2 ^ (d₂ + 1) ≤ 4 * (C + 1)) (hB : B ≤ C) :
    (run I F P t right₁ right₂ C frontCharge fillCharge outerCharge charge copyCharge K
      B fuel₁ fuel₂ s₁ s₂ r budget).2 ≤ inputScale I ^ 9 * (C + 1) := by
  let u := inputScale I
  let H := u ^ 8 * (C + 1)
  have hu : n + 1 ≤ u := by unfold u inputScale; omega
  have hup : 1 ≤ u := by omega
  have hbase : 1000 ≤ u ^ 7 := by
    have hp : u ≤ u ^ 7 := by
      simpa only [pow_one] using Nat.pow_le_pow_right hup (by decide : 1 ≤ 7)
    omega
  have hscale : 1000 * u ≤ u ^ 8 := by
    simpa only [pow_succ] using Nat.mul_le_mul_right u hbase
  have hsMul : 1000 * u * (C + 1) ≤ H := Nat.mul_le_mul_right (C + 1) hscale
  have huC : 1 ≤ u * (C + 1) := Nat.mul_pos hup (by omega)
  have hH : 32 ≤ H := by nlinarith only [hsMul, huC]
  have h5 : u ^ 5 * (C + 1) ≤ H :=
    Nat.mul_le_mul_right (C + 1) (Nat.pow_le_pow_right hup (by decide : 5 ≤ 8))
  have hl : ∀ st : Left I F P right₁ d₁, ParentLiveState.reader st ≤ H := by
    intro st
    have h := ParentLiveBounds.reader_le I F P .direct right₁ st C ht₁
    change _ ≤ 176 * u * (C + 1) at h
    nlinarith only [h, hsMul, huC]
  have hr : ∀ st : Right I F P t right₂ d₂, ParentLiveState.reader st ≤ H := by
    intro st
    have h := ParentLiveBounds.reader_le I F P (.complementary t) right₂ st C ht₂
    change _ ≤ 176 * u * (C + 1) at h
    nlinarith only [h, hsMul, huC]
  have hd : ∀ st : StoredEntry.Dictionary I C, ParentLiveState.dictionary st ≤ H := by
    intro st
    have h := ParentLiveState.dictionary_scale I C st
    change _ ≤ 18 * u * (C + 1) + 8 at h
    nlinarith only [h, hsMul, huC]
  have hret : ParentLiveState.reader s₁ + ParentLiveState.reader s₂ + ParentLiveState.dictionary r + 32 ≤
      4 * H := by have h₁ := hl s₁; have h₂ := hr s₂; have h₃ := hd r; omega
  have hfill := (RepresentationFillCells.run_cells I F P (.complementary t) right₂ fillCharge K B C
    s₂ (budget - frontCharge) hn hd₂ ht₂ hB).trans h5
  have hpeak :
      (run I F P t right₁ right₂ C frontCharge fillCharge outerCharge charge copyCharge K
        B fuel₁ fuel₂ s₁ s₂ r budget).2 ≤ 16 * H := by
    unfold run
    dsimp only
    split
    · cases hf : (RepresentationFillCells.run I F P (.complementary t) right₂ fillCharge K B s₂
          (budget - frontCharge)).1.1 with
      | none => dsimp only; omega
      | some p =>
        rcases p with ⟨f, left⟩
        have hcap : f.buffer.size ≤ C :=
          (RepresentationObservationCells.fill_capacity I F P (.complementary t) right₂ fillCharge K B
            s₂ (budget - frontCharge) f left hf).trans hB
        have hbuf := Nat.mul_le_mul_left (6 * n + 5) hcap
        have hbufH : (6 * n + 5) * f.buffer.size + 1 ≤ H := by
          nlinarith only [hbuf, hsMul, huC, hu]
        have hcursor := hr f.cursor
        have hlong := (RepresentationObservationCells.hasKey_cells I F P (.complementary t) right₂ K
          f.cursor C hn hd₂ ht₂).trans h5
        have hpresent := (RepresentationObservationCells.hasKey_cells I F P .direct right₁ K
          s₁ C hn hd₁ ht₁).trans h5
        have hsnap := (RepresentationObservationCells.snapshot_cells I F P (.complementary t) right₂
          copyCharge ((RepresentationObservationCells.hasKey I F P (.complementary t) right₂ K f.cursor).1.1 &&
            (RepresentationObservationCells.hasKey I F P .direct right₁ K s₁).1.1)
          f.cursor left C hn hd₂ ht₂).trans h5
        dsimp only
        cases hs : (RepresentationObservationCells.snapshot I F P (.complementary t) right₂ copyCharge
            ((RepresentationObservationCells.hasKey I F P (.complementary t) right₂ K f.cursor).1.1 &&
              (RepresentationObservationCells.hasKey I F P .direct right₁ K s₁).1.1) f.cursor left).1.1 with
        | none => dsimp only; omega
        | some p =>
          rcases p with ⟨saved, remaining⟩
          have ho := RepresentationTieOuterCells.run_cells I F P t right₁ right₂ C outerCharge charge copyCharge K
            f.buffer saved (RepresentationObservationCells.hasKey I F P (.complementary t) right₂ K f.cursor).1.1
            fuel₁ fuel₂ s₁ ⟨f.cursor, r, 0, 0, 0⟩ remaining hn hd₁ hd₂ ht₁ ht₂ hcap
          change _ ≤ H at ho
          dsimp only
          omega
    · dsimp only; omega
  exact hpeak.trans (peak_scale u C (by omega))

end LowSpaceSubsetSum.RepresentationGroupCells

end OAI
