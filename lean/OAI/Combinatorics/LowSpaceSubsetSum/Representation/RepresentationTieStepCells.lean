import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationOneCells

namespace OAI

/-! # Live cells of one prepaid outer tie callback -/

namespace LowSpaceSubsetSum.RepresentationTieStepCells

variable {n : ℕ}

abbrev State (I : Instance n) (F : IndexedMask n) (P : ℤ) (mode : FilteredStream.Mode)
    (right : Array (LeafRecord n)) (d C : ℕ) :=
  TieGroup.State (CountedParentJoin.State I F P mode right d) (StoredEntry.Dictionary I C)

def payload {I : Instance n} {F : IndexedMask n} {P : ℤ} {mode : FilteredStream.Mode}
    {right : Array (LeafRecord n)} {d C : ℕ} (st : State I F P mode right d C) :=
  ParentLiveState.reader st.last + ParentLiveState.dictionary st.user + 32

def run (I : Instance n) (F : IndexedMask n) (P : ℤ) (mode : FilteredStream.Mode)
    (right : Array (LeafRecord n)) {d : ℕ} (C charge copyCharge : ℕ) (K : ℤ)
    (xs : Array (LeafRecord n × LeafRecord n)) (saved : CountedParentJoin.State I F P mode right d)
    (long : Bool) (fuel : ℕ) (x : LeafRecord n × LeafRecord n)
    (st : State I F P mode right d C) (budget : ℕ) :=
  if 6 ≤ budget then
    let inner := RepresentationOneCells.run I F P mode right C charge copyCharge K x xs saved long
      fuel st.user (budget - 6)
    ((inner.1.1.map (fun (out, left) => (BudgetedTieStep.result long st out, left)), inner.1.2 + 6),
      payload st + inner.2 + 32)
  else ((none, 1), payload st + 8)

theorem run_value (I : Instance n) (F : IndexedMask n) (P : ℤ) (mode : FilteredStream.Mode)
    (right : Array (LeafRecord n)) {d : ℕ} (C charge copyCharge : ℕ) (K : ℤ)
    (xs : Array (LeafRecord n × LeafRecord n)) (saved : CountedParentJoin.State I F P mode right d)
    (long : Bool) (fuel : ℕ) (x : LeafRecord n × LeafRecord n)
    (st : State I F P mode right d C) (budget : ℕ) :
    (run I F P mode right C charge copyCharge K xs saved long fuel x st budget).1 =
      BudgetedTieStep.execute charge copyCharge (RepresentationKeys.read I F P mode right)
        (RepresentationKeys.pairKey I F P mode) K
        (StoredEntry.report I C (CountedRepresentationEmit.emit I F))
        (CountedParentJoin.snapshot I F P mode right) xs saved long fuel x st budget := by
  simp only [run, BudgetedTieStep.execute, RepresentationOneCells.run_value]
  split <;> rfl

theorem payload_le (I : Instance n) (F : IndexedMask n) (P : ℤ) (mode : FilteredStream.Mode)
    (right : Array (LeafRecord n)) {d : ℕ} (C : ℕ) (st : State I F P mode right d C)
    (ht : 2 ^ (d + 1) ≤ 4 * (C + 1)) :
    payload st ≤ 250 * inputScale I * (C + 1) := by
  have hu : n + 1 ≤ inputScale I := by unfold inputScale; omega
  have hc : 12 * n + 32 ≤ 44 * inputScale I := by omega
  have hm := Nat.mul_le_mul hc ht
  have hs : ParentLiveState.reader st.last ≤ 176 * inputScale I * (C + 1) := by
    rw [ParentLiveState.reader_exact]
    nlinarith only [hm]
  have hd := ParentLiveState.dictionary_scale I C st.user
  unfold payload
  nlinarith only [hs, hd, hu]

theorem run_cells (I : Instance n) (F : IndexedMask n) (P : ℤ) (mode : FilteredStream.Mode)
    (right : Array (LeafRecord n)) {d : ℕ} (C charge copyCharge : ℕ) (K : ℤ)
    (xs : Array (LeafRecord n × LeafRecord n)) (saved : CountedParentJoin.State I F P mode right d)
    (long : Bool) (fuel : ℕ) (x : LeafRecord n × LeafRecord n)
    (st : State I F P mode right d C) (budget : ℕ) (hn : 10000 ≤ n)
    (hd : d ≤ n) (ht : 2 ^ (d + 1) ≤ 4 * (C + 1)) (hxs : xs.size ≤ C) :
    (run I F P mode right C charge copyCharge K xs saved long fuel x st budget).2 ≤
      inputScale I ^ 7 * (C + 1) := by
  let u := inputScale I
  have hp := payload_le I F P mode right C st ht
  have hi := RepresentationOneCells.run_cells I F P mode right C charge copyCharge K x xs saved long
    fuel st.user (budget - 6) hn hd ht hxs
  have hu : n + 1 ≤ u := by unfold u inputScale; omega
  change _ ≤ 250 * u * (C + 1) at hp
  change _ ≤ u ^ 6 * (C + 1) at hi
  have hlow : 250 * u + 32 ≤ u ^ 6 := by
    have hpow : u ≤ u ^ 5 := by
      simpa only [pow_one] using
        Nat.pow_le_pow_right (by omega : 1 ≤ u) (by decide : 1 ≤ 5)
    have hmul := Nat.mul_le_mul_left u hpow
    have hlarge : 1000 ≤ u := by omega
    nlinarith only [hmul, hlarge]
  have hmul := Nat.mul_le_mul_right (C + 1) hlow
  have hpow : 2 * u ^ 6 ≤ u ^ 7 := by
    calc
      _ ≤ u * u ^ 6 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' _ _).symm
  have hfinal := Nat.mul_le_mul_right (C + 1) hpow
  change (run I F P mode right C charge copyCharge K xs saved long fuel x st budget).2 ≤ u ^ 7 * (C + 1)
  unfold run
  split <;> dsimp only <;> nlinarith only [hp, hi, hmul, hfinal]

end LowSpaceSubsetSum.RepresentationTieStepCells

end OAI
