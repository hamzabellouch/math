import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationTieStepCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.BudgetedOuterCells
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.ParentLiveBounds

namespace OAI

/-! # Live cells of the complete outer traversal of one tie group

The buffer and saved second reader form a shared callback context. Each outer
iteration releases its old reader and user state before the tail call; inner
buffer/suffix replay uses the concrete bounded-list callbacks.
-/

namespace LowSpaceSubsetSum.RepresentationTieOuterCells

variable {n : ℕ}

def run (I : Instance n) (F : IndexedMask n) (P t : ℤ)
    (right₁ right₂ : Array (LeafRecord n)) {d₁ d₂ : ℕ}
    (C outerCharge charge copyCharge : ℕ) (K : ℤ)
    (xs : Array (LeafRecord n × LeafRecord n))
    (saved : CountedParentJoin.State I F P (.complementary t) right₂ d₂)
    (long : Bool) (fuel₁ fuel₂ : ℕ) (s₁ : CountedParentJoin.State I F P .direct right₁ d₁)
    (st : RepresentationTieStepCells.State I F P (.complementary t) right₂ d₂ C) (budget : ℕ) :=
  let out := BudgetedOuterCells.run outerCharge (RepresentationReaderCells.read I F P .direct right₁)
    (RepresentationKeyCells.pairKey I F P .direct) K
    (RepresentationTieStepCells.run I F P (.complementary t) right₂ C charge copyCharge K xs saved long fuel₂)
    ParentLiveState.reader RepresentationTieStepCells.payload CountedParentJoin.cells
    fuel₁ s₁ st 0 0 budget
  (out.1, out.2 + (6 * n + 5) * xs.size + ParentLiveState.reader saved + 16)

theorem run_value (I : Instance n) (F : IndexedMask n) (P t : ℤ)
    (right₁ right₂ : Array (LeafRecord n)) {d₁ d₂ : ℕ}
    (C outerCharge charge copyCharge : ℕ) (K : ℤ)
    (xs : Array (LeafRecord n × LeafRecord n))
    (saved : CountedParentJoin.State I F P (.complementary t) right₂ d₂)
    (long : Bool) (fuel₁ fuel₂ : ℕ) (s₁ : CountedParentJoin.State I F P .direct right₁ d₁)
    (st : RepresentationTieStepCells.State I F P (.complementary t) right₂ d₂ C) (budget : ℕ) :
    (run I F P t right₁ right₂ C outerCharge charge copyCharge K xs saved long fuel₁ fuel₂ s₁ st budget).1 =
      BudgetedTieOuter.execute outerCharge charge copyCharge
        (RepresentationKeys.read I F P .direct right₁) (RepresentationKeys.pairKey I F P .direct)
        (RepresentationKeys.read I F P (.complementary t) right₂)
        (RepresentationKeys.pairKey I F P (.complementary t)) K
        (StoredEntry.report I C (CountedRepresentationEmit.emit I F))
        (CountedParentJoin.snapshot I F P (.complementary t) right₂)
        xs saved long fuel₁ fuel₂ s₁ st budget := by
  rw [run, BudgetedOuterCells.run_value]
  have hr : (fun s : CountedParentJoin.State I F P .direct right₁ d₁ =>
      (RepresentationReaderCells.read I F P .direct right₁ s).1) =
      RepresentationKeys.read I F P .direct right₁ :=
    funext (RepresentationReaderCells.read_value I F P .direct right₁)
  have hk : (fun x => (RepresentationKeyCells.pairKey I F P .direct x).1) =
      RepresentationKeys.pairKey I F P .direct := funext (RepresentationKeyCells.pairKey_value I F P .direct)
  have hp : (fun x st b =>
      (RepresentationTieStepCells.run I F P (.complementary t) right₂ C charge copyCharge K
        xs saved long fuel₂ x st b).1) =
      BudgetedTieStep.execute charge copyCharge (RepresentationKeys.read I F P (.complementary t) right₂)
        (RepresentationKeys.pairKey I F P (.complementary t)) K
        (StoredEntry.report I C (CountedRepresentationEmit.emit I F))
        (CountedParentJoin.snapshot I F P (.complementary t) right₂) xs saved long fuel₂ := by
    funext x st b
    exact RepresentationTieStepCells.run_value I F P (.complementary t) right₂ C charge copyCharge K
      xs saved long fuel₂ x st b
  rw [hr, hk, hp]
  rfl

private theorem outer_bound (u n C a b c : ℕ) (hn : 10000 ≤ n) (hu : n + 1 ≤ u)
    (ha : a ≤ 2 * (176 * u * (C + 1)) + 2 * (250 * u * (C + 1)) +
      (6 * n + 4) + u ^ 4 * (C + 1) + 44 * u + u ^ 7 * (C + 1) + 64)
    (hb : b ≤ 176 * u * (C + 1)) (hc : c ≤ (6 * n + 5) * C) :
    a + c + b + 16 ≤ u ^ 8 * (C + 1) := by
  have hsmall : a + c + b + 16 ≤ (u ^ 7 + u ^ 4 + 1200 * u) * (C + 1) := by
    nlinarith only [ha, hb, hc, hu, hn]
  have hp : 1200 * u ≤ u ^ 4 := by
    have hpow : u ≤ u ^ 3 := by
      simpa only [pow_one] using
        Nat.pow_le_pow_right (by omega : 1 ≤ u) (by decide : 1 ≤ 3)
    have hm := Nat.mul_le_mul_left u hpow
    nlinarith only [hm, hu, hn]
  have h47 : 2 * u ^ 4 ≤ u ^ 7 := by
    have hs : 2 ≤ u ^ 3 := by
      calc
        2 ≤ 2 ^ 3 := by norm_num
        _ ≤ u ^ 3 := Nat.pow_le_pow_left (by omega) 3
    calc
      2 * u ^ 4 ≤ u ^ 3 * u ^ 4 := Nat.mul_le_mul_right _ hs
      _ = u ^ 7 := by rw [← pow_add]
  have h78 : 2 * u ^ 7 ≤ u ^ 8 := by
    calc
      _ ≤ u * u ^ 7 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' _ _).symm
  exact hsmall.trans (Nat.mul_le_mul_right (C + 1) (by omega))

theorem run_cells (I : Instance n) (F : IndexedMask n) (P t : ℤ)
    (right₁ right₂ : Array (LeafRecord n)) {d₁ d₂ : ℕ}
    (C outerCharge charge copyCharge : ℕ) (K : ℤ)
    (xs : Array (LeafRecord n × LeafRecord n))
    (saved : CountedParentJoin.State I F P (.complementary t) right₂ d₂)
    (long : Bool) (fuel₁ fuel₂ : ℕ) (s₁ : CountedParentJoin.State I F P .direct right₁ d₁)
    (st : RepresentationTieStepCells.State I F P (.complementary t) right₂ d₂ C) (budget : ℕ)
    (hn : 10000 ≤ n) (hd₁ : d₁ ≤ n) (hd₂ : d₂ ≤ n)
    (ht₁ : 2 ^ (d₁ + 1) ≤ 4 * (C + 1)) (ht₂ : 2 ^ (d₂ + 1) ≤ 4 * (C + 1))
    (hxs : xs.size ≤ C) :
    (run I F P t right₁ right₂ C outerCharge charge copyCharge K xs saved long fuel₁ fuel₂ s₁ st budget).2 ≤
      inputScale I ^ 8 * (C + 1) := by
  let u := inputScale I
  have hu : n + 1 ≤ u := by unfold u inputScale; omega
  have hkey : ∀ x, (RepresentationKeyCells.pairKey I F P .direct x).2 ≤ 44 * u := by
    intro x
    exact (RepresentationKeyCells.pairKey_cells I F P .direct x).trans (by omega)
  have h := BudgetedOuterCells.run_cells outerCharge (RepresentationReaderCells.read I F P .direct right₁)
    (RepresentationKeyCells.pairKey I F P .direct) K
    (RepresentationTieStepCells.run I F P (.complementary t) right₂ C charge copyCharge K xs saved long fuel₂)
    ParentLiveState.reader RepresentationTieStepCells.payload CountedParentJoin.cells
    (176 * u * (C + 1)) (250 * u * (C + 1)) (6 * n + 4) (u ^ 4 * (C + 1)) (44 * u)
    (u ^ 7 * (C + 1)) (fun s => ParentLiveBounds.reader_le I F P .direct right₁ s C ht₁)
    (fun st => RepresentationTieStepCells.payload_le I F P (.complementary t) right₂ C st ht₂)
    CountedParentJoin.cells_le
    (fun s => RepresentationReaderCells.read_scale I F P .direct right₁ s C hn hd₁ ht₁) hkey
    (fun x st b => RepresentationTieStepCells.run_cells I F P (.complementary t) right₂ C charge copyCharge K
      xs saved long fuel₂ x st b hn hd₂ ht₂ hxs) fuel₁ s₁ st 0 0 budget
  have hs := ParentLiveBounds.reader_le I F P (.complementary t) right₂ saved C ht₂
  have hbuf := Nat.mul_le_mul_left (6 * n + 5) hxs
  change _ ≤ u ^ 8 * (C + 1)
  exact outer_bound u n C _ _ _ hn hu h hs hbuf

end LowSpaceSubsetSum.RepresentationTieOuterCells

end OAI
