import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationReaderCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.BudgetedFillCells

namespace OAI

/-! # Concrete bounded-space filling of a representation tie buffer -/

namespace LowSpaceSubsetSum.RepresentationFillCells

variable {n : ℕ}

def run (I : Instance n) (F : IndexedMask n) (P : ℤ) (mode : FilteredStream.Mode)
    (right : Array (LeafRecord n)) {d : ℕ} (charge : ℕ) (K : ℤ) (B : ℕ)
    (s : CountedParentJoin.State I F P mode right d) (budget : ℕ) :=
  BudgetedFillCells.run charge (RepresentationReaderCells.read I F P mode right)
    (RepresentationKeyCells.pairKey I F P mode) CountedParentJoin.cells ParentLiveState.reader
    K B s budget

theorem run_value (I : Instance n) (F : IndexedMask n) (P : ℤ) (mode : FilteredStream.Mode)
    (right : Array (LeafRecord n)) {d : ℕ} (charge : ℕ) (K : ℤ) (B : ℕ)
    (s : CountedParentJoin.State I F P mode right d) (budget : ℕ) :
    (run I F P mode right charge K B s budget).1 =
      BudgetedFill.execute charge (RepresentationKeys.read I F P mode right)
        (RepresentationKeys.pairKey I F P mode) CountedParentJoin.cells K B s #[] 0 budget := by
  rw [run, BudgetedFillCells.run_value]
  have hr : (fun s : CountedParentJoin.State I F P mode right d =>
      (RepresentationReaderCells.read I F P mode right s).1) =
      RepresentationKeys.read I F P mode right :=
    funext (RepresentationReaderCells.read_value I F P mode right)
  have hk : (fun x => (RepresentationKeyCells.pairKey I F P mode x).1) =
      RepresentationKeys.pairKey I F P mode :=
    funext (RepresentationKeyCells.pairKey_value I F P mode)
  rw [hr, hk]

theorem run_cells (I : Instance n) (F : IndexedMask n) (P : ℤ) (mode : FilteredStream.Mode)
    (right : Array (LeafRecord n)) {d : ℕ} (charge : ℕ) (K : ℤ) (B C : ℕ)
    (s : CountedParentJoin.State I F P mode right d) (budget : ℕ)
    (hn : 10000 ≤ n) (hd : d ≤ n) (ht : 2 ^ (d + 1) ≤ 4 * (C + 1)) (hB : B ≤ C) :
    (run I F P mode right charge K B s budget).2 ≤ inputScale I ^ 5 * (C + 1) := by
  let u := inputScale I
  have hu : n + 1 ≤ u := by unfold u inputScale; omega
  have hc : 12 * n + 32 ≤ 44 * u := by omega
  have hsc := Nat.mul_le_mul hc ht
  have hs : ∀ st : CountedParentJoin.State I F P mode right d,
      ParentLiveState.reader st ≤ 176 * u * (C + 1) := by
    intro st
    rw [ParentLiveState.reader_exact]
    nlinarith only [hsc]
  have hl : ∀ x, (RepresentationKeyCells.pairKey I F P mode x).2 ≤ 44 * u := by
    intro x
    exact (RepresentationKeyCells.pairKey_cells I F P mode x).trans hc
  have h := BudgetedFillCells.run_cells charge (RepresentationReaderCells.read I F P mode right)
    (RepresentationKeyCells.pairKey I F P mode) CountedParentJoin.cells ParentLiveState.reader K
    (u ^ 4 * (C + 1)) (44 * u) (176 * u * (C + 1)) (6 * n + 4)
    (fun st => RepresentationReaderCells.read_scale I F P mode right st C hn hd ht)
    hl hs CountedParentJoin.cells_le B s budget
  have hbuf := Nat.mul_le_mul_left (6 * n + 5) hB
  have hsmall : (run I F P mode right charge K B s budget).2 ≤
      (u ^ 4 + 500 * u) * (C + 1) := by
    change (run I F P mode right charge K B s budget).2 ≤ _ at h
    nlinarith only [h, hbuf, hu]
  have hu3 : 500 ≤ u ^ 3 := by
    calc
      500 ≤ 8 ^ 3 := by norm_num
      _ ≤ u ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hm := Nat.mul_le_mul_right u hu3
  have hp : 500 * u ≤ u ^ 4 := by simpa only [pow_succ, Nat.mul_assoc] using hm
  have hfactor : 2 * u ^ 4 ≤ u ^ 5 := by
    calc
      _ ≤ u * u ^ 4 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' _ _).symm
  change (run I F P mode right charge K B s budget).2 ≤ u ^ 5 * (C + 1)
  exact hsmall.trans (Nat.mul_le_mul_right (C + 1) (by omega))

end LowSpaceSubsetSum.RepresentationFillCells

end OAI
