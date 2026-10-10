import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationStepCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.BudgetedStoppedCells

namespace OAI

/-! # Live cells of the complete prepaid parent join

The stopped driver keeps a single current state. Each iteration includes its
concrete reader, key, tie-buffer, snapshot and dictionary trace. Immutable
leaf arrays are retained once by the outer wrapper.
-/

namespace LowSpaceSubsetSum.RepresentationJoinCells

variable {n : ℕ}

open RepresentationStepCells (State)

def run (I : Instance n) (F : IndexedMask n) (P t : ℤ)
    (right₁ right₂ : Array (LeafRecord n)) {d₁ d₂ : ℕ}
    (C base front fill outer inner copy B fuel₁ fuel₂ control : ℕ)
    (st : State I F P t right₁ right₂ d₁ d₂ C) (budget : ℕ) :=
  BudgetedStoppedCells.run
    (RepresentationStepCells.run I F P t right₁ right₂ C base front fill outer inner copy B fuel₁ fuel₂)
    ParentLiveState.frame control st budget

theorem run_value (I : Instance n) (F : IndexedMask n) (P t : ℤ)
    (right₁ right₂ : Array (LeafRecord n)) {d₁ d₂ : ℕ}
    (C base front fill outer inner copy B fuel₁ fuel₂ control : ℕ)
    (st : State I F P t right₁ right₂ d₁ d₂ C) (budget : ℕ) :
    (run I F P t right₁ right₂ C base front fill outer inner copy B fuel₁ fuel₂ control st budget).1 =
      BudgetedJoinExecution.run base front fill outer inner copy
        (RepresentationKeys.read I F P .direct right₁) (RepresentationKeys.pairKey I F P .direct)
        (RepresentationKeys.read I F P (.complementary t) right₂)
        (RepresentationKeys.pairKey I F P (.complementary t)) CountedParentJoin.cells
        (StoredEntry.report I C (CountedRepresentationEmit.emit I F))
        (CountedParentJoin.snapshot I F P (.complementary t) right₂) B fuel₁ fuel₂ control st budget := by
  rw [run, BudgetedStoppedCells.run_value]
  have he : (fun (s : State I F P t right₁ right₂ d₁ d₂ C) (b : ℕ) =>
      (RepresentationStepCells.run I F P t right₁ right₂ C base front fill outer inner copy B fuel₁ fuel₂ s b).1) =
      BudgetedStreamStep.execute base front fill outer inner copy
        (RepresentationKeys.read I F P .direct right₁) (RepresentationKeys.pairKey I F P .direct)
        (RepresentationKeys.read I F P (.complementary t) right₂)
        (RepresentationKeys.pairKey I F P (.complementary t)) CountedParentJoin.cells
        (StoredEntry.report I C (CountedRepresentationEmit.emit I F))
        (CountedParentJoin.snapshot I F P (.complementary t) right₂) B fuel₁ fuel₂ := by
    funext s b
    exact RepresentationStepCells.run_value I F P t right₁ right₂ C base front fill outer inner copy B fuel₁ fuel₂ s b
  rw [he]

private theorem scale (u C : ℕ) (hu : 10000 ≤ u) :
    2 * (400 * u * (C + 1)) + u ^ 10 * (C + 1) + 32 ≤ u ^ 11 * (C + 1) := by
  have hp : u ≤ u ^ 10 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ u) (by decide : 1 ≤ 10)
  have h1 : 1 ≤ u ^ 10 := Nat.one_le_pow _ _ (by omega)
  have hq : 833 * u ^ 10 ≤ u ^ 11 := by
    calc
      _ ≤ u * u ^ 10 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' _ _).symm
  have hs : 800 * u + u ^ 10 + 32 ≤ u ^ 11 := by omega
  have hm := Nat.mul_le_mul_right (C + 1) hs
  nlinarith only [hm]

theorem run_cells (I : Instance n) (F : IndexedMask n) (P t : ℤ)
    (right₁ right₂ : Array (LeafRecord n)) {d₁ d₂ : ℕ}
    (C base front fill outer inner copy B fuel₁ fuel₂ control : ℕ)
    (st : State I F P t right₁ right₂ d₁ d₂ C) (budget : ℕ) (hn : 10000 ≤ n)
    (hd₁ : d₁ ≤ n) (hd₂ : d₂ ≤ n)
    (ht₁ : 2 ^ (d₁ + 1) ≤ 4 * (C + 1)) (ht₂ : 2 ^ (d₂ + 1) ≤ 4 * (C + 1)) (hB : B ≤ C) :
    (run I F P t right₁ right₂ C base front fill outer inner copy B fuel₁ fuel₂ control st budget).2 ≤
      inputScale I ^ 11 * (C + 1) := by
  have h := BudgetedStoppedCells.run_cells
    (RepresentationStepCells.run I F P t right₁ right₂ C base front fill outer inner copy B fuel₁ fuel₂)
    ParentLiveState.frame (400 * inputScale I * (C + 1)) (inputScale I ^ 10 * (C + 1))
    (fun s => ParentLiveBounds.frame_le I F P t C right₁ right₂ s ht₁ ht₂)
    (fun s b => RepresentationStepCells.run_cells I F P t right₁ right₂ C base front fill outer inner copy
      B fuel₁ fuel₂ s b hn hd₁ hd₂ ht₁ ht₂ hB) control st budget
  exact h.trans (scale _ _ (by unfold inputScale; omega))

def parent (I : Instance n) (F : IndexedMask n) (P t : ℤ) (C B : ℕ)
    (right₁ right₂ : Array (LeafRecord n)) {d₁ d₂ : ℕ}
    (fuel₁ fuel₂ control : ℕ) (s₁ : RepresentationGroupCells.Left I F P right₁ d₁)
    (s₂ : RepresentationGroupCells.Right I F P t right₂ d₂) (budget : ℕ) :=
  let charge := inputScale I ^ 6
  run I F P t right₁ right₂ C charge charge charge charge charge B B fuel₁ fuel₂ control
    (StreamJoin.start s₁ s₂ (StoredEntry.empty I C)) budget

theorem parent_value (I : Instance n) (F : IndexedMask n) (P t : ℤ) (C B : ℕ)
    (right₁ right₂ : Array (LeafRecord n)) {d₁ d₂ : ℕ}
    (fuel₁ fuel₂ control : ℕ) (s₁ : RepresentationGroupCells.Left I F P right₁ d₁)
    (s₂ : RepresentationGroupCells.Right I F P t right₂ d₂) (budget : ℕ) :
    (parent I F P t C B right₁ right₂ fuel₁ fuel₂ control s₁ s₂ budget).1 =
      BudgetedParentJoin.run I F P t C B right₁ right₂ fuel₁ fuel₂ control s₁ s₂ budget :=
  run_value I F P t right₁ right₂ C _ _ _ _ _ _ _ _ _ _ _ _

theorem parent_cells (I : Instance n) (F : IndexedMask n) (P t : ℤ) (C B : ℕ)
    (right₁ right₂ : Array (LeafRecord n)) {d₁ d₂ : ℕ}
    (fuel₁ fuel₂ control : ℕ) (s₁ : RepresentationGroupCells.Left I F P right₁ d₁)
    (s₂ : RepresentationGroupCells.Right I F P t right₂ d₂) (budget : ℕ) (hn : 10000 ≤ n)
    (hd₁ : d₁ ≤ n) (hd₂ : d₂ ≤ n)
    (ht₁ : 2 ^ (d₁ + 1) ≤ 4 * (C + 1)) (ht₂ : 2 ^ (d₂ + 1) ≤ 4 * (C + 1)) (hB : B ≤ C) :
    (parent I F P t C B right₁ right₂ fuel₁ fuel₂ control s₁ s₂ budget).2 ≤ inputScale I ^ 11 * (C + 1) :=
  run_cells I F P t right₁ right₂ C _ _ _ _ _ _ _ _ _ _ _ _ hn hd₁ hd₂ ht₁ ht₂ hB

/-- Explicitly shared arrays are retained once throughout the stopped execution. -/
def withArrays (I : Instance n) (F : IndexedMask n) (P t : ℤ) (C B : ℕ)
    (left₁ right₁ left₂ right₂ : Array (LeafRecord n)) {d₁ d₂ : ℕ}
    (fuel₁ fuel₂ control : ℕ) (s₁ : RepresentationGroupCells.Left I F P right₁ d₁)
    (s₂ : RepresentationGroupCells.Right I F P t right₂ d₂) (budget : ℕ) :=
  let out := parent I F P t C B right₁ right₂ fuel₁ fuel₂ control s₁ s₂ budget
  (out.1, out.2 + ParentLiveState.sharedArrays left₁ right₁ + ParentLiveState.sharedArrays left₂ right₂ + 16)

theorem withArrays_cells (I : Instance n) (F : IndexedMask n) (P t : ℤ) (C B : ℕ)
    (left₁ right₁ left₂ right₂ : Array (LeafRecord n)) {d₁ d₂ : ℕ}
    (fuel₁ fuel₂ control : ℕ) (s₁ : RepresentationGroupCells.Left I F P right₁ d₁)
    (s₂ : RepresentationGroupCells.Right I F P t right₂ d₂) (budget : ℕ) (hn : 10000 ≤ n)
    (hd₁ : d₁ ≤ n) (hd₂ : d₂ ≤ n)
    (ht₁ : 2 ^ (d₁ + 1) ≤ 4 * (C + 1)) (ht₂ : 2 ^ (d₂ + 1) ≤ 4 * (C + 1)) (hB : B ≤ C)
    (hl₁ : left₁.size ≤ C) (hr₁ : right₁.size ≤ C) (hl₂ : left₂.size ≤ C) (hr₂ : right₂.size ≤ C) :
    (withArrays I F P t C B left₁ right₁ left₂ right₂ fuel₁ fuel₂ control s₁ s₂ budget).2 ≤
      inputScale I ^ 12 * (C + 1) := by
  have hp := parent_cells I F P t C B right₁ right₂ fuel₁ fuel₂ control s₁ s₂ budget hn hd₁ hd₂ ht₁ ht₂ hB
  have ha := ParentLiveBounds.shared_le I C left₁ right₁ hl₁ hr₁
  have hb := ParentLiveBounds.shared_le I C left₂ right₂ hl₂ hr₂
  have hu : 10000 ≤ inputScale I := by unfold inputScale; omega
  have hx : 16 * inputScale I + 16 ≤ inputScale I ^ 11 := by
    have hp : inputScale I ≤ inputScale I ^ 10 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ inputScale I) (by decide : 1 ≤ 10)
    have hq : 32 * inputScale I ^ 10 ≤ inputScale I ^ 11 := by
      calc
        _ ≤ inputScale I * inputScale I ^ 10 := Nat.mul_le_mul_right _ (by omega)
        _ = _ := (pow_succ' _ _).symm
    omega
  have hmul : 2 * inputScale I ^ 11 ≤ inputScale I ^ 12 := by
    calc
      _ ≤ inputScale I * inputScale I ^ 11 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' _ _).symm
  have hfinal := Nat.mul_le_mul_right (C + 1) hmul
  have hsmall := Nat.mul_le_mul_right (C + 1) hx
  change _ + _ + _ + 16 ≤ _
  nlinarith only [hp, ha, hb, hsmall, hfinal]

end LowSpaceSubsetSum.RepresentationJoinCells

end OAI
