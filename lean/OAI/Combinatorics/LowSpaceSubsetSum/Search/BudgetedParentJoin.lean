import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedJoinExecution
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.CountedParentJoin

namespace OAI

/-! # Concrete parent collection under a prepaid watchdog

All six per-operation charges are fixed from the input scale. The executable
never evaluates a reference run or its ledger to decide whether to continue.
-/

namespace LowSpaceSubsetSum.BudgetedParentJoin

variable {n : ℕ}

open CountedParentJoin (State)

def run (I : Instance n) (F : IndexedMask n) (P t : ℤ) (C B : ℕ)
    (right₁ right₂ : Array (LeafRecord n)) {d₁ d₂ : ℕ}
    (fuel₁ fuel₂ control : ℕ) (s₁ : State I F P .direct right₁ d₁)
    (s₂ : State I F P (.complementary t) right₂ d₂) (budget : ℕ) :=
  let charge := inputScale I ^ 6
  BudgetedJoinExecution.run charge charge charge charge charge B
    (RepresentationKeys.read I F P .direct right₁) (RepresentationKeys.pairKey I F P .direct)
    (RepresentationKeys.read I F P (.complementary t) right₂)
    (RepresentationKeys.pairKey I F P (.complementary t)) CountedParentJoin.cells
    (StoredEntry.report I C (CountedRepresentationEmit.emit I F))
    (CountedParentJoin.snapshot I F P (.complementary t) right₂)
    B fuel₁ fuel₂ control (StreamJoin.start s₁ s₂ (StoredEntry.empty I C)) budget

theorem charge_bound {n u : ℕ} (hnu : n ≤ u) (hu : 10000 ≤ u) :
    2 * u ^ 5 + 2 * u ^ 3 + u ^ 4 + (6 * n + 4) + 32 ≤ u ^ 6 := by
  have hpos : 1 ≤ u := by omega
  have h15 : u ≤ u ^ 5 := by simpa using Nat.pow_le_pow_right hpos (by decide : 1 ≤ 5)
  have h35 : u ^ 3 ≤ u ^ 5 := Nat.pow_le_pow_right hpos (by decide)
  have h45 : u ^ 4 ≤ u ^ 5 := Nat.pow_le_pow_right hpos (by decide)
  have h1 : 1 ≤ u ^ 5 := Nat.one_le_pow _ _ hpos
  have hs : 48 * u ^ 5 ≤ u ^ 6 := by
    calc
      _ ≤ u * u ^ 5 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' u 5).symm
  omega

/-- Every outcome, including interrupted ties, is covered by the input budget. -/
theorem run_work (I : Instance n) (F : IndexedMask n) (P t : ℤ) (C B : ℕ)
    (right₁ right₂ : Array (LeafRecord n)) {d₁ d₂ : ℕ}
    (fuel₁ fuel₂ control : ℕ) (s₁ : State I F P .direct right₁ d₁)
    (s₂ : State I F P (.complementary t) right₂ d₂) (budget : ℕ)
    (hn : 10000 ≤ n) (hd₁ : d₁ ≤ n) (hd₂ : d₂ ≤ n)
    (hcopy : (12 * n + 32) * 2 ^ (d₂ + 1) ≤ B) :
    (run I F P t C B right₁ right₂ fuel₁ fuel₂ control s₁ s₂ budget).2 ≤ budget + 1 := by
  have hnu : n ≤ inputScale I := by unfold inputScale; omega
  have hu : 10000 ≤ inputScale I := hn.trans hnu
  have hb := charge_bound hnu hu
  have h15 : inputScale I ≤ inputScale I ^ 5 := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ inputScale I) (by decide : 1 ≤ 5)
  have hm : max (inputScale I ^ 5) 4 = inputScale I ^ 5 := max_eq_left (by omega)
  exact BudgetedJoinExecution.run_work
    (RepresentationKeys.read I F P .direct right₁) (RepresentationKeys.pairKey I F P .direct)
    (RepresentationKeys.read I F P (.complementary t) right₂)
    (RepresentationKeys.pairKey I F P (.complementary t)) CountedParentJoin.cells
    (StoredEntry.report I C (CountedRepresentationEmit.emit I F))
    (CountedParentJoin.snapshot I F P (.complementary t) right₂)
    (inputScale I ^ 5) (inputScale I ^ 3) (inputScale I ^ 5) (inputScale I ^ 3)
    (6 * n + 4) (inputScale I ^ 4)
    (inputScale I ^ 6) (inputScale I ^ 6) (inputScale I ^ 6) (inputScale I ^ 6) (inputScale I ^ 6) B
    (fun s => RepresentationKeys.read_scale I F P .direct right₁ s hd₁ hn)
    (fun x => RepresentationKeys.pairKey_scale I F P .direct x hn)
    (fun s => RepresentationKeys.read_scale I F P (.complementary t) right₂ s hd₂ hn)
    (fun x => RepresentationKeys.pairKey_scale I F P (.complementary t) x hn)
    CountedParentJoin.cells_le (fun x y a => CountedParentJoin.report_work I F C x y a hn)
    (by omega) (by omega) (by omega) (by omega) (by rw [hm]; omega)
    (fun s => (CountedParentJoin.snapshot_work I F P (.complementary t) right₂ s).trans hcopy)
    B fuel₁ fuel₂ control (StreamJoin.start s₁ s₂ (StoredEntry.empty I C)) budget

theorem run_value (I : Instance n) (F : IndexedMask n) (P t : ℤ) (C B : ℕ)
    (right₁ right₂ : Array (LeafRecord n)) {d₁ d₂ : ℕ}
    (fuel₁ fuel₂ control : ℕ) (s₁ : State I F P .direct right₁ d₁)
    (s₂ : State I F P (.complementary t) right₂ d₂) (budget : ℕ)
    (out : StreamJoin.StoppedResult (State I F P .direct right₁ d₁)
      (State I F P (.complementary t) right₂ d₂) (StoredEntry.Dictionary I C)) (left : ℕ)
    (h : (run I F P t C B right₁ right₂ fuel₁ fuel₂ control s₁ s₂ budget).1 = some (out, left)) :
    out = (CountedParentJoin.run I F P t C B right₁ right₂ fuel₁ fuel₂ control s₁ s₂).1 ∧
      left ≤ budget :=
  BudgetedJoinExecution.run_value _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h

/-- The favorable-run bound pays for this real execution, without traversing unused fuel. -/
theorem run_complete (I : Instance n) (F : IndexedMask n) (P t : ℤ) (C B : ℕ)
    (right₁ right₂ : Array (LeafRecord n)) {d₁ d₂ : ℕ}
    (fuel₁ fuel₂ control : ℕ) (s₁ : State I F P .direct right₁ d₁)
    (s₂ : State I F P (.complementary t) right₂ d₂) (budget : ℕ) (hn : 10000 ≤ n)
    (hb : let out := (CountedParentJoin.run I F P t C B right₁ right₂ fuel₁ fuel₂ control s₁ s₂).1
      inputScale I ^ 7 * out.state.queries + B * out.state.copies + 4 ≤ budget) :
    ∃ left, (run I F P t C B right₁ right₂ fuel₁ fuel₂ control s₁ s₂ budget).1 =
      some ((CountedParentJoin.run I F P t C B right₁ right₂ fuel₁ fuel₂ control s₁ s₂).1, left) := by
  apply BudgetedJoinExecution.run_complete_queries
  · exact CountedParentJoin.snapshot_value I F P (.complementary t) right₂
  · have hnu : n ≤ inputScale I := by unfold inputScale; omega
    have hpos : 1 ≤ inputScale I := by omega
    have hp : 1 ≤ inputScale I ^ 6 := Nat.one_le_pow _ _ hpos
    have hm : 7 * inputScale I ^ 6 + 16 ≤ inputScale I ^ 7 := by
      have hs : 23 * inputScale I ^ 6 ≤ inputScale I ^ 7 := by
        calc
          _ ≤ inputScale I * inputScale I ^ 6 := Nat.mul_le_mul_right _ (by omega)
          _ = _ := (pow_succ' (inputScale I) 6).symm
      omega
    have hmul := Nat.mul_le_mul_right
      (CountedParentJoin.run I F P t C B right₁ right₂ fuel₁ fuel₂ control s₁ s₂).1.state.queries hm
    change _ ≤ budget
    dsimp only at hb
    have he : 2 * inputScale I ^ 6 + inputScale I ^ 6 + inputScale I ^ 6 + inputScale I ^ 6 +
        2 * inputScale I ^ 6 + 16 = 7 * inputScale I ^ 6 + 16 := by omega
    rw [he]
    exact (Nat.add_le_add_right (Nat.add_le_add_right hmul _) _).trans hb

end LowSpaceSubsetSum.BudgetedParentJoin

end OAI
