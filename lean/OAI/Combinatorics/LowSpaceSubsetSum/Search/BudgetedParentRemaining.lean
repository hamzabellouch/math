import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedParentJoin

namespace OAI

namespace LowSpaceSubsetSum.BudgetedJoinExecution

universe u v s t w
variable {α : Type u} {β : Type v} {σ₁ : Type s} {σ₂ : Type t} {τ : Type w}

theorem run_remaining (base front fill outer inner copy : ℕ)
    (read₁ : σ₁ → Option (α × σ₁) × ℕ) (key₁ : α → ℤ × ℕ)
    (read₂ : σ₂ → Option (β × σ₂) × ℕ) (key₂ : β → ℤ × ℕ)
    (cells : β → ℕ) (report : α → β → τ → (τ × Bool) × ℕ)
    (clone : σ₂ → σ₂ × ℕ) (B fuel₁ fuel₂ fuel : ℕ)
    (st : StreamJoin.State σ₁ σ₂ τ) (budget : ℕ) (out : StreamJoin.StoppedResult σ₁ σ₂ τ) (left : ℕ)
    (h : (run base front fill outer inner copy read₁ key₁ read₂ key₂ cells report clone
      B fuel₁ fuel₂ fuel st budget).1 = some (out, left)) :
    budget ≤ left + (base + front + fill + outer + 2 * inner + 12) * out.state.queries +
      copy * out.state.copies + (base + 4) * out.steps + 4 := by
  let pure := fun s => (CountedStreamJoin.step read₁ key₁ read₂ key₂ cells report clone B fuel₁ fuel₂ s).1
  let bill := BudgetedStreamStep.allowance base front fill outer inner copy read₁ key₁ read₂ key₂ cells report clone B fuel₁ fuel₂
  let M := base + front + fill + outer + 2 * inner + 12
  have hr := BudgetedStoppedJoin.execute_remaining
    (step base front fill outer inner copy read₁ key₁ read₂ key₂ cells report clone B fuel₁ fuel₂) pure bill
    (fun s b v l he => (BudgetedStreamStep.execute_value base front fill outer inner copy read₁ key₁ read₂ key₂ cells
      report clone B fuel₁ fuel₂ s b v l he).1)
    (BudgetedStreamStep.execute_remaining base front fill outer inner copy read₁ key₁ read₂ key₂ cells report clone B fuel₁ fuel₂)
    fuel st budget out left (by simpa only [run, BudgetedStoppedLoop.run_eq] using h)
  have hp := BudgetedStoppedJoin.allowance_potential pure bill (CountedStreamJoin.potential M 0 copy) base
    (BudgetedStreamStep.allowance_potential base front fill outer inner copy read₁ key₁ read₂ key₂ cells report clone B fuel₁ fuel₂)
    fuel st
  dsimp only [pure] at hr hp
  rw [reference_eq] at hp
  rw [← (run_value base front fill outer inner copy read₁ key₁ read₂ key₂ cells report clone
    B fuel₁ fuel₂ fuel st budget out left h).1] at hp
  simp only [CountedStreamJoin.potential, Nat.zero_mul, Nat.add_zero] at hp
  dsimp only [M] at hp
  omega

theorem run_remaining_queries (base front fill outer inner copy : ℕ)
    (read₁ : σ₁ → Option (α × σ₁) × ℕ) (key₁ : α → ℤ × ℕ)
    (read₂ : σ₂ → Option (β × σ₂) × ℕ) (key₂ : β → ℤ × ℕ)
    (cells : β → ℕ) (report : α → β → τ → (τ × Bool) × ℕ)
    (clone : σ₂ → σ₂ × ℕ) (hclone : ∀ s, (clone s).1 = s)
    (B fuel₁ fuel₂ fuel : ℕ) (s₁ : σ₁) (s₂ : σ₂) (a : τ) (budget : ℕ)
    (out : StreamJoin.StoppedResult σ₁ σ₂ τ) (left : ℕ)
    (h : (run base front fill outer inner copy read₁ key₁ read₂ key₂ cells report clone
      B fuel₁ fuel₂ fuel (StreamJoin.start s₁ s₂ a) budget).1 = some (out, left)) :
    budget ≤ left + (2 * base + front + fill + outer + 2 * inner + 16) * out.state.queries +
      copy * out.state.copies + 4 := by
  have hr := run_remaining base front fill outer inner copy read₁ key₁ read₂ key₂ cells report clone
    B fuel₁ fuel₂ fuel (StreamJoin.start s₁ s₂ a) budget out left h
  have hv := (run_value base front fill outer inner copy read₁ key₁ read₂ key₂ cells report clone
    B fuel₁ fuel₂ fuel (StreamJoin.start s₁ s₂ a) budget out left h).1
  have hs := CountedStreamJoin.runAcc_value read₁ key₁ read₂ key₂ cells report clone hclone
    B fuel₁ fuel₂ fuel (StreamJoin.start s₁ s₂ a)
  have hq := StreamJoin.stopped_steps_le_queries (fun s => (read₁ s).1) (fun x => (key₁ x).1)
    (fun s => (read₂ s).1) (fun x => (key₂ x).1) (fun x y a => (report x y a).1)
    B fuel₁ fuel₂ fuel s₁ s₂ a
  rw [← StreamJoin.stopped_eq] at hq
  change (StreamJoin.stoppedAcc _ _ _ _ _ _ _ _ _ _).steps ≤
    (StreamJoin.stoppedAcc _ _ _ _ _ _ _ _ _ _).state.queries at hq
  rw [← hs, ← hv] at hq
  have hm := Nat.mul_le_mul_left (base + 4) hq
  have he : 2 * base + front + fill + outer + 2 * inner + 16 =
      (base + front + fill + outer + 2 * inner + 12) + (base + 4) := by omega
  rw [he, Nat.add_mul]
  omega

end LowSpaceSubsetSum.BudgetedJoinExecution

namespace LowSpaceSubsetSum.BudgetedParentJoin

variable {n : ℕ}
open CountedParentJoin (State)

theorem run_remaining (I : Instance n) (F : IndexedMask n) (P t : ℤ) (C B : ℕ)
    (right₁ right₂ : Array (LeafRecord n)) {d₁ d₂ : ℕ}
    (fuel₁ fuel₂ control : ℕ) (s₁ : State I F P .direct right₁ d₁)
    (s₂ : State I F P (.complementary t) right₂ d₂) (budget : ℕ) (hn : 10000 ≤ n)
    (out : StreamJoin.StoppedResult (State I F P .direct right₁ d₁)
      (State I F P (.complementary t) right₂ d₂) (StoredEntry.Dictionary I C)) (left : ℕ)
    (h : (run I F P t C B right₁ right₂ fuel₁ fuel₂ control s₁ s₂ budget).1 = some (out, left)) :
    budget ≤ left + inputScale I ^ 7 * out.state.queries + B * out.state.copies + 4 := by
  have hr := BudgetedJoinExecution.run_remaining_queries
    (inputScale I ^ 6) (inputScale I ^ 6) (inputScale I ^ 6) (inputScale I ^ 6) (inputScale I ^ 6) B
    (RepresentationKeys.read I F P .direct right₁) (RepresentationKeys.pairKey I F P .direct)
    (RepresentationKeys.read I F P (.complementary t) right₂)
    (RepresentationKeys.pairKey I F P (.complementary t)) CountedParentJoin.cells
    (StoredEntry.report I C (CountedRepresentationEmit.emit I F))
    (CountedParentJoin.snapshot I F P (.complementary t) right₂)
    (CountedParentJoin.snapshot_value I F P (.complementary t) right₂)
    B fuel₁ fuel₂ control s₁ s₂ (StoredEntry.empty I C) budget out left h
  have hu : 10000 ≤ inputScale I := by unfold inputScale; omega
  have hp : 1 ≤ inputScale I ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hm : 7 * inputScale I ^ 6 + 16 ≤ inputScale I ^ 7 := by
    have hs : 23 * inputScale I ^ 6 ≤ inputScale I ^ 7 := by
      calc
        _ ≤ inputScale I * inputScale I ^ 6 := Nat.mul_le_mul_right _ (by omega)
        _ = _ := (pow_succ' (inputScale I) 6).symm
    omega
  have hmul := Nat.mul_le_mul_right out.state.queries hm
  have he : 2 * inputScale I ^ 6 + inputScale I ^ 6 + inputScale I ^ 6 + inputScale I ^ 6 +
      2 * inputScale I ^ 6 + 16 = 7 * inputScale I ^ 6 + 16 := by omega
  rw [he] at hr
  omega

end LowSpaceSubsetSum.BudgetedParentJoin

end OAI
