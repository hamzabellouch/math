import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedStoppedLoop
import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedStreamPotential

namespace OAI

namespace LowSpaceSubsetSum.BudgetedJoinExecution

universe u v s t w
variable {α : Type u} {β : Type v} {σ₁ : Type s} {σ₂ : Type t} {τ : Type w}

abbrev step (base front fill outer inner copy : ℕ)
    (read₁ : σ₁ → Option (α × σ₁) × ℕ) (key₁ : α → ℤ × ℕ)
    (read₂ : σ₂ → Option (β × σ₂) × ℕ) (key₂ : β → ℤ × ℕ)
    (cells : β → ℕ) (report : α → β → τ → (τ × Bool) × ℕ)
    (clone : σ₂ → σ₂ × ℕ) (B fuel₁ fuel₂ : ℕ) :=
  BudgetedStreamStep.execute base front fill outer inner copy read₁ key₁ read₂ key₂ cells report clone B fuel₁ fuel₂

abbrev run (base front fill outer inner copy : ℕ)
    (read₁ : σ₁ → Option (α × σ₁) × ℕ) (key₁ : α → ℤ × ℕ)
    (read₂ : σ₂ → Option (β × σ₂) × ℕ) (key₂ : β → ℤ × ℕ)
    (cells : β → ℕ) (report : α → β → τ → (τ × Bool) × ℕ)
    (clone : σ₂ → σ₂ × ℕ) (B fuel₁ fuel₂ : ℕ) :=
  BudgetedStoppedLoop.run
    (step base front fill outer inner copy read₁ key₁ read₂ key₂ cells report clone B fuel₁ fuel₂)

theorem reference_eq (read₁ : σ₁ → Option (α × σ₁) × ℕ) (key₁ : α → ℤ × ℕ)
    (read₂ : σ₂ → Option (β × σ₂) × ℕ) (key₂ : β → ℤ × ℕ)
    (cells : β → ℕ) (report : α → β → τ → (τ × Bool) × ℕ)
    (clone : σ₂ → σ₂ × ℕ) (B fuel₁ fuel₂ fuel : ℕ) (st : StreamJoin.State σ₁ σ₂ τ) :
    BudgetedStoppedJoin.reference
      (fun s => (CountedStreamJoin.step read₁ key₁ read₂ key₂ cells report clone B fuel₁ fuel₂ s).1) fuel st =
    (CountedStreamJoin.runAcc read₁ key₁ read₂ key₂ cells report clone B fuel₁ fuel₂ fuel st).1 := by
  induction fuel generalizing st with
  | zero => rfl
  | succ fuel ih =>
    simp only [BudgetedStoppedJoin.reference, CountedStreamJoin.runAcc]
    split <;> simp only [ih]

theorem run_value (base front fill outer inner copy : ℕ)
    (read₁ : σ₁ → Option (α × σ₁) × ℕ) (key₁ : α → ℤ × ℕ)
    (read₂ : σ₂ → Option (β × σ₂) × ℕ) (key₂ : β → ℤ × ℕ)
    (cells : β → ℕ) (report : α → β → τ → (τ × Bool) × ℕ)
    (clone : σ₂ → σ₂ × ℕ) (B fuel₁ fuel₂ fuel : ℕ)
    (st : StreamJoin.State σ₁ σ₂ τ) (budget : ℕ) (out : StreamJoin.StoppedResult σ₁ σ₂ τ) (left : ℕ)
    (h : (run base front fill outer inner copy read₁ key₁ read₂ key₂ cells report clone
      B fuel₁ fuel₂ fuel st budget).1 = some (out, left)) :
    out = (CountedStreamJoin.runAcc read₁ key₁ read₂ key₂ cells report clone B fuel₁ fuel₂ fuel st).1 ∧
      left ≤ budget := by
  simp only [run, BudgetedStoppedLoop.run_eq] at h
  have hv := BudgetedStoppedJoin.execute_value
    (step base front fill outer inner copy read₁ key₁ read₂ key₂ cells report clone B fuel₁ fuel₂)
    (fun s => (CountedStreamJoin.step read₁ key₁ read₂ key₂ cells report clone B fuel₁ fuel₂ s).1)
    (BudgetedStreamStep.execute_value base front fill outer inner copy read₁ key₁ read₂ key₂ cells report clone B fuel₁ fuel₂)
    fuel st budget out left h
  rw [reference_eq] at hv
  exact hv

theorem run_work
    (read₁ : σ₁ → Option (α × σ₁) × ℕ) (key₁ : α → ℤ × ℕ)
    (read₂ : σ₂ → Option (β × σ₂) × ℕ) (key₂ : β → ℤ × ℕ)
    (cells : β → ℕ) (report : α → β → τ → (τ × Bool) × ℕ) (clone : σ₂ → σ₂ × ℕ)
    (R₁ L₁ R₂ L₂ S C base front fill outer inner copy : ℕ)
    (hr₁ : ∀ s, (read₁ s).2 ≤ R₁) (hk₁ : ∀ x, (key₁ x).2 ≤ L₁)
    (hr₂ : ∀ s, (read₂ s).2 ≤ R₂) (hk₂ : ∀ y, (key₂ y).2 ≤ L₂)
    (hs : ∀ y, cells y ≤ S) (hc : ∀ x y a, (report x y a).2 ≤ C)
    (hbase : R₁ + L₁ + R₂ + L₂ + 16 ≤ base)
    (hfront : R₁ + L₁ + R₂ + L₂ + 16 ≤ front)
    (hfill : R₂ + L₂ + S + 8 ≤ fill) (houter : R₁ + L₁ + 8 ≤ outer)
    (hinner : max R₂ 4 + L₂ + C + 8 ≤ inner) (hcopy : ∀ s, (clone s).2 ≤ copy)
    (B fuel₁ fuel₂ fuel : ℕ) (st : StreamJoin.State σ₁ σ₂ τ) (budget : ℕ) :
    (run base front fill outer inner copy read₁ key₁ read₂ key₂ cells report clone
      B fuel₁ fuel₂ fuel st budget).2 ≤ budget + 1 := by
  simp only [run, BudgetedStoppedLoop.run_eq]
  apply BudgetedStoppedJoin.execute_work
  · exact BudgetedStreamStep.execute_work read₁ key₁ read₂ key₂ cells report clone
      R₁ L₁ R₂ L₂ S C base front fill outer inner copy hr₁ hk₁ hr₂ hk₂ hs hc hbase hfront hfill houter hinner hcopy
      B fuel₁ fuel₂
  · intro s b out left h
    exact ⟨(BudgetedStreamStep.execute_value base front fill outer inner copy read₁ key₁ read₂ key₂ cells report clone
      B fuel₁ fuel₂ s b out left h).2,
      BudgetedStreamStep.execute_spent read₁ key₁ read₂ key₂ cells report clone
        R₁ L₁ R₂ L₂ S C base front fill outer inner copy hr₁ hk₁ hr₂ hk₂ hs hc hbase hfront hfill houter hinner hcopy
        B fuel₁ fuel₂ s b out left h⟩

theorem run_complete (base front fill outer inner copy : ℕ)
    (read₁ : σ₁ → Option (α × σ₁) × ℕ) (key₁ : α → ℤ × ℕ)
    (read₂ : σ₂ → Option (β × σ₂) × ℕ) (key₂ : β → ℤ × ℕ)
    (cells : β → ℕ) (report : α → β → τ → (τ × Bool) × ℕ)
    (clone : σ₂ → σ₂ × ℕ) (B fuel₁ fuel₂ fuel : ℕ)
    (st : StreamJoin.State σ₁ σ₂ τ) (budget : ℕ)
    (hb : let out := (CountedStreamJoin.runAcc read₁ key₁ read₂ key₂ cells report clone B fuel₁ fuel₂ fuel st).1
      (base + front + fill + outer + 2 * inner + 12) * out.state.queries + copy * out.state.copies +
        (base + 4) * out.steps + 4 ≤ budget) :
    ∃ left, (run base front fill outer inner copy read₁ key₁ read₂ key₂ cells report clone
      B fuel₁ fuel₂ fuel st budget).1 =
      some ((CountedStreamJoin.runAcc read₁ key₁ read₂ key₂ cells report clone B fuel₁ fuel₂ fuel st).1, left) := by
  let pure := fun s => (CountedStreamJoin.step read₁ key₁ read₂ key₂ cells report clone B fuel₁ fuel₂ s).1
  let bill := BudgetedStreamStep.allowance base front fill outer inner copy read₁ key₁ read₂ key₂ cells report clone B fuel₁ fuel₂
  let M := base + front + fill + outer + 2 * inner + 12
  have hp := BudgetedStoppedJoin.allowance_potential pure bill (CountedStreamJoin.potential M 0 copy) base
    (BudgetedStreamStep.allowance_potential base front fill outer inner copy read₁ key₁ read₂ key₂ cells report clone B fuel₁ fuel₂)
    fuel st
  rw [reference_eq] at hp
  simp only [CountedStreamJoin.potential, Nat.zero_mul, Nat.add_zero] at hp
  have ha : BudgetedStoppedJoin.allowance pure bill fuel st ≤ budget := by
    dsimp only [M] at hp
    omega
  have h := BudgetedStoppedJoin.execute_complete
    (step base front fill outer inner copy read₁ key₁ read₂ key₂ cells report clone B fuel₁ fuel₂) pure bill
    (BudgetedStreamStep.execute_complete base front fill outer inner copy read₁ key₁ read₂ key₂ cells report clone B fuel₁ fuel₂)
    (BudgetedStreamStep.execute_remaining base front fill outer inner copy read₁ key₁ read₂ key₂ cells report clone B fuel₁ fuel₂)
    fuel st budget ha
  simpa only [run, BudgetedStoppedLoop.run_eq, pure, reference_eq] using h

/-- From fresh cursors, every control iteration performs at least one query. -/
theorem run_complete_queries (base front fill outer inner copy : ℕ)
    (read₁ : σ₁ → Option (α × σ₁) × ℕ) (key₁ : α → ℤ × ℕ)
    (read₂ : σ₂ → Option (β × σ₂) × ℕ) (key₂ : β → ℤ × ℕ)
    (cells : β → ℕ) (report : α → β → τ → (τ × Bool) × ℕ)
    (clone : σ₂ → σ₂ × ℕ) (hclone : ∀ s, (clone s).1 = s)
    (B fuel₁ fuel₂ fuel : ℕ) (s₁ : σ₁) (s₂ : σ₂) (a : τ) (budget : ℕ)
    (hb : let out := (CountedStreamJoin.runAcc read₁ key₁ read₂ key₂ cells report clone B fuel₁ fuel₂ fuel
        (StreamJoin.start s₁ s₂ a)).1
      (2 * base + front + fill + outer + 2 * inner + 16) * out.state.queries +
        copy * out.state.copies + 4 ≤ budget) :
    ∃ left, (run base front fill outer inner copy read₁ key₁ read₂ key₂ cells report clone
      B fuel₁ fuel₂ fuel (StreamJoin.start s₁ s₂ a) budget).1 =
      some ((CountedStreamJoin.runAcc read₁ key₁ read₂ key₂ cells report clone B fuel₁ fuel₂ fuel
        (StreamJoin.start s₁ s₂ a)).1, left) := by
  have hv := CountedStreamJoin.runAcc_value read₁ key₁ read₂ key₂ cells report clone hclone
    B fuel₁ fuel₂ fuel (StreamJoin.start s₁ s₂ a)
  have hq := StreamJoin.stopped_steps_le_queries (fun s => (read₁ s).1) (fun x => (key₁ x).1)
    (fun s => (read₂ s).1) (fun x => (key₂ x).1) (fun x y a => (report x y a).1)
    B fuel₁ fuel₂ fuel s₁ s₂ a
  rw [← StreamJoin.stopped_eq] at hq
  change (StreamJoin.stoppedAcc _ _ _ _ _ _ _ _ _ _).steps ≤
    (StreamJoin.stoppedAcc _ _ _ _ _ _ _ _ _ _).state.queries at hq
  rw [← hv] at hq
  have hm := Nat.mul_le_mul_left (base + 4) hq
  apply run_complete
  have he : 2 * base + front + fill + outer + 2 * inner + 16 =
      (base + front + fill + outer + 2 * inner + 12) + (base + 4) := by omega
  dsimp only at hb
  rw [he, Nat.add_mul] at hb
  omega

end LowSpaceSubsetSum.BudgetedJoinExecution

end OAI
