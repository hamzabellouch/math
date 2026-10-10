import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedParentJoin

namespace OAI

namespace LowSpaceSubsetSum.BudgetedJoinExecution

universe u v s t w
variable {α : Type u} {β : Type v} {σ₁ : Type s} {σ₂ : Type t} {τ : Type w}

theorem run_spent
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
    (B fuel₁ fuel₂ fuel : ℕ) (st : StreamJoin.State σ₁ σ₂ τ) (budget : ℕ)
    (out : StreamJoin.StoppedResult σ₁ σ₂ τ) (left : ℕ)
    (h : (run base front fill outer inner copy read₁ key₁ read₂ key₂ cells report clone
      B fuel₁ fuel₂ fuel st budget).1 = some (out, left)) :
    (run base front fill outer inner copy read₁ key₁ read₂ key₂ cells report clone
      B fuel₁ fuel₂ fuel st budget).2 ≤ budget - left := by
  simp only [run, BudgetedStoppedLoop.run_eq] at h ⊢
  exact (BudgetedStoppedJoin.execute_spent _ (fun s b v l he =>
    ⟨(BudgetedStreamStep.execute_value base front fill outer inner copy read₁ key₁ read₂ key₂ cells report clone
        B fuel₁ fuel₂ s b v l he).2,
      BudgetedStreamStep.execute_spent read₁ key₁ read₂ key₂ cells report clone
        R₁ L₁ R₂ L₂ S C base front fill outer inner copy hr₁ hk₁ hr₂ hk₂ hs hc hbase hfront hfill houter hinner hcopy
        B fuel₁ fuel₂ s b v l he⟩) fuel st budget out left h).2

end LowSpaceSubsetSum.BudgetedJoinExecution

namespace LowSpaceSubsetSum.BudgetedParentJoin

variable {n : ℕ}
open CountedParentJoin (State)

theorem run_spent (I : Instance n) (F : IndexedMask n) (P t : ℤ) (C B : ℕ)
    (right₁ right₂ : Array (LeafRecord n)) {d₁ d₂ : ℕ}
    (fuel₁ fuel₂ control : ℕ) (s₁ : State I F P .direct right₁ d₁)
    (s₂ : State I F P (.complementary t) right₂ d₂) (budget : ℕ)
    (hn : 10000 ≤ n) (hd₁ : d₁ ≤ n) (hd₂ : d₂ ≤ n)
    (hcopy : (12 * n + 32) * 2 ^ (d₂ + 1) ≤ B)
    (out : StreamJoin.StoppedResult (State I F P .direct right₁ d₁)
      (State I F P (.complementary t) right₂ d₂) (StoredEntry.Dictionary I C)) (left : ℕ)
    (h : (run I F P t C B right₁ right₂ fuel₁ fuel₂ control s₁ s₂ budget).1 = some (out, left)) :
    (run I F P t C B right₁ right₂ fuel₁ fuel₂ control s₁ s₂ budget).2 ≤ budget - left := by
  have hnu : n ≤ inputScale I := by unfold inputScale; omega
  have hu : 10000 ≤ inputScale I := hn.trans hnu
  have hb := charge_bound hnu hu
  have h15 : inputScale I ≤ inputScale I ^ 5 := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ inputScale I) (by decide : 1 ≤ 5)
  have hm : max (inputScale I ^ 5) 4 = inputScale I ^ 5 := max_eq_left (by omega)
  exact BudgetedJoinExecution.run_spent
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
    B fuel₁ fuel₂ control (StreamJoin.start s₁ s₂ (StoredEntry.empty I C)) budget out left h

end LowSpaceSubsetSum.BudgetedParentJoin

end OAI
