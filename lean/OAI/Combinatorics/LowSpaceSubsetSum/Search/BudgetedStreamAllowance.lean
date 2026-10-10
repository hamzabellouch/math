import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedStreamStep

namespace OAI

namespace LowSpaceSubsetSum.BudgetedStreamStep

universe u v s t w
variable {α : Type u} {β : Type v} {σ₁ : Type s} {σ₂ : Type t} {τ : Type w}

/-- Proof-only allowance for one comparison or one complete tie group. -/
def allowance (base front fill outer inner copy : ℕ)
    (read₁ : σ₁ → Option (α × σ₁) × ℕ) (key₁ : α → ℤ × ℕ)
    (read₂ : σ₂ → Option (β × σ₂) × ℕ) (key₂ : β → ℤ × ℕ)
    (cells : β → ℕ) (report : α → β → τ → (τ × Bool) × ℕ)
    (clone : σ₂ → σ₂ × ℕ) (B fuel₁ fuel₂ : ℕ) (st : StreamJoin.State σ₁ σ₂ τ) : ℕ :=
  if st.done then base else
  match (read₁ st.left).1 with
  | none => base
  | some (x, _) => match (read₂ st.right).1 with
    | none => base
    | some (y, _) =>
      if (key₁ x).1 < (key₂ y).1 then base
      else if (key₂ y).1 < (key₁ x).1 then base
      else base + BudgetedTieGroup.allowance front fill outer inner copy read₁ key₁ read₂ key₂
        cells (key₁ x).1 report clone B fuel₁ fuel₂ st.left st.right st.user

theorem execute_complete (base front fill outer inner copy : ℕ)
    (read₁ : σ₁ → Option (α × σ₁) × ℕ) (key₁ : α → ℤ × ℕ)
    (read₂ : σ₂ → Option (β × σ₂) × ℕ) (key₂ : β → ℤ × ℕ)
    (cells : β → ℕ) (report : α → β → τ → (τ × Bool) × ℕ)
    (clone : σ₂ → σ₂ × ℕ) (B fuel₁ fuel₂ : ℕ)
    (st : StreamJoin.State σ₁ σ₂ τ) (budget : ℕ)
    (hb : allowance base front fill outer inner copy read₁ key₁ read₂ key₂ cells report clone
      B fuel₁ fuel₂ st ≤ budget) :
    ∃ left, (execute base front fill outer inner copy read₁ key₁ read₂ key₂ cells report clone
      B fuel₁ fuel₂ st budget).1 =
      some ((CountedStreamJoin.step read₁ key₁ read₂ key₂ cells report clone B fuel₁ fuel₂ st).1, left) := by
  by_cases hd : st.done = true
  · simp only [allowance, hd, ↓reduceIte] at hb
    exact ⟨budget - base, by simp only [execute, hb, hd, ↓reduceIte, CountedStreamJoin.step]⟩
  · simp only [allowance, hd, Bool.false_eq_true, ↓reduceIte] at hb
    cases hx : (read₁ st.left).1 with
    | none =>
      simp only [hx] at hb
      exact ⟨budget - base, by simp only [execute, hb, hd, Bool.false_eq_true, ↓reduceIte, hx,
        CountedStreamJoin.step]⟩
    | some p =>
      rcases p with ⟨x, x'⟩
      simp only [hx] at hb
      cases hy : (read₂ st.right).1 with
      | none =>
        simp only [hy] at hb
        exact ⟨budget - base, by simp only [execute, hb, hd, Bool.false_eq_true, ↓reduceIte, hx, hy,
          CountedStreamJoin.step]⟩
      | some p =>
        rcases p with ⟨y, y'⟩
        simp only [hy] at hb
        by_cases hk : (key₁ x).1 < (key₂ y).1
        · simp only [hk, ↓reduceIte] at hb
          exact ⟨budget - base, by simp only [execute, hb, hd, Bool.false_eq_true, ↓reduceIte, hx, hy, hk,
            CountedStreamJoin.step]⟩
        · simp only [hk, ↓reduceIte] at hb
          by_cases hk' : (key₂ y).1 < (key₁ x).1
          · simp only [hk', ↓reduceIte] at hb
            exact ⟨budget - base, by simp only [execute, hb, hd, Bool.false_eq_true, ↓reduceIte, hx, hy, hk, hk',
              CountedStreamJoin.step]⟩
          · simp only [hk', ↓reduceIte] at hb
            have hbase : base ≤ budget := by omega
            obtain ⟨left, hg⟩ := BudgetedTieGroup.execute_complete front fill outer inner copy
              read₁ key₁ read₂ key₂ cells (key₁ x).1 report clone B fuel₁ fuel₂ st.left st.right st.user
              (budget - base) (by omega)
            refine ⟨left, ?_⟩
            simp only [execute, hbase, hd, Bool.false_eq_true, ↓reduceIte, hx, hy, hk, hk', hg,
              Option.map_some, CountedStreamJoin.step]
            rfl

end LowSpaceSubsetSum.BudgetedStreamStep

end OAI
