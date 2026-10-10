import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedStreamContracts

namespace OAI

namespace LowSpaceSubsetSum.BudgetedStreamStep

universe u v s t w
variable {α : Type u} {β : Type v} {σ₁ : Type s} {σ₂ : Type t} {τ : Type w}

/-- All nested prepaid charges are covered by the actual query and copy ledger. -/
theorem allowance_potential (base front fill outer inner copy : ℕ)
    (read₁ : σ₁ → Option (α × σ₁) × ℕ) (key₁ : α → ℤ × ℕ)
    (read₂ : σ₂ → Option (β × σ₂) × ℕ) (key₂ : β → ℤ × ℕ)
    (cells : β → ℕ) (report : α → β → τ → (τ × Bool) × ℕ)
    (clone : σ₂ → σ₂ × ℕ) (B fuel₁ fuel₂ : ℕ) (st : StreamJoin.State σ₁ σ₂ τ) :
    let M := base + front + fill + outer + 2 * inner + 12
    allowance base front fill outer inner copy read₁ key₁ read₂ key₂ cells report clone B fuel₁ fuel₂ st +
      CountedStreamJoin.potential M 0 copy st ≤
      CountedStreamJoin.potential M 0 copy
        (CountedStreamJoin.step read₁ key₁ read₂ key₂ cells report clone B fuel₁ fuel₂ st).1 + base := by
  let M := base + front + fill + outer + 2 * inner + 12
  change allowance _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ + CountedStreamJoin.potential M 0 copy st ≤
    CountedStreamJoin.potential M 0 copy
      (CountedStreamJoin.step read₁ key₁ read₂ key₂ cells report clone B fuel₁ fuel₂ st).1 + base
  have hbase : base ≤ M := by dsimp [M]; omega
  by_cases hd : st.done = true
  · simp only [allowance, CountedStreamJoin.step, hd, ↓reduceIte]
    omega
  · cases hx : (read₁ st.left).1 with
    | none =>
      simp only [allowance, CountedStreamJoin.step, hd, Bool.false_eq_true, ↓reduceIte, hx,
        CountedStreamJoin.potential, Nat.mul_add, Nat.mul_one, Nat.zero_mul, Nat.add_zero]
      omega
    | some p =>
      rcases p with ⟨x, x'⟩
      cases hy : (read₂ st.right).1 with
      | none =>
        simp only [allowance, CountedStreamJoin.step, hd, Bool.false_eq_true, ↓reduceIte, hx, hy,
          CountedStreamJoin.potential, Nat.mul_add, Nat.zero_mul, Nat.add_zero]
        omega
      | some p =>
        rcases p with ⟨y, y'⟩
        simp only [allowance, CountedStreamJoin.step, hd, Bool.false_eq_true, ↓reduceIte, hx, hy]
        split
        · simp only [CountedStreamJoin.potential, Nat.mul_add, Nat.zero_mul, Nat.add_zero]
          omega
        · split
          · simp only [CountedStreamJoin.potential, Nat.mul_add, Nat.zero_mul, Nat.add_zero]
            omega
          · let out := (CountedTieGroup.run read₁ key₁ read₂ key₂ cells (key₁ x).1 report clone
              B fuel₁ fuel₂ st.left st.right st.user).1
            have hg := BudgetedTieGroup.allowance_le front fill outer inner copy read₁ key₁ read₂ key₂ cells
              (key₁ x).1 report clone B fuel₁ fuel₂ st.left st.right st.user
            change BudgetedTieGroup.allowance front fill outer inner copy read₁ key₁ read₂ key₂ cells
              (key₁ x).1 report clone B fuel₁ fuel₂ st.left st.right st.user ≤
              (front + fill + outer + 2 * inner + 12) *
                (out.outer.queries + out.fillQueries + out.outer.state.queries + 1) +
              copy * ((if out.snapshot then 1 else 0) + out.outer.state.restores) at hg
            have hm := Nat.mul_le_mul_right
              (out.outer.queries + out.fillQueries + out.outer.state.queries + 1)
              (show front + fill + outer + 2 * inner + 12 ≤ M by dsimp [M]; omega)
            change base + BudgetedTieGroup.allowance front fill outer inner copy read₁ key₁ read₂ key₂ cells
              (key₁ x).1 report clone B fuel₁ fuel₂ st.left st.right st.user +
              CountedStreamJoin.potential M 0 copy st ≤
              CountedStreamJoin.potential M 0 copy
                ⟨out.outer.cursor, out.outer.state.last, out.outer.state.user,
                  st.queries + 2 + out.outer.queries + out.fillQueries + out.outer.state.queries,
                  st.reports + out.outer.state.reports,
                  st.copies + (if out.snapshot then 1 else 0) + out.outer.state.restores,
                  out.outer.halted⟩ + base
            simp only [CountedStreamJoin.potential, Nat.mul_add, Nat.mul_one, Nat.zero_mul, Nat.add_zero] at hg hm ⊢
            omega

end LowSpaceSubsetSum.BudgetedStreamStep

end OAI
