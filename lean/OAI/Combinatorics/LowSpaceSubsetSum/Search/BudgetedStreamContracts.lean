import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedStreamAllowance

namespace OAI

namespace LowSpaceSubsetSum.BudgetedStreamStep

universe u v s t w
variable {α : Type u} {β : Type v} {σ₁ : Type s} {σ₂ : Type t} {τ : Type w}

theorem execute_remaining (base front fill outer inner copy : ℕ)
    (read₁ : σ₁ → Option (α × σ₁) × ℕ) (key₁ : α → ℤ × ℕ)
    (read₂ : σ₂ → Option (β × σ₂) × ℕ) (key₂ : β → ℤ × ℕ)
    (cells : β → ℕ) (report : α → β → τ → (τ × Bool) × ℕ)
    (clone : σ₂ → σ₂ × ℕ) (B fuel₁ fuel₂ : ℕ)
    (st : StreamJoin.State σ₁ σ₂ τ) (budget : ℕ) (out : StreamJoin.State σ₁ σ₂ τ) (left : ℕ)
    (h : (execute base front fill outer inner copy read₁ key₁ read₂ key₂ cells report clone
      B fuel₁ fuel₂ st budget).1 = some (out, left)) :
    budget ≤ left + allowance base front fill outer inner copy read₁ key₁ read₂ key₂ cells report clone
      B fuel₁ fuel₂ st := by
  rw [execute] at h
  split at h
  next hb =>
    by_cases hd : st.done = true
    · simp only [hd, ↓reduceIte] at h
      cases h
      simp only [allowance, hd, ↓reduceIte]
      omega
    · simp only [hd, Bool.false_eq_true, ↓reduceIte] at h
      cases hx : (read₁ st.left).1 with
      | none =>
        simp only [hx] at h
        cases h
        simp only [allowance, hd, Bool.false_eq_true, ↓reduceIte, hx]
        omega
      | some p =>
        rcases p with ⟨x, x'⟩
        simp only [hx] at h
        cases hy : (read₂ st.right).1 with
        | none =>
          simp only [hy] at h
          cases h
          simp only [allowance, hd, Bool.false_eq_true, ↓reduceIte, hx, hy]
          omega
        | some p =>
          rcases p with ⟨y, y'⟩
          simp only [hy] at h
          by_cases hk : (key₁ x).1 < (key₂ y).1
          · simp only [hk, ↓reduceIte] at h
            cases h
            simp only [allowance, hd, Bool.false_eq_true, ↓reduceIte, hx, hy, hk]
            omega
          · simp only [hk, ↓reduceIte] at h
            by_cases hk' : (key₂ y).1 < (key₁ x).1
            · simp only [hk', ↓reduceIte] at h
              cases h
              simp only [allowance, hd, Bool.false_eq_true, ↓reduceIte, hx, hy, hk, hk']
              omega
            · simp only [hk', ↓reduceIte] at h
              obtain ⟨pair, hg, he⟩ := Option.map_eq_some_iff.mp h
              rcases pair with ⟨group, remaining⟩
              have hr := BudgetedTieGroup.execute_remaining front fill outer inner copy read₁ key₁ read₂ key₂ cells
                (key₁ x).1 report clone B fuel₁ fuel₂ st.left st.right st.user (budget - base) group remaining hg
              cases he
              simp only [allowance, hd, Bool.false_eq_true, ↓reduceIte, hx, hy, hk, hk']
              omega
  next _ => contradiction

theorem execute_spent
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
    (B fuel₁ fuel₂ : ℕ) (st : StreamJoin.State σ₁ σ₂ τ) (budget : ℕ)
    (out : StreamJoin.State σ₁ σ₂ τ) (left : ℕ)
    (h : (execute base front fill outer inner copy read₁ key₁ read₂ key₂ cells report clone
      B fuel₁ fuel₂ st budget).1 = some (out, left)) :
    (execute base front fill outer inner copy read₁ key₁ read₂ key₂ cells report clone
      B fuel₁ fuel₂ st budget).2 ≤ budget - left := by
  rw [execute] at h ⊢
  split at h
  next hb =>
    simp only [hb, ↓reduceIte] at h ⊢
    by_cases hd : st.done = true
    · simp only [hd, ↓reduceIte] at h ⊢
      cases h
      omega
    · simp only [hd, Bool.false_eq_true, ↓reduceIte] at h ⊢
      have hxw := hr₁ st.left
      cases hx : (read₁ st.left).1 with
      | none =>
        simp only [hx] at h ⊢
        cases h
        omega
      | some p =>
        rcases p with ⟨x, x'⟩
        simp only [hx] at h ⊢
        have hyw := hr₂ st.right
        cases hy : (read₂ st.right).1 with
        | none =>
          simp only [hy] at h ⊢
          cases h
          omega
        | some p =>
          rcases p with ⟨y, y'⟩
          have hxk := hk₁ x
          have hyk := hk₂ y
          simp only [hy] at h ⊢
          by_cases hk : (key₁ x).1 < (key₂ y).1
          · simp only [hk, ↓reduceIte] at h ⊢
            cases h
            omega
          · simp only [hk, ↓reduceIte] at h ⊢
            by_cases hk' : (key₂ y).1 < (key₁ x).1
            · simp only [hk', ↓reduceIte] at h ⊢
              cases h
              omega
            · simp only [hk', ↓reduceIte] at h ⊢
              obtain ⟨pair, hg, he⟩ := Option.map_eq_some_iff.mp h
              rcases pair with ⟨group, remaining⟩
              have hgv := (BudgetedTieGroup.execute_value front fill outer inner copy read₁ key₁ read₂ key₂ cells
                (key₁ x).1 report clone B fuel₁ fuel₂ st.left st.right st.user (budget - base) group remaining hg).2
              have hgs := BudgetedTieGroup.execute_spent read₁ key₁ read₂ key₂ cells (key₁ x).1 report clone
                R₁ L₁ R₂ L₂ S C front fill outer inner copy hr₁ hk₁ hr₂ hk₂ hs hc hfront hfill houter hinner hcopy
                B fuel₁ fuel₂ st.left st.right st.user (budget - base) group remaining hg
              cases he
              omega
  next _ => contradiction

end LowSpaceSubsetSum.BudgetedStreamStep

end OAI
