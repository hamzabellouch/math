import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedTieGroupCompletion
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.CountedStreamJoin

namespace OAI

/-! # One prepaid step of the stopped sorted-stream join -/

namespace LowSpaceSubsetSum.BudgetedStreamStep

universe u v s t w
variable {α : Type u} {β : Type v} {σ₁ : Type s} {σ₂ : Type t} {τ : Type w}

def advance (st : StreamJoin.State σ₁ σ₂ τ) (out : TieGroup.Result σ₁ σ₂ τ) :
    StreamJoin.State σ₁ σ₂ τ :=
  ⟨out.outer.cursor, out.outer.state.last, out.outer.state.user,
    st.queries + 2 + out.outer.queries + out.fillQueries + out.outer.state.queries,
    st.reports + out.outer.state.reports,
    st.copies + (if out.snapshot then 1 else 0) + out.outer.state.restores, out.outer.halted⟩

def execute (base front fill outer inner copy : ℕ)
    (read₁ : σ₁ → Option (α × σ₁) × ℕ) (key₁ : α → ℤ × ℕ)
    (read₂ : σ₂ → Option (β × σ₂) × ℕ) (key₂ : β → ℤ × ℕ)
    (cells : β → ℕ) (report : α → β → τ → (τ × Bool) × ℕ)
    (clone : σ₂ → σ₂ × ℕ) (B fuel₁ fuel₂ : ℕ)
    (st : StreamJoin.State σ₁ σ₂ τ) (budget : ℕ) :
    Option (StreamJoin.State σ₁ σ₂ τ × ℕ) × ℕ :=
  if base ≤ budget then
    if st.done then (some (st, budget - base), 1) else
    let x := read₁ st.left
    match x.1 with
    | none => (some ({st with queries := st.queries + 1, done := true}, budget - base), x.2 + 4)
    | some (a, left) =>
      let y := read₂ st.right
      match y.1 with
      | none => (some ({st with queries := st.queries + 2, done := true}, budget - base), x.2 + y.2 + 5)
      | some (b, right) =>
        let k₁ := key₁ a
        let k₂ := key₂ b
        if k₁.1 < k₂.1 then
          (some ({st with left := left, queries := st.queries + 2}, budget - base), x.2 + y.2 + k₁.2 + k₂.2 + 8)
        else if k₂.1 < k₁.1 then
          (some ({st with right := right, queries := st.queries + 2}, budget - base), x.2 + y.2 + k₁.2 + k₂.2 + 8)
        else
          let out := BudgetedTieGroup.execute front fill outer inner copy read₁ key₁ read₂ key₂ cells k₁.1
            report clone B fuel₁ fuel₂ st.left st.right st.user (budget - base)
          (out.1.map (fun (group, left) => (advance st group, left)),
            x.2 + y.2 + k₁.2 + k₂.2 + out.2 + 16)
  else (none, 1)

theorem execute_value (base front fill outer inner copy : ℕ)
    (read₁ : σ₁ → Option (α × σ₁) × ℕ) (key₁ : α → ℤ × ℕ)
    (read₂ : σ₂ → Option (β × σ₂) × ℕ) (key₂ : β → ℤ × ℕ)
    (cells : β → ℕ) (report : α → β → τ → (τ × Bool) × ℕ)
    (clone : σ₂ → σ₂ × ℕ) (B fuel₁ fuel₂ : ℕ)
    (st : StreamJoin.State σ₁ σ₂ τ) (budget : ℕ) (out : StreamJoin.State σ₁ σ₂ τ) (left : ℕ)
    (h : (execute base front fill outer inner copy read₁ key₁ read₂ key₂ cells report clone
      B fuel₁ fuel₂ st budget).1 = some (out, left)) :
    out = (CountedStreamJoin.step read₁ key₁ read₂ key₂ cells report clone B fuel₁ fuel₂ st).1 ∧
      left ≤ budget := by
  rw [execute] at h
  split at h
  next hb =>
    by_cases hd : st.done = true
    · simp only [hd, ↓reduceIte] at h
      cases h
      exact ⟨by simp only [CountedStreamJoin.step, hd, ↓reduceIte], Nat.sub_le _ _⟩
    · simp only [hd, Bool.false_eq_true, ↓reduceIte] at h
      rw [CountedStreamJoin.step]
      simp only [hd, Bool.false_eq_true, ↓reduceIte]
      cases hx : (read₁ st.left).1 with
      | none =>
        simp only [hx] at h ⊢
        cases h
        exact ⟨rfl, Nat.sub_le _ _⟩
      | some p =>
        rcases p with ⟨a, a'⟩
        simp only [hx] at h ⊢
        cases hy : (read₂ st.right).1 with
        | none =>
          simp only [hy] at h ⊢
          cases h
          exact ⟨rfl, Nat.sub_le _ _⟩
        | some p =>
          rcases p with ⟨b, b'⟩
          simp only [hy] at h ⊢
          by_cases hk : (key₁ a).1 < (key₂ b).1
          · simp only [hk, ↓reduceIte] at h ⊢
            cases h
            exact ⟨rfl, Nat.sub_le _ _⟩
          · simp only [hk, ↓reduceIte] at h ⊢
            by_cases hk' : (key₂ b).1 < (key₁ a).1
            · simp only [hk', ↓reduceIte] at h ⊢
              cases h
              exact ⟨rfl, Nat.sub_le _ _⟩
            · simp only [hk', ↓reduceIte] at h ⊢
              obtain ⟨pair, hg, he⟩ := Option.map_eq_some_iff.mp h
              rcases pair with ⟨group, remaining⟩
              have hv := BudgetedTieGroup.execute_value front fill outer inner copy read₁ key₁ read₂ key₂ cells
                (key₁ a).1 report clone B fuel₁ fuel₂ st.left st.right st.user (budget - base) group remaining hg
              cases he
              exact ⟨by rw [hv.1]; rfl, hv.2.trans (Nat.sub_le _ _)⟩
  next _ => contradiction

theorem execute_work
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
    (B fuel₁ fuel₂ : ℕ) (st : StreamJoin.State σ₁ σ₂ τ) (budget : ℕ) :
    (execute base front fill outer inner copy read₁ key₁ read₂ key₂ cells report clone
      B fuel₁ fuel₂ st budget).2 ≤ budget + 1 := by
  rw [execute]
  split
  next hb =>
    by_cases hd : st.done = true
    · simp only [hd, ↓reduceIte]; omega
    · simp only [hd, Bool.false_eq_true, ↓reduceIte]
      have hxw := hr₁ st.left
      cases hx : (read₁ st.left).1 with
      | none => dsimp only; omega
      | some p =>
        rcases p with ⟨x, x'⟩
        dsimp only
        have hyw := hr₂ st.right
        cases hy : (read₂ st.right).1 with
        | none => dsimp only; omega
        | some p =>
          rcases p with ⟨y, y'⟩
          have hxk := hk₁ x
          have hyk := hk₂ y
          dsimp only
          split
          · (try dsimp only); omega
          · split
            · (try dsimp only); omega
            · have hg := BudgetedTieGroup.execute_work read₁ key₁ read₂ key₂ cells (key₁ x).1 report clone
                R₁ L₁ R₂ L₂ S C front fill outer inner copy hr₁ hk₁ hr₂ hk₂ hs hc
                hfront hfill houter hinner hcopy B fuel₁ fuel₂ st.left st.right st.user (budget - base)
              try dsimp only
              omega
  next _ => (try dsimp only); omega

end LowSpaceSubsetSum.BudgetedStreamStep

end OAI
