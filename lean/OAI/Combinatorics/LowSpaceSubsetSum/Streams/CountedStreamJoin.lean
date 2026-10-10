import OAI.Combinatorics.LowSpaceSubsetSum.Streams.CountedTieGroup
import OAI.Combinatorics.LowSpaceSubsetSum.Search.StoppedStreamJoin

namespace OAI

/-! # Costed execution of the stopped sorted-stream join

Every read, key evaluation, callback and snapshot invokes its supplied counted
implementation. The resulting work follows the exact stopped query/report/copy
ledger. The unused control fuel is never traversed.
-/

namespace LowSpaceSubsetSum.CountedStreamJoin

universe u v s t w
variable {α : Type u} {β : Type v} {σ₁ : Type s} {σ₂ : Type t} {τ : Type w}

def potential (M C D : ℕ) (st : StreamJoin.State σ₁ σ₂ τ) : ℕ :=
  M * st.queries + C * st.reports + D * st.copies

def step (read₁ : σ₁ → Option (α × σ₁) × ℕ) (key₁ : α → ℤ × ℕ)
    (read₂ : σ₂ → Option (β × σ₂) × ℕ) (key₂ : β → ℤ × ℕ) (cells : β → ℕ)
    (report : α → β → τ → (τ × Bool) × ℕ) (clone : σ₂ → σ₂ × ℕ)
    (B fuel₁ fuel₂ : ℕ) (s : StreamJoin.State σ₁ σ₂ τ) :
    StreamJoin.State σ₁ σ₂ τ × ℕ :=
  if s.done then (s, 1) else
  let fetched₁ := read₁ s.left
  match fetched₁.1 with
  | none => ({ s with queries := s.queries + 1, done := true }, fetched₁.2 + 4)
  | some (x, left') =>
    let fetched₂ := read₂ s.right
    match fetched₂.1 with
    | none => ({ s with queries := s.queries + 2, done := true }, fetched₁.2 + fetched₂.2 + 5)
    | some (y, right') =>
      let k₁ := key₁ x
      let k₂ := key₂ y
      let base := fetched₁.2 + fetched₂.2 + k₁.2 + k₂.2 + 8
      if k₁.1 < k₂.1 then ({ s with left := left', queries := s.queries + 2 }, base)
      else if k₂.1 < k₁.1 then ({ s with right := right', queries := s.queries + 2 }, base)
      else
        let out := CountedTieGroup.run read₁ key₁ read₂ key₂ cells k₁.1 report clone
          B fuel₁ fuel₂ s.left s.right s.user
        (⟨out.1.outer.cursor, out.1.outer.state.last, out.1.outer.state.user,
          s.queries + 2 + out.1.outer.queries + out.1.fillQueries + out.1.outer.state.queries,
          s.reports + out.1.outer.state.reports,
          s.copies + (if out.1.snapshot then 1 else 0) + out.1.outer.state.restores,
          out.1.outer.halted⟩, base + out.2 + 8)

theorem step_value (read₁ : σ₁ → Option (α × σ₁) × ℕ) (key₁ : α → ℤ × ℕ)
    (read₂ : σ₂ → Option (β × σ₂) × ℕ) (key₂ : β → ℤ × ℕ) (cells : β → ℕ)
    (report : α → β → τ → (τ × Bool) × ℕ) (clone : σ₂ → σ₂ × ℕ)
    (hclone : ∀ s, (clone s).1 = s)
    (B fuel₁ fuel₂ : ℕ) (s : StreamJoin.State σ₁ σ₂ τ) :
    (step read₁ key₁ read₂ key₂ cells report clone B fuel₁ fuel₂ s).1 =
      StreamJoin.step (fun s => (read₁ s).1) (fun x => (key₁ x).1)
        (fun s => (read₂ s).1) (fun y => (key₂ y).1) (fun x y a => (report x y a).1)
        B fuel₁ fuel₂ s := by
  by_cases hd : s.done = true
  · simp only [step, StreamJoin.step, hd, ↓reduceIte]
  · cases h₁ : (read₁ s.left).1 with
    | none => simp only [step, StreamJoin.step, hd, Bool.false_eq_true, ↓reduceIte, h₁]
    | some z₁ =>
      rcases z₁ with ⟨x, left'⟩
      cases h₂ : (read₂ s.right).1 with
      | none => simp only [step, StreamJoin.step, hd, Bool.false_eq_true, ↓reduceIte, h₁, h₂]
      | some z₂ =>
        rcases z₂ with ⟨y, right'⟩
        simp only [step, StreamJoin.step, hd, Bool.false_eq_true, ↓reduceIte, h₁, h₂,
          CountedTieGroup.run_value read₁ key₁ read₂ key₂ cells _ report clone hclone]
        split_ifs <;> rfl

theorem step_work_potential
    (read₁ : σ₁ → Option (α × σ₁) × ℕ) (key₁ : α → ℤ × ℕ)
    (read₂ : σ₂ → Option (β × σ₂) × ℕ) (key₂ : β → ℤ × ℕ) (cells : β → ℕ)
    (report : α → β → τ → (τ × Bool) × ℕ) (clone : σ₂ → σ₂ × ℕ)
    (R₁ R₂ L₁ L₂ S C D : ℕ)
    (hr₁ : ∀ s, (read₁ s).2 ≤ R₁) (hr₂ : ∀ s, (read₂ s).2 ≤ R₂)
    (hk₁ : ∀ x, (key₁ x).2 ≤ L₁) (hk₂ : ∀ y, (key₂ y).2 ≤ L₂)
    (hs : ∀ y, cells y ≤ S) (hc : ∀ x y a, (report x y a).2 ≤ C)
    (hcopy : ∀ s, (clone s).2 ≤ D)
    (B fuel₁ fuel₂ : ℕ) (s : StreamJoin.State σ₁ σ₂ τ) :
    (step read₁ key₁ read₂ key₂ cells report clone B fuel₁ fuel₂ s).2 +
        potential (R₁ + R₂ + L₁ + L₂ + S + 64) C D s ≤
      potential (R₁ + R₂ + L₁ + L₂ + S + 64) C D
        (step read₁ key₁ read₂ key₂ cells report clone B fuel₁ fuel₂ s).1 +
          (R₁ + R₂ + L₁ + L₂ + S + 64) := by
  by_cases hd : s.done = true
  · simp only [step, hd, ↓reduceIte]
    omega
  · have hr := hr₁ s.left
    cases h₁ : (read₁ s.left).1 with
    | none =>
      simp only [step, hd, Bool.false_eq_true, ↓reduceIte, h₁, potential, Nat.mul_add, Nat.mul_one]
      omega
    | some z₁ =>
      rcases z₁ with ⟨x, left'⟩
      have hr' := hr₂ s.right
      cases h₂ : (read₂ s.right).1 with
      | none =>
        simp only [step, hd, Bool.false_eq_true, ↓reduceIte, h₁, h₂, potential, Nat.mul_add]
        omega
      | some z₂ =>
        rcases z₂ with ⟨y, right'⟩
        have hk := hk₁ x
        have hk' := hk₂ y
        have hg := CountedTieGroup.run_work read₁ key₁ read₂ key₂ cells (key₁ x).1 report clone
          R₁ R₂ L₁ L₂ S C D hr₁ hr₂ hk₁ hk₂ hs hc hcopy B fuel₁ fuel₂ s.left s.right s.user
        let out := CountedTieGroup.run read₁ key₁ read₂ key₂ cells (key₁ x).1 report clone
          B fuel₁ fuel₂ s.left s.right s.user
        change out.2 ≤ (R₁ + R₂ + L₁ + L₂ + S + 50) *
          (out.1.outer.queries + out.1.fillQueries + out.1.outer.state.queries + 1) +
          C * out.1.outer.state.reports +
          D * ((if out.1.snapshot then 1 else 0) + out.1.outer.state.restores) at hg
        have hmul := Nat.mul_le_mul_right
          (out.1.outer.queries + out.1.fillQueries + out.1.outer.state.queries + 1)
          (show R₁ + R₂ + L₁ + L₂ + S + 50 ≤ R₁ + R₂ + L₁ + L₂ + S + 64 by omega)
        simp only [step, hd, Bool.false_eq_true, ↓reduceIte, h₁, h₂]
        split
        · simp only [potential, Nat.mul_add]
          omega
        · split
          · simp only [potential, Nat.mul_add]
            omega
          · change (read₁ s.left).2 + (read₂ s.right).2 + (key₁ x).2 + (key₂ y).2 + 8 + out.2 + 8 +
              potential (R₁ + R₂ + L₁ + L₂ + S + 64) C D s ≤
              potential (R₁ + R₂ + L₁ + L₂ + S + 64) C D
                ⟨out.1.outer.cursor, out.1.outer.state.last, out.1.outer.state.user,
                  s.queries + 2 + out.1.outer.queries + out.1.fillQueries + out.1.outer.state.queries,
                  s.reports + out.1.outer.state.reports,
                  s.copies + (if out.1.snapshot then 1 else 0) + out.1.outer.state.restores,
                  out.1.outer.halted⟩ + _
            simp only [potential, Nat.mul_add, Nat.mul_one] at hg hmul ⊢
            omega

def runAcc (read₁ : σ₁ → Option (α × σ₁) × ℕ) (key₁ : α → ℤ × ℕ)
    (read₂ : σ₂ → Option (β × σ₂) × ℕ) (key₂ : β → ℤ × ℕ) (cells : β → ℕ)
    (report : α → β → τ → (τ × Bool) × ℕ) (clone : σ₂ → σ₂ × ℕ)
    (B fuel₁ fuel₂ : ℕ) : ℕ → StreamJoin.State σ₁ σ₂ τ → StreamJoin.StoppedResult σ₁ σ₂ τ × ℕ
  | 0, st => (⟨st, 0⟩, 1)
  | fuel + 1, st =>
    if st.done then (⟨st, 0⟩, 1) else
      let next := step read₁ key₁ read₂ key₂ cells report clone B fuel₁ fuel₂ st
      let out := runAcc read₁ key₁ read₂ key₂ cells report clone B fuel₁ fuel₂ fuel next.1
      (⟨out.1.state, out.1.steps + 1⟩, next.2 + out.2 + 3)

theorem runAcc_value (read₁ : σ₁ → Option (α × σ₁) × ℕ) (key₁ : α → ℤ × ℕ)
    (read₂ : σ₂ → Option (β × σ₂) × ℕ) (key₂ : β → ℤ × ℕ) (cells : β → ℕ)
    (report : α → β → τ → (τ × Bool) × ℕ) (clone : σ₂ → σ₂ × ℕ)
    (hclone : ∀ s, (clone s).1 = s) (B fuel₁ fuel₂ fuel : ℕ) (st : StreamJoin.State σ₁ σ₂ τ) :
    (runAcc read₁ key₁ read₂ key₂ cells report clone B fuel₁ fuel₂ fuel st).1 =
      StreamJoin.stoppedAcc (fun s => (read₁ s).1) (fun x => (key₁ x).1)
        (fun s => (read₂ s).1) (fun y => (key₂ y).1) (fun x y a => (report x y a).1)
        B fuel₁ fuel₂ fuel st := by
  induction fuel generalizing st with
  | zero => rfl
  | succ fuel ih =>
    by_cases hd : st.done = true
    · simp only [runAcc, StreamJoin.stoppedAcc, hd, ↓reduceIte]
    · simp only [runAcc, StreamJoin.stoppedAcc, hd, Bool.false_eq_true, ↓reduceIte, ih,
        step_value read₁ key₁ read₂ key₂ cells report clone hclone]

theorem runAcc_work
    (read₁ : σ₁ → Option (α × σ₁) × ℕ) (key₁ : α → ℤ × ℕ)
    (read₂ : σ₂ → Option (β × σ₂) × ℕ) (key₂ : β → ℤ × ℕ) (cells : β → ℕ)
    (report : α → β → τ → (τ × Bool) × ℕ) (clone : σ₂ → σ₂ × ℕ)
    (R₁ R₂ L₁ L₂ S C D : ℕ)
    (hr₁ : ∀ s, (read₁ s).2 ≤ R₁) (hr₂ : ∀ s, (read₂ s).2 ≤ R₂)
    (hk₁ : ∀ x, (key₁ x).2 ≤ L₁) (hk₂ : ∀ y, (key₂ y).2 ≤ L₂)
    (hs : ∀ y, cells y ≤ S) (hc : ∀ x y a, (report x y a).2 ≤ C)
    (hcopy : ∀ s, (clone s).2 ≤ D)
    (B fuel₁ fuel₂ fuel : ℕ) (st : StreamJoin.State σ₁ σ₂ τ) :
    (runAcc read₁ key₁ read₂ key₂ cells report clone B fuel₁ fuel₂ fuel st).2 +
        potential (R₁ + R₂ + L₁ + L₂ + S + 64) C D st ≤
      potential (R₁ + R₂ + L₁ + L₂ + S + 64) C D
        (runAcc read₁ key₁ read₂ key₂ cells report clone B fuel₁ fuel₂ fuel st).1.state +
      (R₁ + R₂ + L₁ + L₂ + S + 67) *
        (runAcc read₁ key₁ read₂ key₂ cells report clone B fuel₁ fuel₂ fuel st).1.steps + 1 := by
  induction fuel generalizing st with
  | zero => simp only [runAcc, Nat.mul_zero, Nat.add_zero]; omega
  | succ fuel ih =>
    by_cases hd : st.done = true
    · simp only [runAcc, hd, ↓reduceIte, Nat.mul_zero, Nat.add_zero]; omega
    · have hstep := step_work_potential read₁ key₁ read₂ key₂ cells report clone
        R₁ R₂ L₁ L₂ S C D hr₁ hr₂ hk₁ hk₂ hs hc hcopy B fuel₁ fuel₂ st
      have hi := ih (step read₁ key₁ read₂ key₂ cells report clone B fuel₁ fuel₂ st).1
      simp only [runAcc, hd, Bool.false_eq_true, ↓reduceIte, Nat.mul_add, Nat.mul_one]
      omega

/-- After initialization, control iterations can themselves be charged to
queries, giving a bound using only the original join ledger. -/
theorem run_work_queries
    (read₁ : σ₁ → Option (α × σ₁) × ℕ) (key₁ : α → ℤ × ℕ)
    (read₂ : σ₂ → Option (β × σ₂) × ℕ) (key₂ : β → ℤ × ℕ) (cells : β → ℕ)
    (report : α → β → τ → (τ × Bool) × ℕ) (clone : σ₂ → σ₂ × ℕ)
    (hclone : ∀ s, (clone s).1 = s) (R₁ R₂ L₁ L₂ S C D : ℕ)
    (hr₁ : ∀ s, (read₁ s).2 ≤ R₁) (hr₂ : ∀ s, (read₂ s).2 ≤ R₂)
    (hk₁ : ∀ x, (key₁ x).2 ≤ L₁) (hk₂ : ∀ y, (key₂ y).2 ≤ L₂)
    (hs : ∀ y, cells y ≤ S) (hc : ∀ x y a, (report x y a).2 ≤ C)
    (hcopy : ∀ s, (clone s).2 ≤ D)
    (B fuel₁ fuel₂ fuel : ℕ) (s₁ : σ₁) (s₂ : σ₂) (a : τ) :
    (runAcc read₁ key₁ read₂ key₂ cells report clone B fuel₁ fuel₂ fuel
      (StreamJoin.start s₁ s₂ a)).2 ≤
      (2 * (R₁ + R₂ + L₁ + L₂ + S) + 131) *
        (StreamJoin.run (fun s => (read₁ s).1) (fun x => (key₁ x).1)
          (fun s => (read₂ s).1) (fun y => (key₂ y).1) (fun x y a => (report x y a).1)
          B fuel₁ fuel₂ fuel s₁ s₂ a).queries +
      C * (StreamJoin.run (fun s => (read₁ s).1) (fun x => (key₁ x).1)
          (fun s => (read₂ s).1) (fun y => (key₂ y).1) (fun x y a => (report x y a).1)
          B fuel₁ fuel₂ fuel s₁ s₂ a).reports +
      D * (StreamJoin.run (fun s => (read₁ s).1) (fun x => (key₁ x).1)
          (fun s => (read₂ s).1) (fun y => (key₂ y).1) (fun x y a => (report x y a).1)
          B fuel₁ fuel₂ fuel s₁ s₂ a).copies + 1 := by
  have h := runAcc_work read₁ key₁ read₂ key₂ cells report clone
    R₁ R₂ L₁ L₂ S C D hr₁ hr₂ hk₁ hk₂ hs hc hcopy B fuel₁ fuel₂ fuel
    (StreamJoin.start s₁ s₂ a)
  rw [runAcc_value read₁ key₁ read₂ key₂ cells report clone hclone] at h
  have hq := StreamJoin.stopped_steps_le_queries (fun s => (read₁ s).1) (fun x => (key₁ x).1)
    (fun s => (read₂ s).1) (fun y => (key₂ y).1) (fun x y a => (report x y a).1)
    B fuel₁ fuel₂ fuel s₁ s₂ a
  have hmul := Nat.mul_le_mul_left (R₁ + R₂ + L₁ + L₂ + S + 67) hq
  simp only [potential, StreamJoin.start, Nat.mul_zero, Nat.add_zero,
    StreamJoin.stoppedAcc_eq] at h
  simp only [StreamJoin.stopped] at hmul
  dsimp only [StreamJoin.run, StreamJoin.start] at hmul ⊢
  have he : 2 * (R₁ + R₂ + L₁ + L₂ + S) + 131 =
      (R₁ + R₂ + L₁ + L₂ + S + 64) + (R₁ + R₂ + L₁ + L₂ + S + 67) := by omega
  rw [he, Nat.add_mul]
  omega

end LowSpaceSubsetSum.CountedStreamJoin

end OAI
