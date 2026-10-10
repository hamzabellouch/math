import OAI.Combinatorics.LowSpaceSubsetSum.Streams.StreamJoinBounds

namespace OAI

/-! # An early-stopping implementation of the bounded global join -/

namespace LowSpaceSubsetSum.StreamJoin

universe u v s t w
variable {α : Type u} {β : Type v} {σ₁ : Type s} {σ₂ : Type t} {τ : Type w}

structure StoppedResult (σ₁ : Type s) (σ₂ : Type t) (τ : Type w) where
  state : State σ₁ σ₂ τ
  steps : ℕ

/-- Return immediately at exhaustion or callback halt. The fuel counter is
only a bound; its unused suffix is never traversed. -/
def stoppedAcc (read₁ : σ₁ → Option (α × σ₁)) (key₁ : α → ℤ)
    (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ)
    (report : α → β → τ → τ × Bool) (B fuel₁ fuel₂ : ℕ) :
    ℕ → State σ₁ σ₂ τ → StoppedResult σ₁ σ₂ τ
  | 0, st => ⟨st, 0⟩
  | fuel + 1, st =>
    if st.done then ⟨st, 0⟩ else
      let out := stoppedAcc read₁ key₁ read₂ key₂ report B fuel₁ fuel₂ fuel
        (step read₁ key₁ read₂ key₂ report B fuel₁ fuel₂ st)
      ⟨out.state, out.steps + 1⟩

def stopped (read₁ : σ₁ → Option (α × σ₁)) (key₁ : α → ℤ)
    (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ)
    (report : α → β → τ → τ × Bool) (B fuel₁ fuel₂ controlFuel : ℕ)
    (s₁ : σ₁) (s₂ : σ₂) (a : τ) : StoppedResult σ₁ σ₂ τ :=
  stoppedAcc read₁ key₁ read₂ key₂ report B fuel₁ fuel₂ controlFuel (start s₁ s₂ a)

theorem stoppedAcc_eq (read₁ : σ₁ → Option (α × σ₁)) (key₁ : α → ℤ)
    (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ)
    (report : α → β → τ → τ × Bool) (B fuel₁ fuel₂ fuel : ℕ) (st : State σ₁ σ₂ τ) :
    (stoppedAcc read₁ key₁ read₂ key₂ report B fuel₁ fuel₂ fuel st).state =
      runAcc read₁ key₁ read₂ key₂ report B fuel₁ fuel₂ fuel st := by
  induction fuel generalizing st with
  | zero => rfl
  | succ fuel ih =>
    by_cases hd : st.done = true
    · simp only [stoppedAcc, hd, ↓reduceIte,
        runAcc_done read₁ key₁ read₂ key₂ report B fuel₁ fuel₂ (fuel + 1) st hd]
    · simp only [stoppedAcc, hd, runAcc]
      exact ih _

theorem stopped_eq (read₁ : σ₁ → Option (α × σ₁)) (key₁ : α → ℤ)
    (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ)
    (report : α → β → τ → τ × Bool) (B fuel₁ fuel₂ controlFuel : ℕ)
    (s₁ : σ₁) (s₂ : σ₂) (a : τ) :
    (stopped read₁ key₁ read₂ key₂ report B fuel₁ fuel₂ controlFuel s₁ s₂ a).state =
      run read₁ key₁ read₂ key₂ report B fuel₁ fuel₂ controlFuel s₁ s₂ a :=
  stoppedAcc_eq _ _ _ _ _ _ _ _ _ _

theorem step_query_growth (read₁ : σ₁ → Option (α × σ₁)) (key₁ : α → ℤ)
    (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ)
    (report : α → β → τ → τ × Bool) (B fuel₁ fuel₂ : ℕ)
    (st : State σ₁ σ₂ τ) (hd : st.done = false) :
    st.queries + 1 ≤ (step read₁ key₁ read₂ key₂ report B fuel₁ fuel₂ st).queries := by
  simp only [step, hd, Bool.false_eq_true, ↓reduceIte]
  split
  · dsimp
    omega
  · split
    · dsimp
      omega
    · split_ifs <;> dsimp <;> omega

/-- Each actual control iteration performs a charged reader query. -/
theorem stoppedAcc_steps_le (read₁ : σ₁ → Option (α × σ₁)) (key₁ : α → ℤ)
    (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ)
    (report : α → β → τ → τ × Bool) (B fuel₁ fuel₂ fuel : ℕ) (st : State σ₁ σ₂ τ) :
    st.queries + (stoppedAcc read₁ key₁ read₂ key₂ report B fuel₁ fuel₂ fuel st).steps ≤
      (stoppedAcc read₁ key₁ read₂ key₂ report B fuel₁ fuel₂ fuel st).state.queries := by
  induction fuel generalizing st with
  | zero => simp [stoppedAcc]
  | succ fuel ih =>
    by_cases hd : st.done = true
    · simp only [stoppedAcc, hd, ↓reduceIte, Nat.add_zero, le_refl]
    · have hq := step_query_growth read₁ key₁ read₂ key₂ report B fuel₁ fuel₂ st
        (Bool.eq_false_iff.mpr hd)
      have hi := ih (step read₁ key₁ read₂ key₂ report B fuel₁ fuel₂ st)
      simp only [stoppedAcc, hd, Bool.false_eq_true, ↓reduceIte]
      omega

theorem stopped_steps_le_queries (read₁ : σ₁ → Option (α × σ₁)) (key₁ : α → ℤ)
    (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ)
    (report : α → β → τ → τ × Bool) (B fuel₁ fuel₂ controlFuel : ℕ)
    (s₁ : σ₁) (s₂ : σ₂) (a : τ) :
    (stopped read₁ key₁ read₂ key₂ report B fuel₁ fuel₂ controlFuel s₁ s₂ a).steps ≤
      (run read₁ key₁ read₂ key₂ report B fuel₁ fuel₂ controlFuel s₁ s₂ a).queries := by
  have h := stoppedAcc_steps_le read₁ key₁ read₂ key₂ report B fuel₁ fuel₂ controlFuel (start s₁ s₂ a)
  have hs : (stopped read₁ key₁ read₂ key₂ report B fuel₁ fuel₂ controlFuel s₁ s₂ a).steps ≤
      (stopped read₁ key₁ read₂ key₂ report B fuel₁ fuel₂ controlFuel s₁ s₂ a).state.queries := by
    simpa only [stopped, start, Nat.zero_add] using h
  rw [stopped_eq] at hs
  exact hs

end LowSpaceSubsetSum.StreamJoin

end OAI
