import OAI.Combinatorics.LowSpaceSubsetSum.Search.StoppedStreamJoin

namespace OAI

/-! # Erasing proof-carrying callback states through the actual join

This refinement lets a counted dictionary carry its invariant intrinsically,
while retaining exactly the original join's cursors, counters and halt behavior.
-/

namespace LowSpaceSubsetSum

universe u v s t w z
variable {α : Type u} {β : Type v} {σ : Type s} {τ : Type w} {τ' : Type z}

namespace TieReplay

def mapUser (f : τ → τ') (r : Result σ τ) : Result σ τ' :=
  ⟨r.cursor, f r.state, r.queries, r.reports, r.complete, r.halted⟩

theorem runAcc_mapUser (read : σ → Option (α × σ)) (key : α → ℤ) (K : ℤ)
    (report : α → τ → τ × Bool) (report' : α → τ' → τ' × Bool) (f : τ → τ')
    (hf : ∀ x a, report' x (f a) = (f (report x a).1, (report x a).2))
    (fuel : ℕ) (s : σ) (a : τ) (q r : ℕ) :
    mapUser f (runAcc read key K report fuel s a q r) =
      runAcc read key K report' fuel s (f a) q r := by
  induction fuel generalizing s a q r with
  | zero => rfl
  | succ fuel ih =>
    cases hr : read s with
    | none => simp only [runAcc, hr, mapUser]
    | some p =>
      rcases p with ⟨x, s'⟩
      simp only [runAcc, hr]
      split
      · rw [hf]
        split
        · rfl
        · exact ih _ _ _ _
      · rfl

theorem run_mapUser (read : σ → Option (α × σ)) (key : α → ℤ) (K : ℤ)
    (report : α → τ → τ × Bool) (report' : α → τ' → τ' × Bool) (f : τ → τ')
    (hf : ∀ x a, report' x (f a) = (f (report x a).1, (report x a).2))
    (fuel : ℕ) (s : σ) (a : τ) :
    mapUser f (run read key K report fuel s a) =
      run read key K report' fuel s (f a) :=
  runAcc_mapUser read key K report report' f hf fuel s a 0 0

end TieReplay

namespace JoinOne

theorem run_mapUser (read : σ → Option (α × σ)) (key : α → ℤ) (K : ℤ)
    (report : α → τ → τ × Bool) (report' : α → τ' → τ' × Bool) (f : τ → τ')
    (hf : ∀ x a, report' x (f a) = (f (report x a).1, (report x a).2))
    (buffer : Array α) (saved : σ) (long : Bool) (fuel : ℕ) (a : τ) :
    TieReplay.mapUser f (run read key K report buffer saved long fuel a) =
      run read key K report' buffer saved long fuel (f a) := by
  simp only [run, BufferReplay.run,
    ← TieReplay.run_mapUser (BufferReplay.read buffer) key K report report' f hf,
    TieReplay.mapUser]
  split
  · simp_all only [↓reduceIte]
  · simp_all only [Bool.false_eq_true, ↓reduceIte]
    split
    · simp_all only
      have h := TieReplay.run_mapUser read key K report report' f hf fuel saved
        (TieReplay.run (BufferReplay.read buffer) key K report buffer.size 0 a).state
      cases h₁ : TieReplay.run read key K report fuel saved
        (TieReplay.run (BufferReplay.read buffer) key K report buffer.size 0 a).state
      simp only [h₁, TieReplay.mapUser] at h
      rw [← h]
    · simp_all only

end JoinOne

namespace TieGroup

variable {σ₂ : Type t}

def mapUser (f : τ → τ') (a : State σ₂ τ) : State σ₂ τ' :=
  ⟨a.last, f a.user, a.queries, a.reports, a.restores⟩

def mapResult (f : τ → τ') (r : Result σ σ₂ τ) : Result σ σ₂ τ' :=
  ⟨TieReplay.mapUser (mapUser f) r.outer, r.fillQueries, r.bufferSize, r.snapshot⟩

theorem step_mapUser (read : σ₂ → Option (β × σ₂)) (key : β → ℤ) (K : ℤ)
    (report : α → β → τ → τ × Bool) (report' : α → β → τ' → τ' × Bool) (f : τ → τ')
    (hf : ∀ x y a, report' x y (f a) = (f (report x y a).1, (report x y a).2))
    (buffer : Array β) (saved : σ₂) (long : Bool) (fuel : ℕ) (x : α) (a : State σ₂ τ) :
    (mapUser f (step read key K report buffer saved long fuel x a).1,
      (step read key K report buffer saved long fuel x a).2) =
      step read key K report' buffer saved long fuel x (mapUser f a) := by
  simp only [step, mapUser,
    ← JoinOne.run_mapUser read key K (report x) (report' x) f (hf x), TieReplay.mapUser]

theorem run_mapUser (read₁ : σ → Option (α × σ)) (key₁ : α → ℤ)
    (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ) (K : ℤ)
    (report : α → β → τ → τ × Bool) (report' : α → β → τ' → τ' × Bool) (f : τ → τ')
    (hf : ∀ x y a, report' x y (f a) = (f (report x y a).1, (report x y a).2))
    (B fuel₁ fuel₂ : ℕ) (s₁ : σ) (s₂ : σ₂) (a : τ) :
    mapResult f (run read₁ key₁ read₂ key₂ K report B fuel₁ fuel₂ s₁ s₂ a) =
      run read₁ key₁ read₂ key₂ K report' B fuel₁ fuel₂ s₁ s₂ (f a) := by
  let filled := TieBuffer.fill read₂ key₂ K B s₂
  let long := TieBuffer.hasKey read₂ key₂ K filled.cursor
  have hstep := fun x st => (step_mapUser read₂ key₂ K report report' f hf
    filled.buffer filled.cursor long fuel₂ x st).symm
  have h := TieReplay.run_mapUser read₁ key₁ K
    (step read₂ key₂ K report filled.buffer filled.cursor long fuel₂)
    (step read₂ key₂ K report' filled.buffer filled.cursor long fuel₂)
    (mapUser f) hstep fuel₁ s₁ ⟨filled.cursor, a, 0, 0, 0⟩
  change mapResult f ⟨_, filled.queries, filled.buffer.size, _⟩ = _
  unfold mapResult
  rw [h]
  rfl

end TieGroup
namespace StreamJoin

variable {σ₂ : Type t}

def mapUser (f : τ → τ') (a : State σ σ₂ τ) : State σ σ₂ τ' :=
  ⟨a.left, a.right, f a.user, a.queries, a.reports, a.copies, a.done⟩

def mapStopped (f : τ → τ') (a : StoppedResult σ σ₂ τ) : StoppedResult σ σ₂ τ' :=
  ⟨mapUser f a.state, a.steps⟩

theorem step_mapUser (read₁ : σ → Option (α × σ)) (key₁ : α → ℤ)
    (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ)
    (report : α → β → τ → τ × Bool) (report' : α → β → τ' → τ' × Bool) (f : τ → τ')
    (hf : ∀ x y a, report' x y (f a) = (f (report x y a).1, (report x y a).2))
    (B fuel₁ fuel₂ : ℕ) (a : State σ σ₂ τ) :
    mapUser f (step read₁ key₁ read₂ key₂ report B fuel₁ fuel₂ a) =
      step read₁ key₁ read₂ key₂ report' B fuel₁ fuel₂ (mapUser f a) := by
  by_cases hd : a.done = true
  · simp only [step, mapUser, hd, ↓reduceIte]
  · cases h₁ : read₁ a.left with
    | none => simp only [step, mapUser, hd, Bool.false_eq_true, ↓reduceIte, h₁]
    | some p₁ =>
      rcases p₁ with ⟨x, l⟩
      cases h₂ : read₂ a.right with
      | none => simp only [step, mapUser, hd, Bool.false_eq_true, ↓reduceIte, h₁, h₂]
      | some p₂ =>
        rcases p₂ with ⟨y, r⟩
        simp only [step, mapUser, hd, Bool.false_eq_true, ↓reduceIte, h₁, h₂,
          ← TieGroup.run_mapUser read₁ key₁ read₂ key₂ (key₁ x) report report' f hf,
          TieGroup.mapResult, TieReplay.mapUser, TieGroup.mapUser]
        split
        · simp_all only
        · split <;> simp_all only

theorem stoppedAcc_mapUser (read₁ : σ → Option (α × σ)) (key₁ : α → ℤ)
    (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ)
    (report : α → β → τ → τ × Bool) (report' : α → β → τ' → τ' × Bool) (f : τ → τ')
    (hf : ∀ x y a, report' x y (f a) = (f (report x y a).1, (report x y a).2))
    (B fuel₁ fuel₂ fuel : ℕ) (a : State σ σ₂ τ) :
    mapStopped f (stoppedAcc read₁ key₁ read₂ key₂ report B fuel₁ fuel₂ fuel a) =
      stoppedAcc read₁ key₁ read₂ key₂ report' B fuel₁ fuel₂ fuel (mapUser f a) := by
  induction fuel generalizing a with
  | zero => rfl
  | succ fuel ih =>
    by_cases hd : a.done = true
    · simp only [stoppedAcc, mapStopped, mapUser, hd, ↓reduceIte]
    · have h := ih (step read₁ key₁ read₂ key₂ report B fuel₁ fuel₂ a)
      have hdone : (mapUser f a).done = a.done := rfl
      simp only [stoppedAcc, hdone, hd, Bool.false_eq_true, ↓reduceIte]
      rw [← step_mapUser read₁ key₁ read₂ key₂ report report' f hf]
      rw [← h]
      rfl

theorem run_mapUser (read₁ : σ → Option (α × σ)) (key₁ : α → ℤ)
    (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ)
    (report : α → β → τ → τ × Bool) (report' : α → β → τ' → τ' × Bool) (f : τ → τ')
    (hf : ∀ x y a, report' x y (f a) = (f (report x y a).1, (report x y a).2))
    (B fuel₁ fuel₂ fuel : ℕ) (s₁ : σ) (s₂ : σ₂) (a : τ) :
    mapUser f (run read₁ key₁ read₂ key₂ report B fuel₁ fuel₂ fuel s₁ s₂ a) =
      run read₁ key₁ read₂ key₂ report' B fuel₁ fuel₂ fuel s₁ s₂ (f a) := by
  have h := congrArg StoppedResult.state (stoppedAcc_mapUser read₁ key₁ read₂ key₂
    report report' f hf B fuel₁ fuel₂ fuel (start s₁ s₂ a))
  simpa only [mapStopped, stoppedAcc_eq, mapUser, start, run] using h

end StreamJoin

end LowSpaceSubsetSum

end OAI
