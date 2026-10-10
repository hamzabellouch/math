import OAI.Combinatorics.LowSpaceSubsetSum.Counting.MatchPotential

namespace OAI

/-!
# A finite-state join of two sorted streams

Unequal keys consume one occurrence. Equal keys invoke the bounded-buffer
Cartesian reporter and continue from its two saved endpoints. The loop keeps
only the two generator states, callback state, and counters. Its finite output
lists and matching potential are analysis objects only.
-/

namespace LowSpaceSubsetSum
namespace StreamJoin

universe u v s t w

variable {α : Type u} {β : Type v} {σ₁ : Type s} {σ₂ : Type t} {τ : Type w}

structure State (σ₁ : Type s) (σ₂ : Type t) (τ : Type w) where
  left : σ₁
  right : σ₂
  user : τ
  queries : ℕ
  reports : ℕ
  copies : ℕ
  done : Bool

def start (s₁ : σ₁) (s₂ : σ₂) (a : τ) : State σ₁ σ₂ τ := ⟨s₁, s₂, a, 0, 0, 0, false⟩

def step (read₁ : σ₁ → Option (α × σ₁)) (key₁ : α → ℤ)
    (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ)
    (report : α → β → τ → τ × Bool) (B fuel₁ fuel₂ : ℕ)
    (s : State σ₁ σ₂ τ) : State σ₁ σ₂ τ :=
  if s.done then s else
  match read₁ s.left with
  | none => { s with queries := s.queries + 1, done := true }
  | some (x, left') => match read₂ s.right with
    | none => { s with queries := s.queries + 2, done := true }
    | some (y, right') =>
      if key₁ x < key₂ y then { s with left := left', queries := s.queries + 2 }
      else if key₂ y < key₁ x then { s with right := right', queries := s.queries + 2 }
      else
        let out := TieGroup.run read₁ key₁ read₂ key₂ (key₁ x) report B fuel₁ fuel₂
          s.left s.right s.user
        ⟨out.outer.cursor, out.outer.state.last, out.outer.state.user,
          s.queries + 2 + out.outer.queries + out.fillQueries + out.outer.state.queries,
          s.reports + out.outer.state.reports,
          s.copies + (if out.snapshot then 1 else 0) + out.outer.state.restores,
          out.outer.halted⟩

def runAcc (read₁ : σ₁ → Option (α × σ₁)) (key₁ : α → ℤ)
    (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ)
    (report : α → β → τ → τ × Bool) (B fuel₁ fuel₂ : ℕ) :
    ℕ → State σ₁ σ₂ τ → State σ₁ σ₂ τ
  | 0, s => s
  | fuel + 1, s => runAcc read₁ key₁ read₂ key₂ report B fuel₁ fuel₂ fuel
      (step read₁ key₁ read₂ key₂ report B fuel₁ fuel₂ s)

def run (read₁ : σ₁ → Option (α × σ₁)) (key₁ : α → ℤ)
    (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ)
    (report : α → β → τ → τ × Bool) (B fuel₁ fuel₂ controlFuel : ℕ)
    (s₁ : σ₁) (s₂ : σ₂) (a : τ) : State σ₁ σ₂ τ :=
  runAcc read₁ key₁ read₂ key₂ report B fuel₁ fuel₂ controlFuel (start s₁ s₂ a)

def rank (view₁ : σ₁ → List α) (view₂ : σ₂ → List β) (s : State σ₁ σ₂ τ) : ℕ :=
  (view₁ s.left).length + (view₂ s.right).length

def potential (key₁ : α → ℤ) (key₂ : β → ℤ)
    (view₁ : σ₁ → List α) (view₂ : σ₂ → List β) (s : State σ₁ σ₂ τ) : ℕ :=
  MatchPotential.count key₁ key₂ (view₁ s.left) (view₂ s.right)

def WellFormed (key₁ : α → ℤ) (key₂ : β → ℤ)
    (view₁ : σ₁ → List α) (view₂ : σ₂ → List β) (fuel₁ fuel₂ : ℕ)
    (s : State σ₁ σ₂ τ) : Prop :=
  (view₁ s.left).Pairwise (fun x y => key₁ x ≤ key₁ y) ∧
  (view₂ s.right).Pairwise (fun x y => key₂ x ≤ key₂ y) ∧
  (view₁ s.left).length ≤ fuel₁ ∧ (view₂ s.right).length ≤ fuel₂

theorem step_done (read₁ : σ₁ → Option (α × σ₁)) (key₁ : α → ℤ)
    (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ)
    (report : α → β → τ → τ × Bool) (B fuel₁ fuel₂ : ℕ)
    (s : State σ₁ σ₂ τ) (hs : s.done = true) :
    step read₁ key₁ read₂ key₂ report B fuel₁ fuel₂ s = s := by
  simp only [step, hs, ite_true]

theorem runAcc_done (read₁ : σ₁ → Option (α × σ₁)) (key₁ : α → ℤ)
    (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ)
    (report : α → β → τ → τ × Bool) (B fuel₁ fuel₂ fuel : ℕ)
    (s : State σ₁ σ₂ τ) (hs : s.done = true) :
    runAcc read₁ key₁ read₂ key₂ report B fuel₁ fuel₂ fuel s = s := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => rw [runAcc, step_done _ _ _ _ _ _ _ _ s hs, ih]

end StreamJoin
end LowSpaceSubsetSum

end OAI
