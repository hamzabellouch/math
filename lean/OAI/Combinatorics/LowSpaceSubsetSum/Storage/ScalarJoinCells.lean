import OAI.Combinatorics.LowSpaceSubsetSum.Storage.ScalarStepCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.BudgetedStoppedCells
import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedJoinExecution

namespace OAI

/-! # Tail-recursive scalar join lifetime

The stopped loop retains only its current two cursors and user state.
No previously completed group remains reachable from its successor.
-/

namespace LowSpaceSubsetSum.ScalarJoinCells

universe u v w
variable {σ₁ : Type u} {σ₂ : Type v} {τ : Type w}

def run (base front fill outer inner copy : ℕ)
    (read₁ : σ₁ → (Option (ℤ × σ₁) × ℕ) × ℕ) (key₁ : ℤ → (ℤ × ℕ) × ℕ)
    (read₂ : σ₂ → (Option (ℤ × σ₂) × ℕ) × ℕ) (key₂ : ℤ → (ℤ × ℕ) × ℕ)
    (report : ℤ → ℤ → τ → ((τ × Bool) × ℕ) × ℕ) (clone : σ₂ → (σ₂ × ℕ) × ℕ)
    (cells₁ : σ₁ → ℕ) (cells₂ : σ₂ → ℕ) (userCells : τ → ℕ)
    (B fuel₁ fuel₂ control : ℕ) (st : StreamJoin.State σ₁ σ₂ τ) (budget : ℕ) :=
  BudgetedStoppedCells.run
    (ScalarStepCells.run base front fill outer inner copy read₁ key₁ read₂ key₂ report clone
      cells₁ cells₂ userCells B fuel₁ fuel₂)
    (ScalarStepCells.frame cells₁ cells₂ userCells) control st budget

theorem run_value (base front fill outer inner copy : ℕ)
    (read₁ : σ₁ → (Option (ℤ × σ₁) × ℕ) × ℕ) (key₁ : ℤ → (ℤ × ℕ) × ℕ)
    (read₂ : σ₂ → (Option (ℤ × σ₂) × ℕ) × ℕ) (key₂ : ℤ → (ℤ × ℕ) × ℕ)
    (report : ℤ → ℤ → τ → ((τ × Bool) × ℕ) × ℕ) (clone : σ₂ → (σ₂ × ℕ) × ℕ)
    (cells₁ : σ₁ → ℕ) (cells₂ : σ₂ → ℕ) (userCells : τ → ℕ)
    (B fuel₁ fuel₂ control : ℕ) (st : StreamJoin.State σ₁ σ₂ τ) (budget : ℕ) :
    (run base front fill outer inner copy read₁ key₁ read₂ key₂ report clone
      cells₁ cells₂ userCells B fuel₁ fuel₂ control st budget).1 =
      BudgetedJoinExecution.run base front fill outer inner copy
        (fun s => (read₁ s).1) (fun x => (key₁ x).1) (fun s => (read₂ s).1) (fun y => (key₂ y).1)
        (fun _ => 1) (fun x y a => (report x y a).1) (fun s => (clone s).1)
        B fuel₁ fuel₂ control st budget := by
  rw [run,BudgetedStoppedCells.run_value]
  have he : (fun s b => (ScalarStepCells.run base front fill outer inner copy
      read₁ key₁ read₂ key₂ report clone cells₁ cells₂ userCells B fuel₁ fuel₂ s b).1) =
      BudgetedStreamStep.execute base front fill outer inner copy
        (fun s => (read₁ s).1) (fun x => (key₁ x).1) (fun s => (read₂ s).1) (fun y => (key₂ y).1)
        (fun _ => 1) (fun x y a => (report x y a).1) (fun s => (clone s).1) B fuel₁ fuel₂ := by
    funext s b
    exact ScalarStepCells.run_value base front fill outer inner copy read₁ key₁ read₂ key₂
      report clone cells₁ cells₂ userCells B fuel₁ fuel₂ s b
  rw [he]

theorem run_cells (base front fill outer inner copy : ℕ)
    (read₁ : σ₁ → (Option (ℤ × σ₁) × ℕ) × ℕ) (key₁ : ℤ → (ℤ × ℕ) × ℕ)
    (read₂ : σ₂ → (Option (ℤ × σ₂) × ℕ) × ℕ) (key₂ : ℤ → (ℤ × ℕ) × ℕ)
    (report : ℤ → ℤ → τ → ((τ × Bool) × ℕ) × ℕ) (clone : σ₂ → (σ₂ × ℕ) × ℕ)
    (cells₁ : σ₁ → ℕ) (cells₂ : σ₂ → ℕ) (userCells : τ → ℕ)
    (H : ℕ) (hH : 100 ≤ H) (hs₁ : ∀ s, cells₁ s ≤ H) (hs₂ : ∀ s, cells₂ s ≤ H)
    (hu : ∀ a, userCells a ≤ H)
    (hr₁ : ∀ s, (read₁ s).2 ≤ H) (hr₂ : ∀ s, (read₂ s).2 ≤ H)
    (hk₁ : ∀ x, (key₁ x).2 ≤ H) (hk₂ : ∀ x, (key₂ x).2 ≤ H)
    (hp : ∀ x y a, (report x y a).2 ≤ H) (hc : ∀ s, (clone s).2 ≤ H)
    (B fuel₁ fuel₂ control : ℕ) (hB : B ≤ H) (st : StreamJoin.State σ₁ σ₂ τ) (budget : ℕ) :
    (run base front fill outer inner copy read₁ key₁ read₂ key₂ report clone
      cells₁ cells₂ userCells B fuel₁ fuel₂ control st budget).2 ≤ 65*H := by
  have h := BudgetedStoppedCells.run_cells
    (ScalarStepCells.run base front fill outer inner copy read₁ key₁ read₂ key₂ report clone
      cells₁ cells₂ userCells B fuel₁ fuel₂)
    (ScalarStepCells.frame cells₁ cells₂ userCells) (4*H) (56*H)
    (ScalarStepCells.frame_cells cells₁ cells₂ userCells H hH hs₁ hs₂ hu)
    (ScalarStepCells.run_cells base front fill outer inner copy read₁ key₁ read₂ key₂ report clone
      cells₁ cells₂ userCells H hH hs₁ hs₂ hu hr₁ hr₂ hk₁ hk₂ hp hc B fuel₁ fuel₂ hB)
    control st budget
  change (run base front fill outer inner copy read₁ key₁ read₂ key₂ report clone
    cells₁ cells₂ userCells B fuel₁ fuel₂ control st budget).2 ≤ _ at h
  omega

end LowSpaceSubsetSum.ScalarJoinCells

end OAI
