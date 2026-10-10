import OAI.Combinatorics.LowSpaceSubsetSum.Storage.ScalarJoinOneCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.BudgetedOuterCells
import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedTieOuter

namespace OAI

/-! # The outer scalar tie replay with a shared buffer and saved reader -/

namespace LowSpaceSubsetSum.ScalarTieOuterCells

universe u v w
variable {σ₁ : Type u} {σ₂ : Type v} {τ : Type w}

def payload (stateCells : σ₂ → ℕ) (userCells : τ → ℕ) (st : TieGroup.State σ₂ τ) : ℕ :=
  stateCells st.last+userCells st.user+32

def step (charge copyCharge : ℕ) (read : σ₂ → (Option (ℤ × σ₂) × ℕ) × ℕ)
    (key : ℤ → (ℤ × ℕ) × ℕ) (K : ℤ)
    (report : ℤ → ℤ → τ → ((τ × Bool) × ℕ) × ℕ)
    (clone : σ₂ → (σ₂ × ℕ) × ℕ) (stateCells : σ₂ → ℕ) (userCells : τ → ℕ)
    (xs : Array ℤ) (saved : σ₂) (long : Bool) (fuel : ℕ)
    (x : ℤ) (st : TieGroup.State σ₂ τ) (budget : ℕ) :=
  if 6 ≤ budget then
    let inner := ScalarJoinOneCells.run charge copyCharge read key K (report x) clone
      stateCells userCells xs saved long fuel st.user (budget-6)
    ((inner.1.1.map (fun (out,left) => (BudgetedTieStep.result long st out,left)),inner.1.2+6),
      payload stateCells userCells st+inner.2+32)
  else ((none,1),payload stateCells userCells st+8)

theorem step_value (charge copyCharge : ℕ) (read : σ₂ → (Option (ℤ × σ₂) × ℕ) × ℕ)
    (key : ℤ → (ℤ × ℕ) × ℕ) (K : ℤ)
    (report : ℤ → ℤ → τ → ((τ × Bool) × ℕ) × ℕ)
    (clone : σ₂ → (σ₂ × ℕ) × ℕ) (stateCells : σ₂ → ℕ) (userCells : τ → ℕ)
    (xs : Array ℤ) (saved : σ₂) (long : Bool) (fuel : ℕ)
    (x : ℤ) (st : TieGroup.State σ₂ τ) (budget : ℕ) :
    (step charge copyCharge read key K report clone stateCells userCells
      xs saved long fuel x st budget).1 =
      BudgetedTieStep.execute charge copyCharge (fun s => (read s).1) (fun y => (key y).1) K
        (fun x y a => (report x y a).1) (fun s => (clone s).1) xs saved long fuel x st budget := by
  simp only [step,BudgetedTieStep.execute,ScalarJoinOneCells.run_value]
  split <;> rfl

theorem payload_le (stateCells : σ₂ → ℕ) (userCells : τ → ℕ) (H : ℕ)
    (hH : 100 ≤ H) (hs : ∀ s, stateCells s ≤ H) (hu : ∀ a, userCells a ≤ H)
    (st : TieGroup.State σ₂ τ) : payload stateCells userCells st ≤ 3*H := by
  have h₁ := hs st.last
  have h₂ := hu st.user
  unfold payload
  omega

theorem step_cells (charge copyCharge : ℕ) (read : σ₂ → (Option (ℤ × σ₂) × ℕ) × ℕ)
    (key : ℤ → (ℤ × ℕ) × ℕ) (K : ℤ)
    (report : ℤ → ℤ → τ → ((τ × Bool) × ℕ) × ℕ)
    (clone : σ₂ → (σ₂ × ℕ) × ℕ) (stateCells : σ₂ → ℕ) (userCells : τ → ℕ)
    (H : ℕ) (hH : 100 ≤ H) (hs : ∀ s, stateCells s ≤ H) (hu : ∀ a, userCells a ≤ H)
    (hr : ∀ s, (read s).2 ≤ H) (hk : ∀ x, (key x).2 ≤ H)
    (hp : ∀ x y a, (report x y a).2 ≤ H) (hc : ∀ s, (clone s).2 ≤ H)
    (xs : Array ℤ) (hxs : xs.size ≤ H) (saved : σ₂) (long : Bool) (fuel : ℕ)
    (x : ℤ) (st : TieGroup.State σ₂ τ) (budget : ℕ) :
    (step charge copyCharge read key K report clone stateCells userCells
      xs saved long fuel x st budget).2 ≤ 20*H := by
  have hpay := payload_le stateCells userCells H hH hs hu st
  have hi := ScalarJoinOneCells.run_cells charge copyCharge read key K (report x) clone
    stateCells userCells H hH hs hu hr hk (hp x) hc xs hxs saved long fuel st.user (budget-6)
  unfold step
  split <;> dsimp only <;> omega

def run (outerCharge charge copyCharge : ℕ)
    (read₁ : σ₁ → (Option (ℤ × σ₁) × ℕ) × ℕ) (key₁ : ℤ → (ℤ × ℕ) × ℕ)
    (read₂ : σ₂ → (Option (ℤ × σ₂) × ℕ) × ℕ) (key₂ : ℤ → (ℤ × ℕ) × ℕ) (K : ℤ)
    (report : ℤ → ℤ → τ → ((τ × Bool) × ℕ) × ℕ)
    (clone : σ₂ → (σ₂ × ℕ) × ℕ)
    (cells₁ : σ₁ → ℕ) (cells₂ : σ₂ → ℕ) (userCells : τ → ℕ)
    (xs : Array ℤ) (saved : σ₂) (long : Bool) (fuel₁ fuel₂ : ℕ)
    (s₁ : σ₁) (st : TieGroup.State σ₂ τ) (budget : ℕ) :=
  let out := BudgetedOuterCells.run outerCharge read₁ key₁ K
    (step charge copyCharge read₂ key₂ K report clone cells₂ userCells xs saved long fuel₂)
    cells₁ (payload cells₂ userCells) (fun _ => 1) fuel₁ s₁ st 0 0 budget
  (out.1,out.2+2*xs.size+cells₂ saved+16)

theorem run_value (outerCharge charge copyCharge : ℕ)
    (read₁ : σ₁ → (Option (ℤ × σ₁) × ℕ) × ℕ) (key₁ : ℤ → (ℤ × ℕ) × ℕ)
    (read₂ : σ₂ → (Option (ℤ × σ₂) × ℕ) × ℕ) (key₂ : ℤ → (ℤ × ℕ) × ℕ) (K : ℤ)
    (report : ℤ → ℤ → τ → ((τ × Bool) × ℕ) × ℕ)
    (clone : σ₂ → (σ₂ × ℕ) × ℕ)
    (cells₁ : σ₁ → ℕ) (cells₂ : σ₂ → ℕ) (userCells : τ → ℕ)
    (xs : Array ℤ) (saved : σ₂) (long : Bool) (fuel₁ fuel₂ : ℕ)
    (s₁ : σ₁) (st : TieGroup.State σ₂ τ) (budget : ℕ) :
    (run outerCharge charge copyCharge read₁ key₁ read₂ key₂ K report clone
      cells₁ cells₂ userCells xs saved long fuel₁ fuel₂ s₁ st budget).1 =
      BudgetedTieOuter.execute outerCharge charge copyCharge
        (fun s => (read₁ s).1) (fun x => (key₁ x).1)
        (fun s => (read₂ s).1) (fun y => (key₂ y).1) K
        (fun x y a => (report x y a).1) (fun s => (clone s).1)
        xs saved long fuel₁ fuel₂ s₁ st budget := by
  rw [run,BudgetedOuterCells.run_value]
  have hp : (fun x st b => (step charge copyCharge read₂ key₂ K report clone
      cells₂ userCells xs saved long fuel₂ x st b).1) =
      BudgetedTieStep.execute charge copyCharge (fun s => (read₂ s).1) (fun y => (key₂ y).1) K
        (fun x y a => (report x y a).1) (fun s => (clone s).1) xs saved long fuel₂ := by
    funext x st b
    exact step_value _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  rw [hp]
  rfl

theorem run_cells (outerCharge charge copyCharge : ℕ)
    (read₁ : σ₁ → (Option (ℤ × σ₁) × ℕ) × ℕ) (key₁ : ℤ → (ℤ × ℕ) × ℕ)
    (read₂ : σ₂ → (Option (ℤ × σ₂) × ℕ) × ℕ) (key₂ : ℤ → (ℤ × ℕ) × ℕ) (K : ℤ)
    (report : ℤ → ℤ → τ → ((τ × Bool) × ℕ) × ℕ)
    (clone : σ₂ → (σ₂ × ℕ) × ℕ)
    (cells₁ : σ₁ → ℕ) (cells₂ : σ₂ → ℕ) (userCells : τ → ℕ)
    (H : ℕ) (hH : 100 ≤ H) (hs₁ : ∀ s, cells₁ s ≤ H) (hs₂ : ∀ s, cells₂ s ≤ H)
    (hu : ∀ a, userCells a ≤ H)
    (hr₁ : ∀ s, (read₁ s).2 ≤ H) (hr₂ : ∀ s, (read₂ s).2 ≤ H)
    (hk₁ : ∀ x, (key₁ x).2 ≤ H) (hk₂ : ∀ x, (key₂ x).2 ≤ H)
    (hp : ∀ x y a, (report x y a).2 ≤ H) (hc : ∀ s, (clone s).2 ≤ H)
    (xs : Array ℤ) (hxs : xs.size ≤ H) (saved : σ₂) (long : Bool) (fuel₁ fuel₂ : ℕ)
    (s₁ : σ₁) (st : TieGroup.State σ₂ τ) (budget : ℕ) :
    (run outerCharge charge copyCharge read₁ key₁ read₂ key₂ K report clone
      cells₁ cells₂ userCells xs saved long fuel₁ fuel₂ s₁ st budget).2 ≤ 36*H := by
  have h := BudgetedOuterCells.run_cells outerCharge read₁ key₁ K
    (step charge copyCharge read₂ key₂ K report clone cells₂ userCells xs saved long fuel₂)
    cells₁ (payload cells₂ userCells) (fun _ => 1)
    H (3*H) 1 H H (20*H) hs₁ (payload_le cells₂ userCells H hH hs₂ hu)
    (fun _ => le_rfl) hr₁ hk₁
    (step_cells charge copyCharge read₂ key₂ K report clone cells₂ userCells
      H hH hs₂ hu hr₂ hk₂ hp hc xs hxs saved long fuel₂) fuel₁ s₁ st 0 0 budget
  have hsave := hs₂ saved
  change _+2*xs.size+cells₂ saved+16 ≤ _
  omega

end LowSpaceSubsetSum.ScalarTieOuterCells

end OAI
