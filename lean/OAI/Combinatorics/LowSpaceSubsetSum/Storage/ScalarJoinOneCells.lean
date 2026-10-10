import OAI.Combinatorics.LowSpaceSubsetSum.Storage.BudgetedReplayCells
import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedJoinOne

namespace OAI

/-! # Live storage in buffered scalar replay

The parameter bounds describe concrete primitive calls. The proof is
independent of the replay fuel: only the current cursor and user state,
the shared tie buffer, and one cloned cursor remain live.
-/

namespace LowSpaceSubsetSum.ScalarJoinOneCells

universe u v
variable {σ : Type u} {τ : Type v}

private def bufferRead (xs : Array ℤ) (i : ℕ) := ((BufferReplay.read xs i,4),8)

def buffer (charge : ℕ) (key : ℤ → (ℤ × ℕ) × ℕ) (K : ℤ)
    (report : ℤ → τ → ((τ × Bool) × ℕ) × ℕ) (userCells : τ → ℕ)
    (xs : Array ℤ) (a : τ) (budget : ℕ) :=
  BudgetedReplayCells.run charge (bufferRead xs) key K report (fun _ => 1)
    userCells (fun _ => 1) xs.size 0 a 0 0 budget

theorem buffer_value (charge : ℕ) (key : ℤ → (ℤ × ℕ) × ℕ) (K : ℤ)
    (report : ℤ → τ → ((τ × Bool) × ℕ) × ℕ) (userCells : τ → ℕ)
    (xs : Array ℤ) (a : τ) (budget : ℕ) :
    (buffer charge key K report userCells xs a budget).1 =
      BudgetedReplay.execute charge (fun i => (BufferReplay.read xs i,4))
        (fun x => (key x).1) K (fun x a => (report x a).1) xs.size 0 a 0 0 budget := by
  rw [buffer,BudgetedReplayCells.run_value]
  rfl

theorem buffer_cells (charge : ℕ) (key : ℤ → (ℤ × ℕ) × ℕ) (K : ℤ)
    (report : ℤ → τ → ((τ × Bool) × ℕ) × ℕ) (userCells : τ → ℕ)
    (H : ℕ) (hH : 100 ≤ H) (hu : ∀ a, userCells a ≤ H)
    (hk : ∀ x, (key x).2 ≤ H) (hp : ∀ x a, (report x a).2 ≤ H)
    (xs : Array ℤ) (a : τ) (budget : ℕ) :
    (buffer charge key K report userCells xs a budget).2 ≤ 6*H := by
  have h := BudgetedReplayCells.run_cells charge (bufferRead xs) key K report
    (fun _ => 1) userCells (fun _ => 1) 1 H 1 8 H H
    (fun _ => le_rfl) hu (fun _ => le_rfl) (fun _ => le_rfl) hk hp xs.size 0 a 0 0 budget
  change (buffer charge key K report userCells xs a budget).2 ≤ _ at h
  omega

def run (charge copyCharge : ℕ) (read : σ → (Option (ℤ × σ) × ℕ) × ℕ)
    (key : ℤ → (ℤ × ℕ) × ℕ) (K : ℤ)
    (report : ℤ → τ → ((τ × Bool) × ℕ) × ℕ)
    (clone : σ → (σ × ℕ) × ℕ) (stateCells : σ → ℕ) (userCells : τ → ℕ)
    (xs : Array ℤ) (saved : σ) (long : Bool) (fuel : ℕ) (a : τ) (budget : ℕ) :
    (Option (TieReplay.Result σ τ × ℕ) × ℕ) × ℕ :=
  let retained := 2*xs.size+stateCells saved+userCells a+32
  if 6 ≤ budget then
    let first := buffer charge key K report userCells xs a (budget-6)
    let peak := retained+first.2+16
    match first.1.1 with
    | none => ((none,first.1.2+6),peak)
    | some (out,left) =>
      if out.halted then
        ((some (⟨saved,out.state,out.queries,out.reports,false,true⟩,left),first.1.2+6),peak)
      else if long then
        if copyCharge ≤ left then
          let copied := clone saved
          let rest := BudgetedReplayCells.run charge read key K report stateCells userCells
            (fun _ => 1) fuel copied.1.1 out.state 0 0 (left-copyCharge)
          ((rest.1.1.map (fun (tail,remaining) =>
              (⟨tail.cursor,tail.state,out.queries+tail.queries,
                out.reports+tail.reports,tail.complete,tail.halted⟩,remaining)),
            first.1.2+copied.1.2+rest.1.2+6),
            max peak (max (retained+userCells out.state+copied.2+16)
              (retained+userCells out.state+rest.2+32)))
        else ((none,first.1.2+7),peak)
      else ((some (⟨saved,out.state,out.queries,out.reports,true,false⟩,left),first.1.2+6),peak)
  else ((none,1),retained)

theorem run_value (charge copyCharge : ℕ) (read : σ → (Option (ℤ × σ) × ℕ) × ℕ)
    (key : ℤ → (ℤ × ℕ) × ℕ) (K : ℤ)
    (report : ℤ → τ → ((τ × Bool) × ℕ) × ℕ)
    (clone : σ → (σ × ℕ) × ℕ) (stateCells : σ → ℕ) (userCells : τ → ℕ)
    (xs : Array ℤ) (saved : σ) (long : Bool) (fuel : ℕ) (a : τ) (budget : ℕ) :
    (run charge copyCharge read key K report clone stateCells userCells xs saved long fuel a budget).1 =
      BudgetedJoinOne.execute charge copyCharge (fun s => (read s).1) (fun x => (key x).1) K
        (fun x a => (report x a).1) (fun s => (clone s).1) xs saved long fuel a budget := by
  unfold run BudgetedJoinOne.execute
  dsimp only
  split
  · simp only [buffer_value]
    cases hfirst : (BudgetedReplay.execute charge (fun i => (BufferReplay.read xs i,4))
        (fun x => (key x).1) K (fun x a => (report x a).1) xs.size 0 a 0 0 (budget-6)).1 with
    | none => rfl
    | some p =>
      rcases p with ⟨out,left⟩
      dsimp only
      by_cases hh : out.halted = true
      · simp only [hh,↓reduceIte]
      · simp only [hh,Bool.false_eq_true,↓reduceIte]
        by_cases hl : long = true
        · simp only [hl,↓reduceIte]
          by_cases hc : copyCharge ≤ left
          · simp only [hc,↓reduceIte,BudgetedReplayCells.run_value]
          · simp only [hc,↓reduceIte]
        · simp only [hl,Bool.false_eq_true,↓reduceIte]
  · rfl

theorem run_cells (charge copyCharge : ℕ) (read : σ → (Option (ℤ × σ) × ℕ) × ℕ)
    (key : ℤ → (ℤ × ℕ) × ℕ) (K : ℤ)
    (report : ℤ → τ → ((τ × Bool) × ℕ) × ℕ)
    (clone : σ → (σ × ℕ) × ℕ) (stateCells : σ → ℕ) (userCells : τ → ℕ)
    (H : ℕ) (hH : 100 ≤ H) (hs : ∀ s, stateCells s ≤ H) (hu : ∀ a, userCells a ≤ H)
    (hr : ∀ s, (read s).2 ≤ H) (hk : ∀ x, (key x).2 ≤ H)
    (hp : ∀ x a, (report x a).2 ≤ H) (hc : ∀ s, (clone s).2 ≤ H)
    (xs : Array ℤ) (hxs : xs.size ≤ H) (saved : σ) (long : Bool) (fuel : ℕ) (a : τ) (budget : ℕ) :
    (run charge copyCharge read key K report clone stateCells userCells xs saved long fuel a budget).2 ≤
      16*H := by
  have hret : 2*xs.size+stateCells saved+userCells a+32 ≤ 5*H := by
    have h₁ := hs saved
    have h₂ := hu a
    omega
  have hb := buffer_cells charge key K report userCells H hH hu hk hp xs a (budget-6)
  have hcopy := hc saved
  unfold run
  dsimp only
  split
  · cases hout : (buffer charge key K report userCells xs a (budget-6)).1.1 with
    | none => dsimp only; omega
    | some p =>
      rcases p with ⟨out,left⟩
      have huo := hu out.state
      dsimp only
      split
      · omega
      · split
        · split
          · have ht := BudgetedReplayCells.run_cells charge read key K report stateCells userCells
              (fun _ => 1) H H 1 H H H hs hu (fun _ => le_rfl) hr hk hp
              fuel (clone saved).1.1 out.state 0 0 (left-copyCharge)
            dsimp only
            omega
          · omega
        · omega
  · dsimp only; omega

end LowSpaceSubsetSum.ScalarJoinOneCells

end OAI
