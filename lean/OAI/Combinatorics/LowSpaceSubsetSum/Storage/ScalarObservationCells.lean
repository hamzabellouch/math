import OAI.Combinatorics.LowSpaceSubsetSum.Storage.BudgetedFillCells
import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedSnapshot

namespace OAI

/-! # Lookahead, snapshots and scalar tie-buffer capacity -/

namespace LowSpaceSubsetSum.ScalarObservationCells

universe u
variable {σ : Type u}

private theorem fillAcc_size (read : σ → Option (ℤ × σ) × ℕ)
    (key : ℤ → ℤ × ℕ) (K : ℤ) (fuel : ℕ) (s : σ) (buf : Array ℤ) (q : ℕ) :
    (CountedFill.fillAcc read key (fun _ => 1) K fuel s buf q).1.buffer.size ≤ buf.size+fuel := by
  induction fuel generalizing s buf q with
  | zero => simp only [CountedFill.fillAcc]; omega
  | succ fuel ih =>
    rw [CountedFill.fillAcc]
    dsimp only
    cases hr : (read s).1 with
    | none => dsimp only; omega
    | some p =>
      rcases p with ⟨x,s'⟩
      dsimp only
      split
      · have h := ih s' (buf.push x) (q+1)
        simpa only [Array.size_push,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h
      · dsimp only; omega

theorem fill_capacity (charge : ℕ) (read : σ → (Option (ℤ × σ) × ℕ) × ℕ)
    (key : ℤ → (ℤ × ℕ) × ℕ) (stateCells : σ → ℕ) (K : ℤ) (B : ℕ)
    (s : σ) (budget : ℕ) (out : TieBuffer.Result ℤ σ) (left : ℕ)
    (h : (BudgetedFillCells.run charge read key (fun _ => 1) stateCells K B s budget).1.1 =
      some (out,left)) : out.buffer.size ≤ B := by
  have he := congrArg Prod.fst
    (BudgetedFillCells.run_value charge read key (fun _ => 1) stateCells K B s budget)
  have hv := BudgetedFill.execute_value charge (fun s => (read s).1) (fun x => (key x).1)
    (fun _ => 1) K B s #[] 0 budget out left (he.symm.trans h)
  rw [hv.1]
  simpa only [Array.size_empty,Nat.zero_add] using fillAcc_size
    (fun s => (read s).1) (fun x => (key x).1) K B s #[] 0

def hasKey (read : σ → (Option (ℤ × σ) × ℕ) × ℕ) (key : ℤ → (ℤ × ℕ) × ℕ)
    (stateCells : σ → ℕ) (K : ℤ) (s : σ) : (Bool × ℕ) × ℕ :=
  let fetched := read s
  match fetched.1.1 with
  | none => ((false,fetched.1.2+3),stateCells s+fetched.2+8)
  | some (x,s') =>
    let found := key x
    ((decide (found.1.1=K),fetched.1.2+found.1.2+4),
      max (stateCells s+fetched.2+8) (stateCells s+stateCells s'+found.2+17))

theorem hasKey_value (read : σ → (Option (ℤ × σ) × ℕ) × ℕ)
    (key : ℤ → (ℤ × ℕ) × ℕ) (stateCells : σ → ℕ) (K : ℤ) (s : σ) :
    (hasKey read key stateCells K s).1 =
      CountedFill.hasKey (fun s => (read s).1) (fun x => (key x).1) K s := by
  unfold hasKey CountedFill.hasKey
  dsimp only
  cases (read s).1.1 <;> rfl

theorem hasKey_cells (read : σ → (Option (ℤ × σ) × ℕ) × ℕ)
    (key : ℤ → (ℤ × ℕ) × ℕ) (stateCells : σ → ℕ)
    (H : ℕ) (hH : 100 ≤ H) (hs : ∀ s, stateCells s ≤ H)
    (hr : ∀ s, (read s).2 ≤ H) (hk : ∀ x, (key x).2 ≤ H) (K : ℤ) (s : σ) :
    (hasKey read key stateCells K s).2 ≤ 4*H := by
  have hs₀ := hs s
  have hr₀ := hr s
  unfold hasKey
  dsimp only
  cases (read s).1.1 with
  | none => dsimp only; omega
  | some p =>
    rcases p with ⟨x,s'⟩
    have hs₁ := hs s'
    have hx := hk x
    dsimp only
    omega

def snapshot (clone : σ → (σ × ℕ) × ℕ) (charge : ℕ) (needed : Bool) (s : σ) (budget : ℕ) :
    (Option (σ × ℕ) × ℕ) × ℕ :=
  if needed then
    if charge ≤ budget then
      let out := clone s
      ((some (out.1.1,budget-charge),out.1.2),out.2+8)
    else ((none,1),8)
  else ((some (s,budget),0),8)

theorem snapshot_value (clone : σ → (σ × ℕ) × ℕ) (charge : ℕ) (needed : Bool) (s : σ)
    (budget : ℕ) : (snapshot clone charge needed s budget).1 =
      BudgetedSnapshot.execute charge (fun s => (clone s).1) needed s budget := by
  unfold snapshot BudgetedSnapshot.execute
  split
  · split <;> rfl
  · rfl

theorem snapshot_cells (clone : σ → (σ × ℕ) × ℕ) (H : ℕ) (hH : 100 ≤ H)
    (hc : ∀ s, (clone s).2 ≤ H) (charge : ℕ) (needed : Bool) (s : σ) (budget : ℕ) :
    (snapshot clone charge needed s budget).2 ≤ 2*H := by
  have h := hc s
  unfold snapshot
  split
  · split <;> dsimp only <;> omega
  · dsimp only; omega

end LowSpaceSubsetSum.ScalarObservationCells

end OAI
