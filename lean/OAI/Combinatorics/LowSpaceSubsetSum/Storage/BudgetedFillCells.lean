import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedReplayLoops

namespace OAI

/-! # Live cells in the tail-recursive prepaid tie buffer

The live counter retains the buffer and the two cursors around a fetch.
Reader and key calls supply their own scratch traces. The loop drops its old
cursor before the tail call, so the bound is independent of the query count.
-/

namespace LowSpaceSubsetSum.BudgetedFillCells

universe u v
variable {α : Type u} {σ : Type v}

def loop (charge : ℕ) (read : σ → (Option (α × σ) × ℕ) × ℕ)
    (key : α → (ℤ × ℕ) × ℕ) (cells : α → ℕ) (stateCells : σ → ℕ) (K : ℤ) :
    ℕ → σ → Array α → ℕ → ℕ → ℕ → ℕ → ℕ →
      (Option (TieBuffer.Result α σ × ℕ) × ℕ) × ℕ
  | fuel, s, buf, q, budget, work, used, peak =>
    let live := max peak (used + stateCells s + 16)
    if charge ≤ budget then
      let left := budget - charge
      match fuel with
      | 0 => ((some (⟨buf, s, q⟩, left), work + 1), live)
      | fuel + 1 =>
        let fetched := read s
        let live := max live (used + stateCells s + fetched.2 + 16)
        match fetched.1.1 with
        | none => ((some (⟨buf, s, q + 1⟩, left), work + fetched.1.2 + 5), live)
        | some (x, s') =>
          let found := key x
          let live := max live
            (2 * used + stateCells s + stateCells s' + 2 * cells x + found.2 + 20)
          if found.1.1 = K then
            loop charge read key cells stateCells K fuel s' (buf.push x) (q + 1) left
              (work + (fetched.1.2 + found.1.2 + cells x + 8)) (used + cells x + 1) live
          else ((some (⟨buf, s, q + 1⟩, left), work + fetched.1.2 + found.1.2 + 6), live)
    else ((none, work + 1), live)

theorem loop_value (charge : ℕ) (read : σ → (Option (α × σ) × ℕ) × ℕ)
    (key : α → (ℤ × ℕ) × ℕ) (cells : α → ℕ) (stateCells : σ → ℕ) (K : ℤ)
    (fuel : ℕ) (s : σ) (buf : Array α) (q budget work used peak : ℕ) :
    (loop charge read key cells stateCells K fuel s buf q budget work used peak).1 =
      ((BudgetedFill.execute charge (fun s => (read s).1) (fun x => (key x).1)
        cells K fuel s buf q budget).1,
        work + (BudgetedFill.execute charge (fun s => (read s).1) (fun x => (key x).1)
          cells K fuel s buf q budget).2) := by
  induction fuel generalizing s buf q budget work used peak with
  | zero => rw [loop, BudgetedFill.execute]; split <;> rfl
  | succ fuel ih =>
    rw [loop, BudgetedFill.execute]
    split
    · dsimp only
      cases hr : (read s).1.1 with
      | none => simp only [Nat.add_assoc]
      | some p =>
        rcases p with ⟨x, s'⟩
        dsimp only
        split
        · rw [ih]
          simp only [Nat.add_assoc]
        · simp only [Nat.add_assoc]
    · rfl

theorem loop_cells (charge : ℕ) (read : σ → (Option (α × σ) × ℕ) × ℕ)
    (key : α → (ℤ × ℕ) × ℕ) (cells : α → ℕ) (stateCells : σ → ℕ) (K : ℤ)
    (R L S X : ℕ) (hr : ∀ s, (read s).2 ≤ R) (hk : ∀ x, (key x).2 ≤ L)
    (hs : ∀ s, stateCells s ≤ S) (hx : ∀ x, cells x ≤ X)
    (fuel : ℕ) (s : σ) (buf : Array α) (q budget work used peak : ℕ) :
    (loop charge read key cells stateCells K fuel s buf q budget work used peak).2 ≤
      max peak (2 * (used + (X + 1) * fuel) + 2 * S + R + L + 2 * X + 40) := by
  induction fuel generalizing s buf q budget work used peak with
  | zero =>
    have h := hs s
    simp only [loop, Nat.mul_zero, Nat.add_zero]
    split <;> dsimp only
    all_goals exact max_le_max le_rfl (by omega)
  | succ fuel ih =>
    have hstate := hs s
    have hread := hr s
    rw [loop]
    split
    · dsimp only
      cases hfetch : (read s).1.1 with
      | none =>
        dsimp only
        simp only [Nat.mul_add, Nat.mul_one]
        omega
      | some p =>
        rcases p with ⟨x, s'⟩
        have hstate' := hs s'
        have hkey := hk x
        have hcell := hx x
        dsimp only
        split
        · have hi := ih s' (buf.push x) (q + 1) (budget - charge)
            (work + ((read s).1.2 + (key x).1.2 + cells x + 8))
            (used + cells x + 1)
            (max (max (max peak (used + stateCells s + 16))
              (used + stateCells s + (read s).2 + 16))
              (2 * used + stateCells s + stateCells s' + 2 * cells x + (key x).2 + 20))
          simp only [Nat.mul_add, Nat.mul_one] at hi ⊢
          omega
        · simp only [Nat.mul_add, Nat.mul_one]
          omega
    · dsimp only
      simp only [Nat.mul_add, Nat.mul_one]
      omega

def run (charge : ℕ) (read : σ → (Option (α × σ) × ℕ) × ℕ)
    (key : α → (ℤ × ℕ) × ℕ) (cells : α → ℕ) (stateCells : σ → ℕ) (K : ℤ)
    (B : ℕ) (s : σ) (budget : ℕ) : (Option (TieBuffer.Result α σ × ℕ) × ℕ) × ℕ :=
  loop charge read key cells stateCells K B s #[] 0 budget 0 1 0

theorem run_value (charge : ℕ) (read : σ → (Option (α × σ) × ℕ) × ℕ)
    (key : α → (ℤ × ℕ) × ℕ) (cells : α → ℕ) (stateCells : σ → ℕ) (K : ℤ)
    (B : ℕ) (s : σ) (budget : ℕ) :
    (run charge read key cells stateCells K B s budget).1 =
      BudgetedFill.execute charge (fun s => (read s).1) (fun x => (key x).1)
        cells K B s #[] 0 budget := by
  simpa only [run, Nat.zero_add] using
    loop_value charge read key cells stateCells K B s #[] 0 budget 0 1 0

theorem run_cells (charge : ℕ) (read : σ → (Option (α × σ) × ℕ) × ℕ)
    (key : α → (ℤ × ℕ) × ℕ) (cells : α → ℕ) (stateCells : σ → ℕ) (K : ℤ)
    (R L S X : ℕ) (hr : ∀ s, (read s).2 ≤ R) (hk : ∀ x, (key x).2 ≤ L)
    (hs : ∀ s, stateCells s ≤ S) (hx : ∀ x, cells x ≤ X)
    (B : ℕ) (s : σ) (budget : ℕ) :
    (run charge read key cells stateCells K B s budget).2 ≤
      2 * ((X + 1) * B + 1) + 2 * S + R + L + 2 * X + 40 := by
  simpa only [run, Nat.zero_max, Nat.add_comm 1] using
    loop_cells charge read key cells stateCells K R L S X hr hk hs hx B s #[] 0 budget 0 1 0

end LowSpaceSubsetSum.BudgetedFillCells

end OAI
