import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedReplay
import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedFill

namespace OAI

/-! # Tail-recursive implementations of prepaid inner loops

The accumulated work counter removes return frames while retaining exactly
the measured semantics used in the correctness proofs.
-/

namespace LowSpaceSubsetSum.BudgetedReplayLoop

universe u v w
variable {α : Type u} {σ : Type v} {τ : Type w}

def loop (charge : ℕ) (read : σ → Option (α × σ) × ℕ) (key : α → ℤ × ℕ) (K : ℤ)
    (report : α → τ → (τ × Bool) × ℕ) :
    ℕ → σ → τ → ℕ → ℕ → ℕ → ℕ → Option (TieReplay.Result σ τ × ℕ) × ℕ
  | fuel, s, a, q, r, budget, work =>
    if charge ≤ budget then
      let left := budget - charge
      match fuel with
      | 0 => (some (⟨s, a, q, r, false, false⟩, left), work + 1)
      | fuel + 1 =>
        let fetched := read s
        match fetched.1 with
        | none => (some (⟨s, a, q + 1, r, true, false⟩, left), work + (fetched.2 + 5))
        | some (x, s') =>
          let found := key x
          if found.1 = K then
            let out := report x a
            if out.1.2 then
              (some (⟨s', out.1.1, q + 1, r + 1, false, true⟩, left),
                work + (fetched.2 + found.2 + out.2 + 8))
            else loop charge read key K report fuel s' out.1.1 (q + 1) (r + 1) left
              (work + (fetched.2 + found.2 + out.2 + 8))
          else (some (⟨s, a, q + 1, r, true, false⟩, left), work + (fetched.2 + found.2 + 6))
    else (none, work + 1)

theorem loop_eq (charge : ℕ) (read : σ → Option (α × σ) × ℕ) (key : α → ℤ × ℕ) (K : ℤ)
    (report : α → τ → (τ × Bool) × ℕ) (fuel : ℕ) (s : σ) (a : τ) (q r budget work : ℕ) :
    loop charge read key K report fuel s a q r budget work =
      ((BudgetedReplay.execute charge read key K report fuel s a q r budget).1,
        work + (BudgetedReplay.execute charge read key K report fuel s a q r budget).2) := by
  induction fuel generalizing s a q r budget work with
  | zero => rw [loop, BudgetedReplay.execute]; split <;> rfl
  | succ fuel ih =>
    rw [loop, BudgetedReplay.execute]
    split
    · dsimp only
      cases hr : (read s).1 with
      | none => dsimp only
      | some p =>
        rcases p with ⟨x, s'⟩
        dsimp only
        split
        · split
          · rfl
          · rw [ih]
            simp only [Nat.add_assoc]
        · rfl
    · rfl

def execute (charge : ℕ) (read : σ → Option (α × σ) × ℕ) (key : α → ℤ × ℕ) (K : ℤ)
    (report : α → τ → (τ × Bool) × ℕ) (fuel : ℕ) (s : σ) (a : τ) (q r budget : ℕ) :=
  loop charge read key K report fuel s a q r budget 0

@[csimp] theorem execute_eq : @BudgetedReplay.execute.{u, v, w} = @execute.{u, v, w} := by
  funext α σ τ charge read key K report fuel s a q r budget
  rw [execute, loop_eq]
  simp only [Nat.zero_add]

end LowSpaceSubsetSum.BudgetedReplayLoop

namespace LowSpaceSubsetSum.BudgetedFillLoop

universe u v
variable {α : Type u} {σ : Type v}

def loop (charge : ℕ) (read : σ → Option (α × σ) × ℕ)
    (key : α → ℤ × ℕ) (cells : α → ℕ) (K : ℤ) :
    ℕ → σ → Array α → ℕ → ℕ → ℕ → Option (TieBuffer.Result α σ × ℕ) × ℕ
  | fuel, s, buf, q, budget, work =>
    if charge ≤ budget then
      let left := budget - charge
      match fuel with
      | 0 => (some (⟨buf, s, q⟩, left), work + 1)
      | fuel + 1 =>
        let fetched := read s
        match fetched.1 with
        | none => (some (⟨buf, s, q + 1⟩, left), work + (fetched.2 + 5))
        | some (x, s') =>
          let found := key x
          if found.1 = K then
            loop charge read key cells K fuel s' (buf.push x) (q + 1) left
              (work + (fetched.2 + found.2 + cells x + 8))
          else (some (⟨buf, s, q + 1⟩, left), work + (fetched.2 + found.2 + 6))
    else (none, work + 1)

theorem loop_eq (charge : ℕ) (read : σ → Option (α × σ) × ℕ)
    (key : α → ℤ × ℕ) (cells : α → ℕ) (K : ℤ)
    (fuel : ℕ) (s : σ) (buf : Array α) (q budget work : ℕ) :
    loop charge read key cells K fuel s buf q budget work =
      ((BudgetedFill.execute charge read key cells K fuel s buf q budget).1,
        work + (BudgetedFill.execute charge read key cells K fuel s buf q budget).2) := by
  induction fuel generalizing s buf q budget work with
  | zero => rw [loop, BudgetedFill.execute]; split <;> rfl
  | succ fuel ih =>
    rw [loop, BudgetedFill.execute]
    split
    · dsimp only
      cases hr : (read s).1 with
      | none => dsimp only
      | some p =>
        rcases p with ⟨x, s'⟩
        dsimp only
        split
        · rw [ih]
          simp only [Nat.add_assoc]
        · rfl
    · rfl

def execute (charge : ℕ) (read : σ → Option (α × σ) × ℕ)
    (key : α → ℤ × ℕ) (cells : α → ℕ) (K : ℤ)
    (fuel : ℕ) (s : σ) (buf : Array α) (q budget : ℕ) :=
  loop charge read key cells K fuel s buf q budget 0

@[csimp] theorem execute_eq : @BudgetedFill.execute.{u, v} = @execute.{u, v} := by
  funext α σ charge read key cells K fuel s buf q budget
  rw [execute, loop_eq]
  simp only [Nat.zero_add]

end LowSpaceSubsetSum.BudgetedFillLoop

end OAI
