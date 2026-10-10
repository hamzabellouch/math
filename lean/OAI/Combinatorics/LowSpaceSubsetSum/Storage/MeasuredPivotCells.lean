import OAI.Combinatorics.LowSpaceSubsetSum.Streams.MeasuredPivot

namespace OAI

/-! # Constant-retention binary-search scratch

The search retains one pair of interval endpoints, one midpoint, and the
scratch of a single predicate invocation. The peak accumulator does not
retain earlier intervals.
-/

namespace LowSpaceSubsetSum.MeasuredPivotCells

variable {n : ℕ}

def step (p : Fin n → (Bool × ℕ) × ℕ) (c : BinaryPivot.Cut n) :
    (BinaryPivot.Cut n × ℕ) × ℕ :=
  if h : c.lo < c.hi then
    let mid := (c.lo + c.hi) / 2
    have hm : mid < n := by have := c.bounded; dsimp [mid]; omega
    let q := p ⟨mid, hm⟩
    ((if q.1.1 then
        ⟨mid + 1, c.hi, by dsimp [mid]; omega, c.bounded⟩
      else ⟨c.lo, mid, by dsimp [mid]; omega, by have := c.bounded; dsimp [mid]; omega⟩,
      q.1.2 + 8), q.2 + 24)
  else ((c, 1), 8)

theorem step_value (p : Fin n → (Bool × ℕ) × ℕ) (c : BinaryPivot.Cut n) :
    (step p c).1 = BinaryPivot.measuredStep (fun i => (p i).1) c := by
  unfold step BinaryPivot.measuredStep
  split <;> rfl

theorem step_cells (p : Fin n → (Bool × ℕ) × ℕ) (R : ℕ)
    (hp : ∀ i, (p i).2 ≤ R) (c : BinaryPivot.Cut n) : (step p c).2 ≤ R + 24 := by
  unfold step
  split
  · rename_i h
    exact Nat.add_le_add_right (hp ⟨(c.lo + c.hi) / 2, by have := c.bounded; omega⟩) 24
  · omega

def loop (p : Fin n → (Bool × ℕ) × ℕ) : ℕ → BinaryPivot.Cut n → ℕ → ℕ →
    (BinaryPivot.Cut n × ℕ) × ℕ
  | 0, c, work, peak => ((c, work), max peak 16)
  | k + 1, c, work, peak =>
    let q := step p c
    loop p k q.1.1 (work + q.1.2) (max peak (q.2 + 16))

theorem loop_value (p : Fin n → (Bool × ℕ) × ℕ) (k : ℕ)
    (c : BinaryPivot.Cut n) (work peak : ℕ) :
    (loop p k c work peak).1 = BinaryPivot.measuredRun (fun i => (p i).1) k c work := by
  induction k generalizing c work peak with
  | zero => rfl
  | succ k ih =>
    rw [loop, BinaryPivot.measuredRun, ih, step_value]

theorem loop_cells (p : Fin n → (Bool × ℕ) × ℕ) (R : ℕ)
    (hp : ∀ i, (p i).2 ≤ R) (k : ℕ) (c : BinaryPivot.Cut n) (work peak : ℕ) :
    (loop p k c work peak).2 ≤ max peak (R + 40) := by
  induction k generalizing c work peak with
  | zero => simp only [loop]; exact max_le_max le_rfl (by omega)
  | succ k ih =>
    have hs := step_cells p R hp c
    have hi := ih (step p c).1.1 (work + (step p c).1.2) (max peak ((step p c).2 + 16))
    exact hi.trans (by omega)

def search (p : Fin n → (Bool × ℕ) × ℕ) (k : ℕ) := loop p k (BinaryPivot.initial n) 0 0

theorem search_value (p : Fin n → (Bool × ℕ) × ℕ) (k : ℕ) :
    (search p k).1 = BinaryPivot.measuredSearch (fun i => (p i).1) k := loop_value _ _ _ _ _

theorem search_cells (p : Fin n → (Bool × ℕ) × ℕ) (R : ℕ)
    (hp : ∀ i, (p i).2 ≤ R) (k : ℕ) : (search p k).2 ≤ R + 40 := by
  simpa only [search, Nat.zero_max] using loop_cells p R hp k (BinaryPivot.initial n) 0 0

end LowSpaceSubsetSum.MeasuredPivotCells

end OAI
