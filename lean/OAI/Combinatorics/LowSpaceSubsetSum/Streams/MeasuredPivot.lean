import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationPivotWork

namespace OAI

/-! # Binary search with counted predicate evaluations

The predicate is evaluated exactly once at each nonempty interval. The
count includes endpoint arithmetic and the actual predicate callback cost.
-/

namespace LowSpaceSubsetSum.BinaryPivot

variable {n : ℕ}

def measuredStep (p : Fin n → Bool × ℕ) (c : Cut n) : Cut n × ℕ :=
  if h : c.lo < c.hi then
    let mid := (c.lo + c.hi) / 2
    have hmid : mid < n := by have := c.bounded; dsimp [mid]; omega
    let q := p ⟨mid, hmid⟩
    (if q.1 then
      ⟨mid + 1, c.hi, by dsimp [mid]; omega, c.bounded⟩
    else
      ⟨c.lo, mid, by dsimp [mid]; omega, by have := c.bounded; dsimp [mid]; omega⟩,
      q.2 + 8)
  else (c, 1)

theorem measuredStep_value (p : Fin n → Bool × ℕ) (c : Cut n) :
    (measuredStep p c).1 = step (fun i => (p i).1) c := by
  unfold measuredStep step
  split <;> rfl

theorem measuredStep_work (p : Fin n → Bool × ℕ) (K : ℕ)
    (hp : ∀ i, (p i).2 ≤ K) (c : Cut n) :
    (measuredStep p c).2 ≤ K + 8 := by
  unfold measuredStep
  split
  · rename_i h
    exact Nat.add_le_add_right (hp ⟨(c.lo + c.hi) / 2, by have := c.bounded; omega⟩) 8
  · omega

/-- The accumulator makes the search loop tail recursive. -/
def measuredRun (p : Fin n → Bool × ℕ) : ℕ → Cut n → ℕ → Cut n × ℕ
  | 0, c, work => (c, work)
  | k + 1, c, work =>
    let q := measuredStep p c
    measuredRun p k q.1 (work + q.2)

theorem measuredRun_value (p : Fin n → Bool × ℕ) (k : ℕ) (c : Cut n) (work : ℕ) :
    (measuredRun p k c work).1 = (step (fun i => (p i).1))^[k] c := by
  induction k generalizing c work with
  | zero => rfl
  | succ k ih =>
    rw [measuredRun, ih, measuredStep_value, Function.iterate_succ_apply]

theorem measuredRun_work (p : Fin n → Bool × ℕ) (K : ℕ)
    (hp : ∀ i, (p i).2 ≤ K) (k : ℕ) (c : Cut n) (work : ℕ) :
    (measuredRun p k c work).2 ≤ work + (K + 8) * k := by
  induction k generalizing c work with
  | zero => simp only [measuredRun, Nat.mul_zero, Nat.add_zero, le_refl]
  | succ k ih =>
    have hi := ih (measuredStep p c).1 (work + (measuredStep p c).2)
    have hs := measuredStep_work p K hp c
    change (measuredRun p k (measuredStep p c).1 (work + (measuredStep p c).2)).2 ≤ _
    simp only [Nat.mul_add, Nat.mul_one]
    omega

def measuredSearch (p : Fin n → Bool × ℕ) (k : ℕ) : Cut n × ℕ :=
  measuredRun p k (initial n) 0

theorem measuredSearch_value (p : Fin n → Bool × ℕ) (k : ℕ) :
    (measuredSearch p k).1 = search (fun i => (p i).1) k := measuredRun_value _ _ _ _

theorem measuredSearch_work (p : Fin n → Bool × ℕ) (K : ℕ)
    (hp : ∀ i, (p i).2 ≤ K) (k : ℕ) :
    (measuredSearch p k).2 ≤ (K + 8) * k := by
  simpa only [measuredSearch, Nat.zero_add] using measuredRun_work p K hp k (initial n) 0

end LowSpaceSubsetSum.BinaryPivot

end OAI
