import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic

namespace OAI

/-! # Constant-state multiplicative binomial computation

Each iteration uses one multiplication and one exact division. The three
state fields and the division numerator have linearly bounded bit lengths.
-/

namespace LowSpaceSubsetSum.CountedBinomial

structure State where
  index : ℕ
  value : ℕ
  steps : ℕ

def initial : State := ⟨0, 1, 0⟩

def step (n : ℕ) (s : State) : State :=
  ⟨s.index + 1, s.value * (n - s.index) / (s.index + 1), s.steps + 1⟩

def runAcc (n : ℕ) : ℕ → State → State
  | 0, s => s
  | fuel + 1, s => runAcc n fuel (step n s)

def run (n k : ℕ) : State :=
  if k ≤ n then runAcc n k initial else ⟨k, 0, 0⟩

theorem recurrence (n k : ℕ) :
    n.choose k * (n - k) / (k + 1) = n.choose (k + 1) := by
  rw [← Nat.choose_succ_right_eq]
  exact Nat.mul_div_cancel _ (by omega)

theorem step_value (n : ℕ) (s : State) (h : s.value = n.choose s.index) :
    (step n s).value = n.choose (step n s).index := by
  change s.value * (n - s.index) / (s.index + 1) = n.choose (s.index + 1)
  rw [h, recurrence]

theorem runAcc_index (n fuel : ℕ) (s : State) :
    (runAcc n fuel s).index = s.index + fuel := by
  induction fuel generalizing s with
  | zero => simp [runAcc]
  | succ fuel ih =>
    simpa [runAcc, step, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (ih (step n s))

theorem runAcc_steps (n fuel : ℕ) (s : State) :
    (runAcc n fuel s).steps = s.steps + fuel := by
  induction fuel generalizing s with
  | zero => simp [runAcc]
  | succ fuel ih =>
    simpa [runAcc, step, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (ih (step n s))

theorem runAcc_value (n fuel : ℕ) (s : State) (h : s.value = n.choose s.index) :
    (runAcc n fuel s).value = n.choose (s.index + fuel) := by
  induction fuel generalizing s with
  | zero => simpa [runAcc] using h
  | succ fuel ih =>
    simpa [runAcc, step, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ih (step n s) (step_value n s h)

theorem run_value (n k : ℕ) : (run n k).value = n.choose k := by
  unfold run
  split
  · simpa [initial] using runAcc_value n k initial (by simp [initial])
  · rename_i h
    exact (Nat.choose_eq_zero_of_lt (by omega)).symm

theorem run_steps (n k : ℕ) : (run n k).steps ≤ n := by
  unfold run
  split
  · rename_i h
    simpa [runAcc_steps, initial] using h
  · exact Nat.zero_le _

/-- The division numerator is exactly divisible by the current index. -/
theorem step_divides (n : ℕ) (s : State) (h : s.value = n.choose s.index) :
    s.index + 1 ∣ s.value * (n - s.index) := by
  rw [h, ← Nat.choose_succ_right_eq]
  exact Nat.dvd_mul_left _ _

theorem value_bound (n : ℕ) (s : State) (h : s.value = n.choose s.index) :
    s.value ≤ 2 ^ n := by
  rw [h]
  exact Nat.choose_le_two_pow n s.index

theorem numerator_bound (n : ℕ) (s : State) (h : s.value = n.choose s.index) :
    s.value * (n - s.index) < 2 ^ (2 * n) := by
  calc
    s.value * (n - s.index) ≤ 2 ^ n * n :=
      Nat.mul_le_mul (value_bound n s h) (Nat.sub_le _ _)
    _ < 2 ^ n * 2 ^ n := Nat.mul_lt_mul_of_pos_left n.lt_two_pow_self (by positivity)
    _ = _ := by rw [← pow_add]; congr 1; omega

/-- This bounds every intermediate prefix state of the multiplicative loop,
not only its final returned value. -/
theorem prefix_bounds (n k j : ℕ) (hj : j ≤ k) (hk : k ≤ n) :
    let s := runAcc n j initial
    s.index ≤ n ∧ s.steps ≤ n ∧ s.value ≤ 2 ^ n ∧
      s.value * (n - s.index) < 2 ^ (2 * n) := by
  dsimp only
  have hv : (runAcc n j initial).value = n.choose (runAcc n j initial).index := by
    rw [runAcc_index]
    exact runAcc_value n j initial (by simp [initial])
  refine ⟨?_, ?_, value_bound n _ hv, numerator_bound n _ hv⟩
  · simpa [runAcc_index, initial] using hj.trans hk
  · simpa [runAcc_steps, initial] using hj.trans hk

end LowSpaceSubsetSum.CountedBinomial

end OAI
