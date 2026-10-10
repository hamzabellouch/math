import Mathlib.Data.Nat.Log

namespace OAI

/-! # A bounded tail-recursive binary logarithm

This is the integer operation needed to turn measured mixer counts into
prime widths. Each iteration divides by two and updates two counters.
-/

namespace LowSpaceSubsetSum.MeasuredLog2

def loop : ℕ → ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, _, value, work => (value, work + 1)
  | fuel + 1, x, value, work =>
    if 2 ≤ x then loop fuel (x / 2) (value + 1) (work + 3)
    else (value, work + 1)

theorem loop_value (fuel x value work : ℕ) (hx : Nat.log2 x ≤ fuel) :
    (loop fuel x value work).1 = value + Nat.log2 x := by
  induction fuel generalizing x value work with
  | zero =>
    have hz : Nat.log2 x = 0 := by omega
    simp [loop, hz]
  | succ fuel ih =>
    rw [loop]
    split
    next h =>
      have he := Nat.log2_def x
      rw [ite_eq_left h] at he
      rw [ih _ _ _ (by omega), he]
      omega
    next h => simp only [Nat.log2_def x, ite_eq_right h, Nat.add_zero]

theorem loop_work (fuel x value work : ℕ) :
    (loop fuel x value work).2 ≤ work + 3 * fuel + 1 := by
  induction fuel generalizing x value work with
  | zero => simp [loop]
  | succ fuel ih =>
    rw [loop]
    split
    · have h := ih (x / 2) (value + 1) (work + 3); omega
    · simp only; omega

def run (bits x : ℕ) : ℕ × ℕ := loop bits x 0 0

theorem run_value (bits x : ℕ) (hx : x ≤ 2 ^ bits) :
    (run bits x).1 = Nat.log2 x := by
  have hlog : Nat.log2 x ≤ bits := by
    rw [Nat.log2_eq_log_two]
    have h := Nat.log_mono_right (b := 2) hx
    simpa only [Nat.log_pow (by decide : 1 < 2)] using h
  simpa only [run, Nat.zero_add] using loop_value bits x 0 0 hlog

theorem run_work (bits x : ℕ) : (run bits x).2 ≤ 3 * bits + 1 := by
  simpa only [run, Nat.zero_add] using loop_work bits x 0 0

end LowSpaceSubsetSum.MeasuredLog2

end OAI
