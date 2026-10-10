import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace OAI

/-! # Computing a bounded binary ceiling logarithm by doubling

The executable loop stores the current power of two. It performs no call
to `Nat.clog` and never forms a power by repeated recomputation.
-/

namespace LowSpaceSubsetSum.CountedCeilLog

def loop (size : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, depth, _, work => (depth, work + 2)
  | fuel + 1, depth, power, work =>
    if size ≤ power then (depth, work + 2)
    else loop size fuel (depth + 1) (2 * power) (work + 4)

theorem loop_value (size fuel depth power work : ℕ)
    (hpower : power = 2 ^ depth) (hlo : depth ≤ Nat.clog 2 size)
    (hhi : Nat.clog 2 size ≤ depth + fuel) :
    (loop size fuel depth power work).1 = Nat.clog 2 size := by
  induction fuel generalizing depth power work with
  | zero => simp only [loop]; omega
  | succ fuel ih =>
    simp only [loop]
    split
    · rename_i h
      have hc : Nat.clog 2 size ≤ depth := Nat.clog_le_of_le_pow (h.trans_eq hpower)
      omega
    · rename_i h
      apply ih
      · rw [hpower, pow_succ]
        omega
      · have hc : depth < Nat.clog 2 size :=
          (Nat.lt_clog_iff_pow_lt (by decide)).mpr (by omega)
        omega
      · omega

theorem loop_work (size fuel depth power work : ℕ) :
    (loop size fuel depth power work).2 ≤ work + 4 * fuel + 2 := by
  induction fuel generalizing depth power work with
  | zero => simp [loop]
  | succ fuel ih =>
    simp only [loop]
    split
    · omega
    · have h := ih (depth + 1) (2 * power) (work + 4)
      omega

def run (size fuel : ℕ) : ℕ × ℕ := loop size fuel 0 1 0

theorem run_value (size fuel : ℕ) (h : size ≤ 2 ^ fuel) :
    (run size fuel).1 = Nat.clog 2 size :=
  loop_value size fuel 0 1 0 (by simp) (Nat.zero_le _)
    (by simpa only [Nat.zero_add] using Nat.clog_le_of_le_pow h)

theorem run_work (size fuel : ℕ) : (run size fuel).2 ≤ 4 * fuel + 2 := by
  simpa only [run, Nat.zero_add] using loop_work size fuel 0 1 0

end LowSpaceSubsetSum.CountedCeilLog

end OAI
