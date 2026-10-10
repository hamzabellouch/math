import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

namespace OAI

/-! # Powers of a unit plus a square-zero element -/
namespace PolycyclicRecognition

theorem one_add_pow_of_square_zero {R : Type*} [Semiring R]
    (x : R) (hx : x * x = 0) (n : ℕ) : (1 + x) ^ n = 1 + n • x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]
    calc
      (1 + n • x) * (1 + x) = 1 + (n + 1) • x := by
        rw [add_mul, one_mul, mul_add, mul_one, smul_mul_assoc, hx, nsmul_zero,
          add_zero, succ_nsmul]
        ac_rfl

theorem one_add_cube {R : Type*} [Ring R] (x : R) :
    (1 + x) ^ 3 = 1 + 3 • x + 3 • (x * x) + x * x * x := by
  noncomm_ring

end PolycyclicRecognition

end OAI
