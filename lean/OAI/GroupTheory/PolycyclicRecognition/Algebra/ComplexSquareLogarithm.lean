import Mathlib.Analysis.SpecialFunctions.Complex.Log

namespace OAI

/-! # A conjugation-compatible logarithm of a complex square

This scalar choice avoids a branch obstruction for the real logarithm of
the square of a real linear automorphism.
-/

noncomputable section
namespace PolycyclicRecognition

def complexSquareLog (z : ℂ) : ℂ :=
  if z.im = 0 then 2 * (Real.log |z.re| : ℂ) else 2 * Complex.log z

theorem complexSquareLog_conj (z : ℂ) :
    complexSquareLog (star z) = star (complexSquareLog z) := by
  by_cases hi : z.im = 0
  · simp [complexSquareLog, hi]
  · have ha : z.arg ≠ Real.pi := fun h => hi (Complex.arg_eq_pi_iff.mp h).2
    simp [complexSquareLog, hi, Complex.log_conj z ha]

theorem exp_complexSquareLog {z : ℂ} (hz : z ≠ 0) :
    Complex.exp (complexSquareLog z) = z ^ 2 := by
  by_cases hi : z.im = 0
  · rw [complexSquareLog, ite_eq_left hi, two_mul, Complex.exp_add, ← pow_two]
    have hr : z.re ≠ 0 := by
      intro h
      apply hz
      exact Complex.ext h hi
    have he : Complex.exp (Real.log |z.re| : ℂ) = ((|z.re| : ℝ) : ℂ) := by
      rw [← Complex.ofReal_exp, Real.exp_log (abs_pos.mpr hr)]
    rw [he, ← Complex.ofReal_pow, sq_abs, Complex.ofReal_pow]
    have hzreal : z = (z.re : ℂ) := by
      apply Complex.ext
      · rfl
      · exact hi
    exact congrArg (fun w : ℂ => w ^ 2) hzreal.symm
  · rw [complexSquareLog, ite_eq_right hi, two_mul, Complex.exp_add,
      Complex.exp_log hz, ← pow_two]

end PolycyclicRecognition

end

end OAI
