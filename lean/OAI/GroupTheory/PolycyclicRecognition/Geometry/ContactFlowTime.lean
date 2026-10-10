import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Ring

namespace OAI

/-! # The inside-letter flow parameter at the inward contact pivot -/

namespace PolycyclicRecognition

/-- Conjugating an allowed neighboring step back through the scalar
contact dilation leaves only an exponential error proportional to `δ`. -/
theorem contact_flow_time_bound (r s δ c η t : ℝ)
    (ht : |t| ≤ Real.exp (((1 + δ) * s + η) * r)) :
    |t * Real.exp (-((1 - (c + 1) * δ) * s * r))| ≤
      Real.exp ((((c + 2) * s) * δ + η) * r) := by
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  apply (mul_le_mul_of_nonneg_right ht (Real.exp_pos _).le).trans_eq
  rw [← Real.exp_add]
  congr 1
  ring

/-- Applying the contact dilation recovers the original neighboring step. -/
theorem contact_flow_time_reconstruction (r s δ c t : ℝ) :
    (t * Real.exp (-((1 - (c + 1) * δ) * s * r))) *
      Real.exp ((1 - (c + 1) * δ) * s * r) = t := by
  rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]

end PolycyclicRecognition

end OAI
