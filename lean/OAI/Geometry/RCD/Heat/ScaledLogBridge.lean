import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace OAI

/-! # The scaled logarithmic form of a positive heat-bridge lower bound -/

namespace RegularPointCoordinates

theorem scaled_log_bridge {ε A f g E t : ℝ}
    (hε : 0 ≤ ε) (hA : 0 < A) (hf : 0 < f)
    (hbound : A*Real.exp (-E/t)*f ≤ g) :
    ε*Real.log f+ε*Real.log A-ε*E/t ≤ ε*Real.log g := by
  have hp : 0 < A*Real.exp (-E/t)*f := by positivity
  have hh := mul_le_mul_of_nonneg_left (Real.log_le_log hp hbound) hε
  rw [Real.log_mul (mul_pos hA (Real.exp_pos _)).ne' hf.ne',
    Real.log_mul hA.ne' (Real.exp_ne_zero _),Real.log_exp] at hh
  have he : ε*(Real.log A + -E/t + Real.log f) =
      ε*Real.log f+ε*Real.log A-ε*E/t := by ring
  rwa [he] at hh

end RegularPointCoordinates

end OAI
