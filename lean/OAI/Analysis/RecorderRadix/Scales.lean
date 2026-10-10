import Mathlib
import OAI.Analysis.RecorderRadix.Tape

namespace OAI

/-! Positive reciprocal radix scales and rational arithmetic formulas. -/

namespace Solenoidal
namespace Radix
theorem scale_pos (m : ℕ) (d : Move) : 0 < scale m d := by
  cases d <;> simp only [scale]
  · exact base_pos m
  · norm_num
  · exact inv_pos.mpr (base_pos m)

theorem prefix_strictMono {m : ℕ} (a : Fin (m + 1)) : StrictMono (pushDigit a) := by
  intro u v huv
  apply (div_lt_div_iff_of_pos_right (base_pos m)).mpr
  linarith

def rationalPrefix {m : ℕ} (a : Fin (m + 1)) (v : ℚ) : ℚ :=
  (2 * (a.val : ℚ) + 1 + v) / (2 * ((m : ℚ) + 1) + 1)

@[simp] theorem rationalPrefix_coe {m : ℕ} (a : Fin (m + 1)) (v : ℚ) :
    (rationalPrefix a v : ℝ) = pushDigit a (v : ℝ) := by
  simp [rationalPrefix, pushDigit, digit, base]

def rationalScale (m : ℕ) : Move → ℚ
  | .right => (2 * ((m : ℚ) + 1) + 1)⁻¹
  | .stay => 1
  | .left => 2 * ((m : ℚ) + 1) + 1

@[simp] theorem rationalScale_coe (m : ℕ) (d : Move) :
    (rationalScale m d : ℝ) = scale m d := by
  cases d <;> simp [rationalScale, scale, base]

theorem rationalScale_pos (m : ℕ) (d : Move) : 0 < rationalScale m d := by
  have h := scale_pos m d
  rw [← rationalScale_coe] at h
  exact_mod_cast h
end Radix
end Solenoidal

end OAI
