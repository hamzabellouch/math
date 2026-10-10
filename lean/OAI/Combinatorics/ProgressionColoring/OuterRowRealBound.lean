import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace OAI

/-!
# A real lower bound for integer row sizes

The natural-number row bound `m / 10 ≤ n` implies a real lower bound with
an absolute loss of one, suitable for the exponential incidence estimates.
-/

namespace QuantitativeVanDerWaerden

/-- Losing one converts the floored row-size bound to a strict real bound. -/
theorem real_div_ten_sub_one_lt {m n : ℕ} (h : m / 10 ≤ n) :
    (m : ℝ) / 10 - 1 < (n : ℝ) := by
  have hnat : m ≤ 10 * n + 9 := by omega
  have hreal : (m : ℝ) ≤ 10 * (n : ℝ) + 9 := by exact_mod_cast hnat
  linarith

/-- The real row-size lower bound used in weighted incidence sums. -/
theorem real_div_ten_sub_one_le {m n : ℕ} (h : m / 10 ≤ n) :
    (m : ℝ) / 10 - 1 ≤ (n : ℝ) :=
  (real_div_ten_sub_one_lt h).le

end QuantitativeVanDerWaerden

end OAI
