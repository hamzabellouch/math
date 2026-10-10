import Mathlib

namespace OAI

namespace Problem344

theorem div_lt_div_succ_iff_gap {a b : ℝ} {n : ℕ} (hn : 0 < n) :
    a / (n : ℝ) < b / ((n + 1 : ℕ) : ℝ) ↔
      a / (n : ℝ) < b - a := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1R : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  rw [div_lt_div_iff₀ hnR hn1R, div_lt_iff₀ hnR]
  push_cast
  constructor <;> intro h <;> nlinarith

theorem div_lt_div_succ_of_gap {a b t : ℝ} {n : ℕ} (hn : 0 < n)
    (hbound : a / (n : ℝ) ≤ t) (hgap : t < b - a) :
    a / (n : ℝ) < b / ((n + 1 : ℕ) : ℝ) :=
  (div_lt_div_succ_iff_gap hn).2 (lt_of_le_of_lt hbound hgap)

end Problem344

end OAI
