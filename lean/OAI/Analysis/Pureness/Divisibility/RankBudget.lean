import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace OAI
namespace CuntzPureness

theorem exists_sandwich_coefficient (n : ℕ) (hn : 1 ≤ n) :
    ∃ s : ℝ, 1 / ((n : ℝ) + 1) < s ∧ s < 1 / (n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hgap : 1 / ((n : ℝ) + 1) < 1 / (n : ℝ) := by
    exact one_div_lt_one_div_of_lt hn0 (by linarith)
  exact ⟨(1 / ((n : ℝ) + 1) + 1 / (n : ℝ)) / 2, by linarith, by linarith⟩

theorem finite_rank_sandwich (n : ℕ) (hn : 1 ≤ n)
    (r b m s E : ℝ) (hm : 0 < m) (hmr : m ≤ r)
    (hslo : 1 / ((n : ℝ) + 1) < s) (hshi : s < 1 / (n : ℝ))
    (hE : E < (s - 1 / ((n : ℝ) + 1)) * m)
    (hb : b ≤ s * r) (hr : s * r ≤ b + E) :
    (n : ℝ) * b < r ∧ r < ((n : ℝ) + 1) * b := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : 0 < (n : ℝ) + 1 := by linarith
  have hr0 : 0 < r := lt_of_lt_of_le hm hmr
  have hupper : s * (n : ℝ) < 1 := (lt_div_iff₀ hn0).mp hshi
  have hmargin : (s - 1 / ((n : ℝ) + 1)) * m ≤
      (s - 1 / ((n : ℝ) + 1)) * r :=
    mul_le_mul_of_nonneg_left hmr (le_of_lt (sub_pos.mpr hslo))
  have hinv : (1 / ((n : ℝ) + 1)) * ((n : ℝ) + 1) = 1 :=
    one_div_mul_cancel (ne_of_gt hn1)
  constructor
  · have h₁ := mul_le_mul_of_nonneg_left hb (le_of_lt hn0)
    have h₂ := mul_lt_mul_of_pos_right hupper hr0
    nlinarith
  · have h₁ : (1 / ((n : ℝ) + 1)) * r < b := by nlinarith
    have h₂ := mul_lt_mul_of_pos_left h₁ hn1
    nlinarith
end CuntzPureness

end OAI
