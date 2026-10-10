import Mathlib
import OAI.Analysis.PrefixRadix.Codes

namespace OAI

/-! The concrete separated odd-digit radix system. -/

noncomputable section
open scoped ContDiff
namespace PrefixFlows
namespace Radix
def oddDigits (K : ℕ) : System (Fin K) where
  base := 2 * (K : ℝ) + 2
  base_ge_two := by linarith [Nat.cast_nonneg (α := ℝ) K]
  digit := fun a => 2 * (a.val : ℝ) + 1
  digit_nonneg := by intro a; positivity
  digit_le := by
    intro a
    have ha : (a.val : ℝ) + 1 ≤ (K : ℝ) := by exact_mod_cast Nat.succ_le_of_lt a.isLt
    linarith
  digit_gap := by
    intro a b hab
    have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
    rcases lt_or_gt_of_ne hne with h | h
    · have hh : (a.val : ℝ) + 1 ≤ (b.val : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hh : (b.val : ℝ) + 1 ≤ (a.val : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
      rw [abs_of_nonneg (by linarith)]
      linarith
end Radix
end PrefixFlows
end

end OAI
