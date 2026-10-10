import OAI.Combinatorics.ExpectationThreshold.SelectorDefinitions

namespace OAI

/-! Elementary bounds on the literal truncation scales. -/

namespace TalagrandThreshold.Selector

theorem dscale_pos {s : ℕ} (i : Fin s) : 0 < dscale i := by
  exact inv_pos.mpr (pow_pos (by norm_num : (0 : ℝ) < 2) _)

theorem dscale_nonneg {s : ℕ} (i : Fin s) : 0 ≤ dscale i :=
  (dscale_pos i).le

theorem dscale_lt_one {s : ℕ} (i : Fin s) : dscale i < 1 := by
  exact inv_lt_one_of_one_lt₀
    (one_lt_pow₀ (by norm_num : (1 : ℝ) < 2) (Nat.succ_ne_zero i.val))

end TalagrandThreshold.Selector

end OAI
