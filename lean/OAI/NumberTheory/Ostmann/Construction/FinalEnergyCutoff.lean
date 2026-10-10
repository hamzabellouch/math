import OAI.NumberTheory.Ostmann.Construction.ConstituentEnergyRate
import OAI.NumberTheory.Ostmann.Construction.CellRoleBudget

namespace OAI

/-! # The fixed epsilon leaves room for the actual final energy cost -/

namespace Ostmann
open Filter

/-- With the manuscript's gap `B + 20 log z`, even the direct finite-history
energy estimate is absorbed by the final factorial gain. All other costs are
fixed before the depth is selected. -/
theorem eventual_final_energy_margin (B F₀ H D B₁ : ℝ) :
    ∀ᶠ k : ℕ in atTop,
      (4 * ((B + 20 * Real.log (cellRoleScale k)) + F₀) -
        (B + 20 * Real.log (cellRoleScale k)) + H) + D + 2 * B₁ + 1 ≤
          (k : ℝ) * Real.log 2 - 1 := by
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  have hk := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop
    (4 * (3 * B + 4 * F₀ + H + D + 2 * B₁ + 2))
  filter_upwards [hk] with k hk
  have hn : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hlog hn
  rw [cellRoleScale, Real.log_exp]
  norm_num [cellRoleEpsilon]
  nlinarith

end Ostmann

end OAI
