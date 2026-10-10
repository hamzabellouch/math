import OAI.NumberTheory.Ostmann.Construction.CellRoleBudget

namespace OAI

/-! # One fixed depth meets the role-count and final entropy budgets -/

namespace Ostmann

theorem cellRoleEpsilon_margin : 0 < Real.log 2 - 60 * cellRoleEpsilon := by
  have hh := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num [cellRoleEpsilon] at hh ⊢
  linarith

theorem log_cellRoleScale (k : ℕ) :
    Real.log (cellRoleScale k) = 3 * cellRoleEpsilon * k := by
  rw [cellRoleScale, Real.log_exp]

/-- The threshold can be chosen before the late-block density increment.
Every resulting depth above it meets both budgets with the same constants. -/
theorem character_depth_cutoff (C R b : ℝ) (hb : 0 < b) (Kmin : ℕ) :
    ∃ K : ℕ, Kmin ≤ K ∧ ∀ k : ℕ, K ≤ k →
      1 ≤ k ∧ 1 ≤ cellRoleScale k ∧
        C + 20 * Real.log (cellRoleScale k) ≤ (k : ℝ) * Real.log 2 - 1 ∧
        cellRoleCountBound R k ≤ b * cellRoleScale k := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((C + 1) / (Real.log 2 - 60 * cellRoleEpsilon))
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.mp (eventually_cellRoleCountBound_le R b hb)
  let K := max Kmin (max 1 (max N J))
  refine ⟨K, by omega, fun k hk => ?_⟩
  have hNk : (N : ℝ) ≤ k := by exact_mod_cast (show N ≤ k by omega)
  have hC : C + 1 < (N : ℝ) * (Real.log 2 - 60 * cellRoleEpsilon) :=
    (div_lt_iff₀ cellRoleEpsilon_margin).mp hN
  have hscale : 1 ≤ cellRoleScale k := by
    unfold cellRoleScale
    apply Real.one_le_exp_iff.mpr
    unfold cellRoleEpsilon
    positivity
  refine ⟨by omega, hscale, ?_, hJ k (by omega)⟩
  rw [log_cellRoleScale]
  have hm := mul_le_mul_of_nonneg_right hNk cellRoleEpsilon_margin.le
  nlinarith

end Ostmann

end OAI
