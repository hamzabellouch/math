import OAI.Analysis.FiniteFactor.CrossedProduct.PhaseCoverage
import OAI.Analysis.FiniteFactor.Coupling.BadEvents

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

theorem sourceStage_L_mono : Monotone (fun s => (sourceStage s).L) := by
  apply monotone_nat_of_le_succ
  intro s
  exact (sourceStage (s+1)).L_ge

theorem staged_rho_first (j s : ℕ) :
    (sourceBlockSize s : ℝ)*(stagedCouplingParameters j s).rho 0 =
      sourceKappa s*Real.sqrt (sourceStageState s).G := by
  have hm := sourceBlockSize_pos s
  have hG : 0 ≤ (sourceStageState s).G := zero_le_one.trans (sourceStageState s).G_ge
  change (sourceBlockSize s : ℝ)*(sourceKappa s*
    Real.sqrt (((sourceStageState s).G/(sourceBlockSize s : ℝ))/(sourceBlockSize s : ℝ))) = _
  rw [div_div, Real.sqrt_div hG, Real.sqrt_mul_self hm.le]
  field_simp

theorem staged_rho_second (j s : ℕ) :
    (sourceBlockSize s : ℝ)*(stagedCouplingParameters j s).rho 1 =
      sourceKappa s*(sourceBlockSize s : ℝ)^(1/40 : ℝ) := by
  have hm := sourceBlockSize_pos s
  change (sourceBlockSize s : ℝ)*(sourceKappa s*
    Real.sqrt (((sourceBlockSize s : ℝ)^(-19/20 : ℝ))/(sourceBlockSize s : ℝ))) = _
  rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg_one,
    ← Real.rpow_add hm, ← Real.rpow_mul hm.le]
  have he : ((-19/20 : ℝ)+(-1))*(1/2) = -39/40 := by ring
  rw [he]
  calc
    _ = sourceKappa s*((sourceBlockSize s : ℝ)^(1 : ℝ)*(sourceBlockSize s : ℝ)^(-39/40 : ℝ)) := by rw [Real.rpow_one]; ring
    _ = _ := by rw [← Real.rpow_add hm]; norm_num

/-- Both conditional crossing budgets now follow from the numerical source
construction. The tag location j does not affect these two mixture weights. -/
theorem staged_rho_budget (j s : ℕ) (hjs : j ≤ s) (w : Fin 2) (hw : w = 0 → j < s) :
    (sourceStage j).L ≤ (sourceBlockSize s : ℝ)*(stagedCouplingParameters j s).rho w := by
  fin_cases w
  · change (sourceStage j).L ≤ (sourceBlockSize s : ℝ)*(stagedCouplingParameters j s).rho 0
    obtain ⟨p,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show s ≠ 0 by have := hw rfl; omega)
    rw [staged_rho_first]
    have hh := (sourceStage p).next_budget
    exact (sourceStage_L_mono (by have := hw rfl; omega : j ≤ p)).trans hh
  · change (sourceStage j).L ≤ (sourceBlockSize s : ℝ)*(stagedCouplingParameters j s).rho 1
    rw [staged_rho_second]
    exact (sourceStage_L_mono hjs).trans (sourceStage s).current_budget

/-- The source coefficient L_j is bounded by the drop in each assigned block. -/
theorem staged_drop_budget (j s : ℕ) (hjs : j ≤ s) :
    (sourceStage j).L ≤ (sourceStage s).C :=
  (sourceStage_L_mono hjs).trans (le_max_left _ _)

end
end FiniteFactor

end OAI
