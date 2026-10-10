import OAI.NumberTheory.Jacobsthal.Conclusions.JacobsthalDeletionBudget
import OAI.NumberTheory.Jacobsthal.Estimates.CorrectionFloorRemainder

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.JacobsthalTerminalScales
open _root_.Filter Asymptotics JacobsthalSourceScale JacobsthalSourceRounding JacobsthalProgressionLength ProgressionSieve
open scoped Topology

noncomputable def terminalTop (x : ℝ) : ℝ := x*Real.log x
noncomputable def terminalY (x : ℝ) : ℕ := ErdosInverseBoxHeight.sourceY (terminalTop x)
noncomputable def terminalCutoff (x : ℝ) : ℕ := ⌊terminalTop x⌋₊

theorem eventual_terminal_logs : ∀ᶠ x : ℝ in atTop,
    4 ≤ x ∧ 2 ≤ Real.log x ∧ (Real.log x)^2 ≤ x ∧ 16*Real.log x ≤ Real.sqrt x ∧
      Real.log x ≤ Real.log (terminalTop x) ∧ Real.log (terminalTop x) ≤ 2*Real.log x := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop (1:ℝ) (s:=1/2) (by norm_num)).bound (by norm_num : (0:ℝ)<1/16)
  filter_upwards [eventually_ge_atTop (4:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop 2,
    log_square_le_sqrt_eventually,hsmall] with x hx hlog hs hsmall
  have hx0 : 0 < x := by linarith
  have hl0 : 0 < Real.log x := by linarith
  have hr : Real.sqrt x ≤ x := by nlinarith [Real.sq_sqrt hx0.le,Real.sqrt_nonneg x]
  have h16 : Real.log x ≤ (1/16:ℝ)*Real.sqrt x := by
    simpa only [Real.rpow_one,Real.norm_eq_abs,abs_of_nonneg hl0.le,
      ← Real.sqrt_eq_rpow,abs_of_nonneg (Real.sqrt_nonneg x)] using hsmall
  have hll0 := Real.log_nonneg (by linarith : 1 ≤ Real.log x)
  have hllu := Real.log_le_sub_one_of_pos hl0
  have he : Real.log (terminalTop x)=Real.log x+Real.log (Real.log x) :=
    Real.log_mul hx0.ne' hl0.ne'
  refine ⟨hx,hlog,hs.trans hr,by linarith,?_,?_⟩ <;> rw [he] <;> linarith

theorem terminal_top_tendsto : Tendsto terminalTop atTop atTop := by
  apply tendsto_atTop.mpr
  intro R
  filter_upwards [eventual_terminal_logs,eventually_ge_atTop R] with x hx hR
  unfold terminalTop
  nlinarith [hx.1,hx.2.1]

theorem eventual_terminal_numerics : ∀ᶠ x : ℝ in atTop,
    4 ≤ x ∧ 2 ≤ Real.log x ∧ (Real.log x)^2 ≤ x ∧ 1 < terminalTop x ∧
    x^2/8 ≤ (terminalY x:ℝ) ∧ (terminalY x:ℝ) ≤ x^2 ∧
    progressionLength (terminalY x) (terminalCutoff x) ≤ terminalCutoff x ∧
    (progressionLength (terminalY x) (terminalCutoff x):ℝ) ≤ 2*x/Real.log x ∧
    Real.log x/2 ≤ Real.log (progressionLength (terminalY x) (terminalCutoff x):ℝ) := by
  filter_upwards [eventual_terminal_logs] with x hx
  obtain ⟨hx,hlog,hs,h16,hlo,hhi⟩ := hx
  have hx0 : 0 < x := by linarith
  have hl0 : 0 < Real.log x := by linarith
  have htop : 2 ≤ terminalTop x := by unfold terminalTop; nlinarith
  have hY : x^2/8 ≤ (terminalY x:ℝ) ∧ (terminalY x:ℝ) ≤ x^2 := by
    simpa only [terminalY,ErdosInverseBoxHeight.sourceY,terminalTop] using floor_length_bounds hx hl0 hlo hhi
  have hZ := floor_cutoff_bounds htop
  have hT := source_progression_bounds hx hlog hs (terminalY x) (terminalCutoff x) hY.1 hY.2 hZ.1
    (by simpa only [terminalCutoff,terminalTop,mul_assoc] using hZ.2.2.2) hZ.2.2.1
  exact ⟨hx,hlog,hs,by linarith,hY.1,hY.2,hT.2.2,hT.2.1,
    progression_log_lower hx0 hl0 h16 _ _ hT.1⟩
end NumberTheoryLean.JacobsthalTerminalScales


end Erdos970

end OAI
