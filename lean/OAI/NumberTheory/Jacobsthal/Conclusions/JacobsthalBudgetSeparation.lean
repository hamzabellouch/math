import OAI.NumberTheory.Jacobsthal.Conclusions.JacobsthalSurvivorScale
import OAI.NumberTheory.Jacobsthal.Conclusions.JacobsthalTerminalScales
import OAI.NumberTheory.Jacobsthal.Sieve.ClosedEulerIndividualUpper

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.JacobsthalBudgetSeparation
open _root_.Filter JacobsthalTerminalScales JacobsthalSurvivorScale JacobsthalDeletionBudget ProgressionSieve
open scoped Topology

theorem terminal_w_tendsto : Tendsto (fun x : ℝ => ErdosInverseBoxHeight.sourceW (terminalTop x)) atTop atTop :=
  (JacobsthalSourceScale.sourceW_tendsto.comp Real.tendsto_log_atTop).comp terminal_top_tendsto

theorem terminal_budget_separation (c : ℝ) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop,
      x*deletionBudget (terminalY x) (terminalCutoff x) <
        c*((terminalY x:ℝ)*SmallSieveFinite.smallEuler ⌊ErdosInverseBoxHeight.sourceW (terminalTop x)⌋₊/
          (ErdosInverseBoxHeight.sourceB (terminalTop x))^2) := by
  let c0 : ℝ := Real.exp (-Real.eulerMascheroniConstant)/2
  have hc0 : 0 < c0 := by dsimp [c0]; positivity
  have hWT := terminal_w_tendsto
  have hLog := Real.tendsto_log_atTop.comp hWT
  filter_upwards [eventual_terminal_numerics,eventual_terminal_logs,
    hWT.eventually ErdosInverseEuler.smallEuler_log_bounds,
    hLog.eventually_gt_atTop ((1276*32)/(c*c0))] with x hn hl he hloglarge
  obtain ⟨hx,hlog,hlogs,hTop,hYlo,_hYhi,_hTcut,hT,hTL⟩ := hn
  have hx0 : 0 < x := by linarith
  have hl0 : 0 < Real.log x := by linarith
  have hw : 1 < ErdosInverseBoxHeight.sourceW (terminalTop x) := by linarith [he.1]
  have hV : c0/Real.log (ErdosInverseBoxHeight.sourceW (terminalTop x)) ≤
      SmallSieveFinite.smallEuler ⌊ErdosInverseBoxHeight.sourceW (terminalTop x)⌋₊ := by
    convert he.2.2.1 using 1
    dsimp [c0]
    ring
  have hscale := normalized_scale_lower hx0 hl0 hl.2.2.2.2.1 hl.2.2.2.2.2 hw hc0 hYlo hV
  have hsep : 1275 < c*c0*Real.log (ErdosInverseBoxHeight.sourceW (terminalTop x))/32 := by
    have hh := (div_lt_iff₀ (mul_pos hc hc0)).mp hloglarge
    dsimp only [Function.comp_def] at hh
    nlinarith
  have hden : 0 < x^2/(Real.log x)^2 := div_pos (sq_pos_of_pos hx0) (sq_pos_of_pos hl0)
  have hbudget := source_deletion_budget hx0 hl0 hlogs (terminalY x) (terminalCutoff x) hT hTL
  calc
    _ ≤ 1275*x^2/(Real.log x)^2 := hbudget
    _ = 1275*(x^2/(Real.log x)^2) := by ring
    _ < (c*c0*Real.log (ErdosInverseBoxHeight.sourceW (terminalTop x))/32)*(x^2/(Real.log x)^2) :=
      mul_lt_mul_of_pos_right hsep hden
    _ = c*(c0*x^2*Real.log (ErdosInverseBoxHeight.sourceW (terminalTop x))/(32*(Real.log x)^2)) := by ring
    _ ≤ c*((terminalY x:ℝ)*SmallSieveFinite.smallEuler ⌊ErdosInverseBoxHeight.sourceW (terminalTop x)⌋₊/
        (Real.log (terminalTop x)/Real.log (ErdosInverseBoxHeight.sourceW (terminalTop x)))^2) :=
      mul_le_mul_of_nonneg_left hscale hc.le
    _ = _ := rfl
end NumberTheoryLean.JacobsthalBudgetSeparation


end Erdos970

end OAI
