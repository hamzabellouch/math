import OAI.NumberTheory.Jacobsthal.Conclusions.JacobsthalBudgetSeparation
import OAI.NumberTheory.Jacobsthal.Conclusions.JacobsthalFinite
import OAI.NumberTheory.Jacobsthal.Estimates.RootCutoffSurvivors

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.JacobsthalFromRootLower
open _root_.Filter JacobsthalTerminalScales JacobsthalBudgetSeparation
open StoppedCountVertex StoppedCountAdapters LogarithmicBinPartition
open RootCutoffSurvivors ProgressionSieve
open scoped Topology

theorem terminal_w_le_top : ∀ᶠ x : ℝ in atTop,
    ErdosInverseBoxHeight.sourceW (terminalTop x) ≤ terminalTop x := by
  filter_upwards [(Real.tendsto_log_atTop.comp terminal_top_tendsto).eventually
    JacobsthalSourceScale.sourceW_bounds_eventually,terminal_top_tendsto.eventually_gt_atTop 1]
    with x hw ht
  have hW : ErdosInverseBoxHeight.sourceW (terminalTop x) ≤ Real.log (terminalTop x) := hw.2.2
  have hlog := Real.log_le_sub_one_of_pos (zero_lt_one.trans ht)
  linarith

theorem jacobsthal_of_source_root_lower (c : ℝ) (hc : 0 < c)
    (z : ℝ → PrimeHistories.Node)
    (hLower : ∀ᶠ top : ℝ in atTop,∀ a : ℕ → ℕ,
      c*((ErdosInverseBoxHeight.sourceY top:ℝ)*
        SmallSieveFinite.smallEuler ⌊ErdosInverseBoxHeight.sourceW top⌋₊/(ErdosInverseBoxHeight.sourceB top)^2) ≤
      countSurvivors (ErdosInverseBoxHeight.sourceY top)
        (LargePrimeDeletion.cutoffPrimes ⌊ErdosInverseBoxHeight.sourceW top⌋₊) a
        (rootVertex (z top) ∅ (sourcePrimeSet (ErdosInverseBoxHeight.sourceW top) top)
          ((ErdosInverseBoxHeight.sourceY top:ℝ)*SmallSieveFinite.smallEuler ⌊ErdosInverseBoxHeight.sourceW top⌋₊))) :
    Targets.JacobsthalQuadratic := by
  have hData : ∀ᶠ x : ℝ in atTop,
      (terminalY x:ℝ) ≤ x^2 ∧
      progressionLength (terminalY x) (terminalCutoff x) ≤ terminalCutoff x ∧
      ErdosInverseBoxHeight.sourceW (terminalTop x) ≤ terminalTop x ∧
      x*deletionBudget (terminalY x) (terminalCutoff x) <
        c*((terminalY x:ℝ)*SmallSieveFinite.smallEuler ⌊ErdosInverseBoxHeight.sourceW (terminalTop x)⌋₊/
          (ErdosInverseBoxHeight.sourceB (terminalTop x))^2) ∧
      ∀ a : ℕ → ℕ,c*((terminalY x:ℝ)*SmallSieveFinite.smallEuler ⌊ErdosInverseBoxHeight.sourceW (terminalTop x)⌋₊/
          (ErdosInverseBoxHeight.sourceB (terminalTop x))^2) ≤
        ((LargePrimeDeletion.cutoffSurvivors (terminalY x) (terminalCutoff x) a).card:ℝ) := by
    filter_upwards [eventual_terminal_numerics,terminal_w_le_top,terminal_budget_separation c hc,
      terminal_top_tendsto.eventually hLower] with x hn hw hb hl
    refine ⟨hn.2.2.2.2.2.1,hn.2.2.2.2.2.2.1,hw,hb,?_⟩
    exact cutoff_lower_of_root_lower (terminalY x) hw (z (terminalTop x)) hl
  have hNat : ∀ᶠ k : ℕ in atTop,
      ∃ m : ℕ,Targets.IsJacobsthalBound k m ∧ (m:ℝ) ≤ (1:ℝ)*(k:ℝ)^2 := by
    filter_upwards [(tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k:ℝ)) atTop atTop).eventually hData] with k hk
    refine ⟨terminalY (k:ℝ),?_,by simpa only [one_mul] using hk.1⟩
    exact isJacobsthalBound_of_cutoff_lower _ _ k hk.2.1 hk.2.2.2.2 hk.2.2.2.1
  obtain ⟨K,hK⟩ := eventually_atTop.mp hNat
  exact JacobsthalFinite.quadratic_of_eventually_quadratic ⟨1,by norm_num,K,fun k hk _hpos => hK k hk⟩
end NumberTheoryLean.JacobsthalFromRootLower


end Erdos970

end OAI
