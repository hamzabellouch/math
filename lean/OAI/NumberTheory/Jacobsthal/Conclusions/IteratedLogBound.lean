import OAI.NumberTheory.Jacobsthal.Conclusions.IteratedLogBudget
import OAI.NumberTheory.Jacobsthal.Conclusions.IteratedLogFinite
import OAI.NumberTheory.Jacobsthal.Conclusions.JacobsthalFromRootLower
import OAI.NumberTheory.Jacobsthal.Conclusions.SourceRootCompletion

namespace OAI

namespace Erdos970.NumberTheoryLean.IteratedLogBound

open _root_.Filter IteratedLogScales JacobsthalTerminalScales
open StoppedCountVertex StoppedCountAdapters LogarithmicBinPartition
open RootCutoffSurvivors ProgressionSieve
open scoped Topology

/-- The strengthened main follows from the same precise survivor estimate as
the old quadratic main. No strengthened conclusion is assumed here. -/
theorem of_source_root_lower (c : ℝ) (hc : 0 < c)
    (z : ℝ → PrimeHistories.Node)
    (hLower : ∀ᶠ top : ℝ in atTop, ∀ a : ℕ → ℕ,
      c * ((ErdosInverseBoxHeight.sourceY top : ℝ) *
        SmallSieveFinite.smallEuler ⌊ErdosInverseBoxHeight.sourceW top⌋₊ /
        (ErdosInverseBoxHeight.sourceB top) ^ 2) ≤
      countSurvivors (ErdosInverseBoxHeight.sourceY top)
        (LargePrimeDeletion.cutoffPrimes ⌊ErdosInverseBoxHeight.sourceW top⌋₊) a
        (rootVertex (z top) ∅ (sourcePrimeSet (ErdosInverseBoxHeight.sourceW top) top)
          ((ErdosInverseBoxHeight.sourceY top : ℝ) *
            SmallSieveFinite.smallEuler ⌊ErdosInverseBoxHeight.sourceW top⌋₊))) :
    Targets.JacobsthalIteratedLog := by
  obtain ⟨A, hA, hbudget⟩ := IteratedLogBudget.separation c hc
  have hA0 : 0 < A := by linarith
  have hu := rescale_tendsto A hA
  have hData : ∀ᶠ k : ℝ in atTop,
      ∃ m : ℕ, (∀ k' : ℕ, (k' : ℝ) = k → Targets.IsJacobsthalBound k' m) ∧
        (m : ℝ) ≤ A ^ 2 * k ^ 2 / (loglog k) ^ 2 := by
    filter_upwards [hu.eventually eventual_terminal_numerics,
      hu.eventually JacobsthalFromRootLower.terminal_w_le_top,
      hbudget, (terminal_top_tendsto.comp hu).eventually hLower] with k hn hw hb hl
    refine ⟨terminalY (rescale A k), ?_, ?_⟩
    · intro k' hk'
      apply isJacobsthalBound_of_cutoff_lower _ _ k' hn.2.2.2.2.2.2.1
      · exact cutoff_lower_of_root_lower _ hw (z (terminalTop (rescale A k))) hl
      · simpa only [hk', Function.comp_def, terminalY] using hb
    · calc
        _ ≤ (rescale A k) ^ 2 := hn.2.2.2.2.2.1
        _ = A ^ 2 * k ^ 2 / (loglog k) ^ 2 := by
          simp only [rescale, div_pow, mul_pow]
  apply IteratedLogFinite.of_eventually
  refine ⟨A ^ 2, sq_pos_of_pos hA0, ?_⟩
  filter_upwards [(tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k : ℝ))
    atTop atTop).eventually hData] with k hk
  obtain ⟨m, hm, hb⟩ := hk
  exact ⟨m, hm k rfl, hb⟩

end Erdos970.NumberTheoryLean.IteratedLogBound

namespace Erdos970.Erdos970Final

/-- Manuscript 293, strengthened Theorem 1.1, revision ad16712e7b45. -/
theorem erdos_970_iterated_log : NumberTheoryLean.Targets.JacobsthalIteratedLog := by
  obtain ⟨c, hc, hLower⟩ := source_root_survivor_lower
  exact NumberTheoryLean.IteratedLogBound.of_source_root_lower c hc
    (ErdosCorrectionLimit.sourceRootNode (1 / 100)) hLower

end Erdos970.Erdos970Final

end OAI
