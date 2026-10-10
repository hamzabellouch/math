import OAI.Computability.PerfectCompleteness.Reduction.FixedStoppedActualBounds
import OAI.Computability.PerfectCompleteness.Reduction.FixedStoppedMeetingEquality
import OAI.Computability.PerfectCompleteness.Sampling.FixedSourcePairVariation

namespace OAI

section

namespace PerfectCompleteness.FixedStoppedUpperProbability

noncomputable section

attribute [local instance] FixedStoppedDecoderLaw.sampleFintype
  UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype

variable {δ : ℚ} {hδ : 0 < δ} (parameters : FixedParameters.Parameters δ hδ)
  (i j : Fin parameters.plan.depth) (hij : i < j) (input : List Bool)
  (strategy : FixedPreliminaryGame.Strategy parameters input)

theorem pairedVariation_le :
    FixedStoppedInverseBound.pairedVariation parameters i j hij input strategy ≤
      10 * parameters.accuracy :=
  FixedSourcePairVariation.totalVariation_le_ten parameters
    (PCPSource.clauseFamily (BinaryLanguage.totalRename input))
    (Nat.succ_le_of_lt j.isLt) hij (FixedStoppedPhysicalLaw.designated parameters i)
    (FixedStoppedDecoderLaw.labeling parameters input strategy) (le_refl _)
    (FixedStoppedInverseBound.outerLaw parameters j input)

theorem meeting_ge_gamma
    (hreserve : InitialParameters.simultaneous δ + 2 * parameters.accuracy ≤
      (StoppedSharedSampler.stoppedLaw
        (PCPSource.clauseFamily (BinaryLanguage.totalRename input))
        (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
        (Nat.succ_le_of_lt i.isLt) (fun k _ => FixedParameters.branch_pos parameters k)
        (fun k => FixedPreliminaryGame.rows_pos parameters (k + 1))).probability
          (StoppedSharedEvents.pair (PCPSource.clauseFamily (BinaryLanguage.totalRename input))
            strategy (Nat.succ_le_of_lt i.isLt)
            (fun k _ => FixedParameters.branch_pos parameters k) i j)) :
    FixedRankContradiction.gamma parameters (j.val + 1) ≤
      (FixedStoppedDecoderLaw.law parameters i j hij input strategy).probability
        (FixedStoppedDecoderLaw.meeting parameters i j hij input) := by
  have hpaired := pairedVariation_le parameters i j hij input strategy
  have hmass := FixedStoppedActualBounds.usefulMass_ge parameters i j hij input strategy hreserve
  have hcoarse :=
    (FixedStoppedActualBounds.coarseVariation_le_pairedVariation parameters i j hij input strategy).trans
      hpaired
  have hupper := FixedStoppedInverseBound.expectedMeeting_ge_gamma
    parameters i j hij input strategy hmass hpaired hcoarse
  exact hupper.trans_eq
    (FixedStoppedMeetingEquality.meeting_probability_eq_expectedMeeting
      parameters i j hij input strategy).symm

end
end PerfectCompleteness.FixedStoppedUpperProbability

end

end OAI
