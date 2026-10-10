import OAI.Computability.PerfectCompleteness.Foundations.StoppedProjectedCoarseLemmas
import OAI.Computability.PerfectCompleteness.Reduction.FixedStoppedInverseBound
import OAI.Computability.PerfectCompleteness.Reduction.FixedStoppedUsefulMass
import OAI.Computability.PerfectCompleteness.Sampling.StoppedProjectedUsefulProbability

namespace OAI

section

namespace PerfectCompleteness.FixedStoppedActualBounds

noncomputable section

open scoped Classical
open RecursiveSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {δ : ℚ} {hδ : 0 < δ} (parameters : FixedParameters.Parameters δ hδ)
  (i j : Fin parameters.plan.depth) (hij : i < j) (input : List Bool)
  (strategy : FixedPreliminaryGame.Strategy parameters input)

theorem usefulMass_ge
    (hreserve : InitialParameters.simultaneous δ + 2 * parameters.accuracy ≤
      (StoppedSharedSampler.stoppedLaw
        (PCPSource.clauseFamily (BinaryLanguage.totalRename input))
        (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
        (Nat.succ_le_of_lt i.isLt) (fun k _ => FixedParameters.branch_pos parameters k)
        (fun k => FixedPreliminaryGame.rows_pos parameters (k + 1))).probability
          (StoppedSharedEvents.pair (PCPSource.clauseFamily (BinaryLanguage.totalRename input))
            strategy (Nat.succ_le_of_lt i.isLt)
            (fun k _ => FixedParameters.branch_pos parameters k) i j)) :
    InitialParameters.simultaneous δ / 2 ≤
      FixedStoppedInverseBound.usefulMass parameters i j hij input strategy := by
  have heq := StoppedProjectedUsefulProbability.usefulMass_eq_original
    (PCPSource.clauseFamily (BinaryLanguage.totalRename input))
    (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
    (Nat.succ_le_of_lt j.isLt) hij (FixedStoppedPhysicalLaw.designated parameters i)
    (fun k _ => FixedParameters.branch_pos parameters k)
    (StoppedProjectedMeetingLaw.rows_positive parameters.plan)
    (FixedStoppedDecoderLaw.flag parameters i)
    (FixedStoppedDecoderLaw.labeling parameters input strategy)
    (InitialParameters.useful δ) (FixedStoppedInverseBound.outerLaw parameters j input)
  change FixedStoppedInverseBound.usefulMass parameters i j hij input strategy =
    (FixedStoppedUsefulMass.originalLaw parameters i j hij input
      (FixedStoppedPhysicalLaw.designated parameters i) strategy).probability
        (HierarchicalUsefulFamily.usefulEvent
          (FixedStoppedUsefulMass.experiment parameters i j hij input
            (FixedStoppedPhysicalLaw.designated parameters i) strategy)
          (InitialParameters.useful δ)
          (FixedStoppedUsefulMass.upperEvent parameters i j hij input
            (FixedStoppedPhysicalLaw.designated parameters i) strategy)) at heq
  rw [heq]
  exact FixedStoppedUsefulMass.useful_probability_ge_of_reserve parameters i j hij input
    (FixedStoppedPhysicalLaw.designated parameters i) strategy hreserve

theorem coarseVariation_le_pairedVariation :
    FixedStoppedInverseBound.coarseVariation parameters i j hij input strategy ≤
      FixedStoppedInverseBound.pairedVariation parameters i j hij input strategy :=
  StoppedProjectedCoarse.totalVariation_le_pair
    (PCPSource.clauseFamily (BinaryLanguage.totalRename input))
    (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
    (Nat.succ_le_of_lt j.isLt) hij (FixedStoppedPhysicalLaw.designated parameters i)
    (fun k _ => FixedParameters.branch_pos parameters k)
    (StoppedProjectedMeetingLaw.rows_positive parameters.plan)
    (FixedStoppedDecoderLaw.flag parameters i)
    (FixedStoppedDecoderLaw.labeling parameters input strategy)
    (FixedStoppedInverseBound.outerLaw parameters j input)
    (FixedStoppedInverseBound.backgrounds parameters i j hij input strategy)
    parameters.plan.order

end
end PerfectCompleteness.FixedStoppedActualBounds

end

end OAI
