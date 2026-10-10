import OAI.Computability.PerfectCompleteness.Decoding.FixedProjectionErrorLemmas
import OAI.Computability.PerfectCompleteness.Foundations.SourcePhysicalSourceSwapLemmas
import OAI.Computability.PerfectCompleteness.Reduction.FixedCallBudgetLemmas

namespace OAI

section

namespace PerfectCompleteness.FixedPhysicalStoppedComparison

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces FixedParameters FixedRows
open UniqueGamesTheorem.Foundations.Games

variable {δ : ℚ} {hδ : 0 < δ} (params : Parameters δ hδ)
  {root h v m : Nat} (p : Path (branch params) root (h + 1))
  (outside : Slots (branch params) root → Fin (sourceLength params.plan hδ) → MixedSupport.Slot)
  (placeholder : Slots (branch params) (h + 1) → Fin (sourceLength params.plan hδ) → MixedSupport.Slot)
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch params h) → Slots (branch params) h)

theorem beta_nonneg : 0 ≤ (projectionProbability params h : ℝ) := by
  exact_mod_cast (projectionProbability_bounds params h).1.le

theorem beta_le_one : (projectionProbability params h : ℝ) ≤ 1 := by
  exact_mod_cast (projectionProbability_bounds params h).2.le

theorem calls_le (hroot : root ≤ params.plan.depth) :
    Fintype.card (WholeCutCalls.Index (rows params.plan) (repeats params.plan) p) ≤
      calls params.plan := by
  have hactual := FixedCallBudget.modified_calls_le (rows params.plan)
    (repeats params.plan) p hroot
  apply hactual.trans
  unfold calls
  omega

variable (source : FiniteDistribution
  (SourceChildKernel.Sources (m := m) (t := sourceLength params.plan hδ) designated))

abbrev modifiedLaw :=
  SourcePhysicalStoppedComparison.sourceModifiedLaw (rows params.plan) (repeats params.plan)
    p outside placeholder clauses designated source (projectionProbability params h : ℝ)
    (beta_nonneg params) (beta_le_one params)

abbrev stoppedLaw :=
  SourcePhysicalStoppedComparison.sourceStoppedLaw (rows params.plan) (repeats params.plan)
    p outside clauses designated source

theorem variation_lt_accuracy (hroot : root ≤ params.plan.depth) :
    (modifiedLaw params p outside placeholder clauses designated source).totalVariation
      (stoppedLaw params p outside clauses designated source) < params.accuracy := by
  have htv := SourcePhysicalStoppedComparison.source_variation
    (rows params.plan) (repeats params.plan) p outside placeholder clauses designated
    source (branch_pos params h) (projectionProbability params h : ℝ)
    (beta_nonneg params) (beta_le_one params)
  apply htv.trans_lt
  simpa only [SourceChildProjectionComparison.error] using
    FixedProjectionError.sparse_error_lt params (calls_le params p hroot) h

theorem probability_gt_sub_accuracy (hroot : root ≤ params.plan.depth)
    (event : SourcePhysicalStoppedComparison.Observation (rows params.plan) p outside clauses designated → Bool) :
    (stoppedLaw params p outside clauses designated source).probability event - params.accuracy <
      (modifiedLaw params p outside placeholder clauses designated source).probability event := by
  have htv := variation_lt_accuracy params p outside placeholder clauses designated source hroot
  have hp := FiniteDistribution.probability_le_add_totalVariation
    (stoppedLaw params p outside clauses designated source)
    (modifiedLaw params p outside placeholder clauses designated source) event
  rw [FiniteDistribution.totalVariation_comm] at hp
  linarith

theorem probability_gt_of_reserve (hroot : root ≤ params.plan.depth)
    (event : SourcePhysicalStoppedComparison.Observation (rows params.plan) p outside clauses designated → Bool)
    (c : ℝ)
    (hreserve : c + params.accuracy ≤
      (stoppedLaw params p outside clauses designated source).probability event) :
    c < (modifiedLaw params p outside placeholder clauses designated source).probability event := by
  have h := probability_gt_sub_accuracy params p outside placeholder clauses designated source hroot event
  linarith

end
end PerfectCompleteness.FixedPhysicalStoppedComparison

end

end OAI
