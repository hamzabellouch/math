import OAI.Analysis.Nonexpansive.CandidatePredictions
import OAI.Analysis.Nonexpansive.CandidateDetectors
import OAI.Analysis.Nonexpansive.CandidateTreeTolerance
import OAI.Analysis.Nonexpansive.SwitchingTreeData

namespace OAI

/-!
# The actual adaptive ordered tree

The anchor is produced by the resolvent-tail construction. A fixed ultrafilter
refines the ordinary tail filter. Concrete finite candidate selections then
construct each level, keeping every discarded candidate in its history. The
finite-frontier recursion produces the final tree and all its detector,
weight, return, path, and ideal-prediction conclusions.
-/

noncomputable section

open Filter

namespace ReflexiveFixedPoints

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- Assemble the proved conclusions of the actual finite-stage recursion. -/
def switchingTreeDataOfAnchor
    (D : NormalizedMinimalData (X := X))
    (A : AnchorPoint (tailFamily D.closed D.convex D.T D.nonexpansive))
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) : SwitchingTreeData D where
  tree := (AnchoredCandidateContext.tower D A U).toOrderedTree
  weights := (AnchoredCandidateContext.tower D A U).toWeightedTree
  evaluation := (AnchoredCandidateContext.tower D A U).toEvaluation
  anchor := A.x
  label := AnchoredCandidateContext.candidateLabel D A U
  label_injective := AnchoredCandidateContext.candidateLabel_injective D A U
  generated := AnchoredCandidateContext.tower_generated D A U
  root_map := (AnchoredCandidateContext.tower D A U).toEvaluation_map_zero _
  functional := AnchoredCandidateContext.candidateFunctional D A U
  functional_norm := AnchoredCandidateContext.candidateFunctional_norm D A U
  child_average := AnchoredCandidateContext.tower_child_average D A U
  path_displacement := AnchoredCandidateContext.candidate_path_displacement D A U
  ultrafilter := U
  ultrafilter_le_atTop := hU
  predictionLimit := AnchoredCandidateContext.candidatePredictionLimit D A U
  prediction_tendsto := AnchoredCandidateContext.candidatePredictionLimit_tendsto D A U
  prediction_detector := fun k v =>
    AnchoredCandidateContext.candidateFunctional_detector D A U k v
      (AnchoredCandidateContext.candidatePredictionLimit D A U k v : X)
      (AnchoredCandidateContext.candidatePredictionLimit_mem_detectorSet D A U k v)
  dense_detector := AnchoredCandidateContext.candidateFunctional_dense_detector D A U

/-- The tree, its anchor and all central construction laws are produced
from the actual normalized minimal invariant set. -/
theorem exists_switchingTreeData (D : NormalizedMinimalData (X := X)) :
    Nonempty (SwitchingTreeData D) := by
  let A := resolventAnchorPoint D.nonempty D.closed D.convex D.T
    D.nonexpansive D.weak_compact
  let U := Ultrafilter.of (Filter.atTop : Filter ℕ)
  exact ⟨switchingTreeDataOfAnchor D A U (Ultrafilter.of_le (Filter.atTop : Filter ℕ))⟩

end ReflexiveFixedPoints

end

end OAI
