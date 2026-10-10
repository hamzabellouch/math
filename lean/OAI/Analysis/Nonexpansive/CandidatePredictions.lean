import OAI.Analysis.Nonexpansive.CandidateLedgerJoin
import OAI.Analysis.Nonexpansive.PrefixPredictionReindex
import OAI.Analysis.Nonexpansive.LedgerPredictionLimits

namespace OAI

/-!
# Final ideal predictions are members of their pre-map detector families

The coefficient parameter is obtained from the completed retained weights.
Reindexing identifies its earlier ledger with the literal candidate prefix.
Finite-frontier evaluation agrees with the final tree evaluation. Thus the
chosen prediction is one of the limits for which the detector was selected
before the current candidate map and before any current-level weights.
-/

noncomputable section

open Filter
open scoped Topology

namespace ReflexiveFixedPoints.AnchoredCandidateContext

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable (D : NormalizedMinimalData (X := X))
variable (A : AnchorPoint (tailFamily D.closed D.convex D.T D.nonexpansive))
variable (U : Ultrafilter ℕ)

/-- The final retained parameter transported to the exact pre-map prefix. -/
def candidatePrefixParameter (k : ℕ)
    (v : (tower D A U).toOrderedTree.Node (k + 1)) :
    Prediction.coefficientSet
      ((context D A U k).historyParent (candidatePrefix D A U k v)) :=
  Prediction.Prefix.pullCoeff (candidatePrefixIndex D A U k v)
    (fun i => (candidatePrefix_parent D A U k v i).symm)
    ((candidatePointLedger D A U k).actualParameter (tower D A U).toWeightedTree v)

/-- This is a member of the prediction family fixed before the map at `v`. -/
def candidatePrefixPrediction (k : ℕ)
    (v : (tower D A U).toOrderedTree.Node (k + 1)) : D.K :=
  Prediction.Prefix.predictionWeakLimit
    (context D A U k).frontier.convex
    (context D A U k).frontier.map (context D A U k).frontier.evaluate
    ((context D A U k).historyParent (candidatePrefix D A U k v))
    ((context D A U k).historyPoint (candidatePrefix D A U k v))
    D.weak_compact (context D A U k).terminal (context D A U k).ultrafilter
    (candidatePrefixParameter D A U k v)

/-- The same point expressed through the final actual ideal-cutoff evaluator. -/
def candidatePredictionLimit (k : ℕ)
    (v : (tower D A U).toOrderedTree.Node (k + 1)) : D.K :=
  (candidatePointLedger D A U k).predictionLimit (tower D A U).toEvaluation
    D.weak_compact (terminalSequence D.closed D.convex D.T D.nonexpansive A.x) U v

/-- Both descriptions choose the limit of literally the same evaluated sequence. -/
theorem candidatePrefixPrediction_eq (k : ℕ)
    (v : (tower D A U).toOrderedTree.Node (k + 1)) :
    candidatePrefixPrediction D A U k v = candidatePredictionLimit D A U k v := by
  let C := context D A U k
  let L := candidatePointLedger D A U k
  let θ := L.actualParameter (tower D A U).toWeightedTree v
  have hreindex := Prediction.Prefix.predictionWeakLimit_pullCoeff
    C.frontier.convex C.frontier.map C.frontier.evaluate
    (candidatePrefixIndex D A U k v)
    (fun i => (candidatePrefix_parent D A U k v i).symm)
    (C.historyPoint (candidatePrefix D A U k v)) (L.earlierPoint v)
    (fun i => (candidatePrefix_point D A U k v i).symm)
    D.weak_compact C.terminal C.ultrafilter θ
  have hevaluate := Prediction.Prefix.predictionWeakLimit_congr_evaluate
    C.frontier.convex C.frontier.map C.frontier.evaluate
    (L.earlierParent v) (L.earlierPoint v)
    (fun H => (tower D A U).evaluate_agreement k H)
    D.weak_compact C.terminal C.ultrafilter θ
  calc
    candidatePrefixPrediction D A U k v =
        Prediction.Prefix.predictionWeakLimit C.frontier.convex C.frontier.map
          C.frontier.evaluate (L.earlierParent v) (L.earlierPoint v)
          D.weak_compact C.terminal C.ultrafilter θ := hreindex
    _ = Prediction.Prefix.predictionWeakLimit C.frontier.convex C.frontier.map
        ((tower D A U).toEvaluation.evaluate k) (L.earlierParent v) (L.earlierPoint v)
        D.weak_compact C.terminal C.ultrafilter θ := hevaluate
    _ = candidatePredictionLimit D A U k v := by
      change Prediction.Prefix.predictionWeakLimit C.frontier.convex C.frontier.map
          ((tower D A U).toEvaluation.evaluate k) (L.earlierParent v) (L.earlierPoint v)
          D.weak_compact (context D A U k).terminal
          (context D A U k).ultrafilter θ = _
      rw [context_terminal, context_ultrafilter]
      rfl

/-- The actual final prediction belongs to the compact set fixed before `v`. -/
theorem candidatePredictionLimit_mem_detectorSet (k : ℕ)
    (v : (tower D A U).toOrderedTree.Node (k + 1)) :
    (candidatePredictionLimit D A U k v : X) ∈
      (context D A U k).detectorSet (candidatePrefix D A U k v) := by
  have h := Prediction.Prefix.mem_detectorSet_predictionWeakLimit
    (context D A U k).frontier.convex
    (context D A U k).frontier.map (context D A U k).frontier.evaluate
    ((context D A U k).historyParent (candidatePrefix D A U k v))
    ((context D A U k).historyPoint (candidatePrefix D A U k v))
    D.weak_compact (context D A U k).terminal (context D A U k).ultrafilter
    D.z (context D A U k).depth (candidatePrefixParameter D A U k v)
  change (candidatePrefixPrediction D A U k v : X) ∈
    (context D A U k).detectorSet (candidatePrefix D A U k v) at h
  rwa [candidatePrefixPrediction_eq] at h

/-- The resulting point is an actual weak limit of the final ideal cutoffs. -/
theorem candidatePredictionLimit_tendsto (k : ℕ)
    (v : (tower D A U).toOrderedTree.Node (k + 1)) :
    Tendsto (fun j => toWeakSpace ℝ X
      ((tower D A U).toEvaluation.evaluate (k + 1)
        ((tower D A U).toEvaluation.idealCutoff (k + 1) A.x
          (terminalSequence D.closed D.convex D.T D.nonexpansive A.x j) v) : X))
      (U : Filter ℕ)
      (𝓝 (toWeakSpace ℝ X (candidatePredictionLimit D A U k v : X))) :=
  (candidatePointLedger D A U k).tendsto_predictionLimit_idealCutoff
    (tower D A U).toEvaluation D.weak_compact
    (terminalSequence D.closed D.convex D.T D.nonexpansive A.x) U A.x
    (candidatePointLedger_retainedPoint D A U k) v

end ReflexiveFixedPoints.AnchoredCandidateContext

end

end OAI
