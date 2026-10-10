import OAI.Analysis.Nonexpansive.CandidateLabels
import OAI.Analysis.Nonexpansive.CandidateTolerance

namespace OAI

/-!
# Exact tolerance for the actual recursively constructed tree

Every earlier retained candidate ordinal precedes the counter at the current
finite stage. Thus the conservative scale used by actual adaptive selection
is bounded by the precise retained-budget tolerance, which is the scale
exported by the tree construction.
-/

namespace ReflexiveFixedPoints
namespace AnchoredCandidateContext

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable (D : NormalizedMinimalData (X := X))
variable (A : AnchorPoint (tailFamily D.closed D.convex D.T D.nonexpansive))
variable (U : Ultrafilter ℕ)

/-- The actual requested return accuracy implies the exact scale. -/
theorem runTolerance_le_tolerance (k : ℕ) :
    (context D A U k).runTolerance ≤
      (tower D A U).toOrderedTree.tolerance
        (OrderedTree.retainedBudget (candidateLabel D A U)) k := by
  have h := (tower D A U).toOrderedTree.candidateScale_le_tolerance_of_lt
    (candidateLabel D A U) k (context D A U k).base
    (fun i hi v => candidateLabel_lt_base_of_lt D A U hi v)
  simpa only [CandidateContext.runTolerance, context_depth] using h

/-- Every actual parent has the required child-average estimate in the
original normalized norm, with the exact retained-budget tolerance. -/
theorem tower_child_average (k : ℕ)
    (p : (tower D A U).toOrderedTree.Node k) :
    ‖((tower D A U).toEvaluation.childAverage k
      (fun v => (tower D A U).toEvaluation.map (k + 1) v A.x) p : X) - (A.x : X)‖ ≤
      (tower D A U).toOrderedTree.tolerance
        (OrderedTree.retainedBudget (candidateLabel D A U)) k :=
  (tower_childAverage_near D A U k p).le.trans
    (runTolerance_le_tolerance D A U k)

end AnchoredCandidateContext
end ReflexiveFixedPoints

end OAI
