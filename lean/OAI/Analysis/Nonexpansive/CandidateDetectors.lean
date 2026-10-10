import OAI.Analysis.Nonexpansive.CandidateLedgerJoin
import OAI.Analysis.Nonexpansive.CandidateAncestors

namespace OAI

/-!
# The actual retained functionals and their detector estimates

The functionals come from the legal candidate records. Their original
prefix budgets equal the global retained labels' budgets. The stored
proper-ancestor list is the actual final tree path, so the same record
also supplies the required path-displacement estimate.
-/

noncomputable section

namespace ReflexiveFixedPoints.AnchoredCandidateContext

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable (D : NormalizedMinimalData (X := X))
variable (A : AnchorPoint (tailFamily D.closed D.convex D.T D.nonexpansive))
variable (U : Ultrafilter ℕ)

/-- The budget fixed before selection is the retained node's original budget. -/
theorem candidatePrefix_nextBudget (k : ℕ)
    (v : (tower D A U).toOrderedTree.Node (k + 1)) :
    (context D A U k).nextBudget (candidatePrefix D A U k v) =
      OrderedTree.retainedBudget (candidateLabel D A U) ⟨k, v⟩ := by
  rw [CandidateContext.nextBudget, CandidateContext.nextOrdinal, candidatePrefix_length]
  rfl

/-- The actual chosen detector has dual norm at most one. -/
theorem candidateFunctional_norm (k : ℕ)
    (v : (tower D A U).toOrderedTree.Node (k + 1)) :
    ‖candidateFunctional D A U k v‖ ≤ 1 :=
  (candidatePrefix_legal D A U k v).1

/-- The original record separates its output from every point of its
actual compact prediction detector set. -/
theorem candidateFunctional_detector (k : ℕ)
    (v : (tower D A U).toOrderedTree.Node (k + 1)) (z : X)
    (hz : z ∈ (context D A U k).detectorSet (candidatePrefix D A U k v)) :
    1 - OrderedTree.retainedBudget (candidateLabel D A U) ⟨k, v⟩ ≤
      candidateFunctional D A U k v
        (((tower D A U).toEvaluation.map (k + 1) v A.x : X) - z) := by
  have h := (candidatePrefix_legal D A U k v).2.1 z hz
  change 1 - OrderedTree.retainedBudget (candidateLabel D A U) ⟨k, v⟩ ≤
    ((candidateLedger D A U k).retainedPoint v).functional
      (((tower D A U).toEvaluation.map (k + 1) v A.x : X) - z)
  simpa only [candidatePrefix_nextBudget, candidateLedger_retainedPoint_map,
    context_anchor] using h

/-- Every prescribed dense test point at this depth lies in the detector. -/
theorem candidateFunctional_dense_detector (k : ℕ)
    (v : (tower D A U).toOrderedTree.Node (k + 1)) (i : ℕ) (hi : i < k + 1) :
    1 - OrderedTree.retainedBudget (candidateLabel D A U) ⟨k, v⟩ ≤
      candidateFunctional D A U k v
        (((tower D A U).toEvaluation.map (k + 1) v A.x : X) - D.z i) := by
  apply candidateFunctional_detector D A U k v (D.z i : X)
  have hi' : i < (context D A U k).depth := by
    simpa only [context_depth] using hi
  exact Prediction.Prefix.mem_detectorSet_prefix
    (context D A U k).frontier.convex (context D A U k).frontier.map
    (context D A U k).frontier.evaluate
    ((context D A U k).historyParent (candidatePrefix D A U k v))
    ((context D A U k).historyPoint (candidatePrefix D A U k v))
    D.weak_compact (context D A U k).terminal (context D A U k).ultrafilter
    D.z (context D A U k).depth ⟨i, hi'⟩

/-- The actual record's ancestor budget controls the final tree's path sum. -/
theorem candidate_path_displacement (k : ℕ)
    (v : (tower D A U).toOrderedTree.Node (k + 1)) :
    (tower D A U).toEvaluation.pathDisplacement (k + 1) v
        ((tower D A U).toEvaluation.map (k + 1) v A.x) ≤
      OrderedTree.retainedBudget (candidateLabel D A U) ⟨k, v⟩ := by
  have h := (candidatePrefix_legal D A U k v).2.2
  rw [candidateLedger_retainedPoint_parent,
    candidateAncestorMap_sum_eq_pathDisplacement,
    candidateLedger_retainedPoint_map, context_anchor, candidatePrefix_nextBudget] at h
  exact h

end ReflexiveFixedPoints.AnchoredCandidateContext

end

end OAI
