import OAI.Analysis.Nonexpansive.TreeFrontier
import OAI.Analysis.Nonexpansive.PrefixPredictionOutputs
import OAI.Analysis.Nonexpansive.TreeBudget
import OAI.Analysis.Nonexpansive.TailMaps

namespace OAI

/-!
# Candidate records and their immutable preceding history

The detector set of a new record is computed from the entire preceding
list. This list includes records which will later receive coefficient zero.
No coefficient, retained child list, or future frontier occurs in that set.
-/

noncomputable section

open scoped BigOperators

namespace ReflexiveFixedPoints

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- A genuine generated selfmap, carrying the proof of its origin. -/
abbrev GeneratedSelfMap (D : NormalizedMinimalData (X := X)) :=
  {g : D.K → D.K // Generated D.closed D.convex D.T D.nonexpansive g}

/-- Data already fixed when construction of a new finite level starts. -/
structure CandidateContext (D : NormalizedMinimalData (X := X)) where
  frontier : TreeFrontier D.K
  frontier_generated : ∀ p, Generated D.closed D.convex D.T D.nonexpansive (frontier.map p)
  anchor : D.K
  terminal : ℕ → D.K
  ultrafilter : Ultrafilter ℕ
  depth : ℕ
  base : ℕ
  ancestors : Fin frontier.size → List (GeneratedSelfMap D)

/-- The auxiliary functional is chosen after this actual map has been
selected. The budget and detector set are derived from the record's prefix. -/
structure CandidateRecord {D : NormalizedMinimalData (X := X)}
    (C : CandidateContext D) where
  parent : Fin C.frontier.size
  map : D.K → D.K
  generated : Generated D.closed D.convex D.T D.nonexpansive map
  functional : X →L[ℝ] ℝ

namespace CandidateContext

variable {D : NormalizedMinimalData (X := X)} (C : CandidateContext D)

/-- The globally fresh zero-based label before a candidate is chosen. -/
def nextOrdinal (history : List (CandidateRecord C)) : ℕ := C.base + history.length

/-- The next budget is fixed by the full history, including discarded maps. -/
def nextBudget (history : List (CandidateRecord C)) : ℝ :=
  candidateBudget (C.nextOrdinal history)

theorem nextBudget_pos (history : List (CandidateRecord C)) :
    0 < C.nextBudget history := candidateBudget_pos _

/-- Earlier parent labels, read without changing their order. -/
def historyParent (history : List (CandidateRecord C))
    (i : Fin history.length) : Fin C.frontier.size := (history.get i).parent

/-- Earlier candidate outputs at the fixed anchor. -/
def historyPoint (history : List (CandidateRecord C))
    (i : Fin history.length) : D.K := (history.get i).map C.anchor

/-- The actual compact prediction detector, computed before the next map. -/
def detectorSet (history : List (CandidateRecord C)) : Set X :=
  Prediction.Prefix.detectorSet C.frontier.convex C.frontier.map C.frontier.evaluate
    (C.historyParent history) (C.historyPoint history) D.weak_compact C.terminal
    C.ultrafilter D.z C.depth

theorem detectorSet_nonempty (history : List (CandidateRecord C)) :
    (C.detectorSet history).Nonempty :=
  Prediction.Prefix.detectorSet_nonempty C.frontier.convex C.frontier.map
    C.frontier.evaluate (C.historyParent history) (C.historyPoint history)
    D.weak_compact C.terminal C.ultrafilter D.z C.depth

theorem detectorSet_subset (history : List (CandidateRecord C)) :
    C.detectorSet history ⊆ D.K :=
  Prediction.Prefix.detectorSet_subset C.frontier.convex C.frontier.map
    C.frontier.evaluate (C.historyParent history) (C.historyPoint history)
    D.weak_compact C.terminal C.ultrafilter D.z C.depth

theorem isCompact_detectorSet (history : List (CandidateRecord C)) :
    IsCompact (C.detectorSet history) :=
  Prediction.Prefix.isCompact_detectorSet C.frontier.convex C.frontier.map
    C.frontier.evaluate (C.historyParent history) (C.historyPoint history)
    C.frontier.nonexpansive
    (fun H H' ε h => C.frontier.evaluate_norm_sub_le_of_forall H H' (ε := ε) h)
    D.weak_compact D.norm_sub_le_one C.terminal C.ultrafilter D.z C.depth

/-- The actual maps on the fixed path to a parent. -/
def ancestorMap (p : Fin C.frontier.size)
    (i : Fin (C.ancestors p).length) : D.K → D.K := ((C.ancestors p).get i).val

theorem ancestorMap_generated (p : Fin C.frontier.size)
    (i : Fin (C.ancestors p).length) :
    Generated D.closed D.convex D.T D.nonexpansive (C.ancestorMap p i) :=
  ((C.ancestors p).get i).property

/-- Proper ancestors of a new child include its current parent map. -/
def candidateAncestors (p : Fin C.frontier.size) : List (GeneratedSelfMap D) :=
  C.ancestors p ++ [⟨C.frontier.map p, C.frontier_generated p⟩]

def candidateAncestorMap (p : Fin C.frontier.size)
    (i : Fin (C.candidateAncestors p).length) : D.K → D.K :=
  ((C.candidateAncestors p).get i).val

theorem candidateAncestorMap_generated (p : Fin C.frontier.size)
    (i : Fin (C.candidateAncestors p).length) :
    Generated D.closed D.convex D.T D.nonexpansive (C.candidateAncestorMap p i) :=
  ((C.candidateAncestors p).get i).property

/-- Legality is relative to the exact immutable preceding prefix. -/
def Legal (history : List (CandidateRecord C)) (r : CandidateRecord C) : Prop :=
  ‖r.functional‖ ≤ 1 ∧
  (∀ z ∈ C.detectorSet history,
    1 - C.nextBudget history ≤ r.functional ((r.map C.anchor : X) - z)) ∧
  (∑ i : Fin (C.candidateAncestors r.parent).length,
    ‖(C.candidateAncestorMap r.parent i (r.map C.anchor) : X) - (r.map C.anchor : X)‖) ≤
      C.nextBudget history

@[simp] theorem nextOrdinal_append (history : List (CandidateRecord C))
    (r : CandidateRecord C) :
    C.nextOrdinal (history ++ [r]) = C.nextOrdinal history + 1 := by
  simp [nextOrdinal, Nat.add_assoc]

theorem nextOrdinal_lt_append (history : List (CandidateRecord C))
    (r : CandidateRecord C) :
    C.nextOrdinal history < C.nextOrdinal (history ++ [r]) := by
  rw [C.nextOrdinal_append]
  exact Nat.lt_succ_self _

end CandidateContext
end ReflexiveFixedPoints

end

end OAI
