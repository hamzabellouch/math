import OAI.Analysis.Nonexpansive.Basic
import OAI.Analysis.Nonexpansive.BlockEstimates
import OAI.Analysis.Nonexpansive.TerminalSequence
import OAI.Analysis.Nonexpansive.TreeBudget
import OAI.Analysis.Nonexpansive.TreeTolerance
import Mathlib.Order.Filter.Ultrafilter.Defs

namespace OAI

/-!
# The concrete tree-construction output consumed by switching

This record states the conclusions of the adaptive ordered-tree producer.
Its candidate labels are the original global selection ordinals. Predictions
are the actual evaluations of the ideal cutoff; the producer derives their
weak limits and detectors from its full earlier-candidate families, with all
discarded candidates retained. No field below is an additional hypothesis of
the public original-norm fixed-point theorem.
-/

noncomputable section

open Filter
open scoped Topology BigOperators

namespace ReflexiveFixedPoints

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

structure SwitchingTreeData (D : NormalizedMinimalData (X := X)) where
  tree : OrderedTree
  weights : WeightedTree tree
  evaluation : TreeEvaluation weights D.K
  anchor : D.K
  label : tree.NonrootNode → ℕ
  label_injective : Function.Injective label
  generated : ∀ k v, Generated D.closed D.convex D.T D.nonexpansive
    (evaluation.map k v)
  root_map : evaluation.map 0 tree.root = id
  functional : (k : ℕ) → tree.Node (k + 1) → X →L[ℝ] ℝ
  functional_norm : ∀ k v, ‖functional k v‖ ≤ 1
  child_average : ∀ k p,
    ‖(evaluation.childAverage k (fun c => evaluation.map (k + 1) c anchor) p : X) -
      anchor‖ ≤ tree.tolerance (OrderedTree.retainedBudget label) k
  path_displacement : ∀ k v,
    evaluation.pathDisplacement (k + 1) v (evaluation.map (k + 1) v anchor) ≤
      OrderedTree.retainedBudget label ⟨k, v⟩
  ultrafilter : Ultrafilter ℕ
  ultrafilter_le_atTop : (ultrafilter : Filter ℕ) ≤ atTop
  predictionLimit : (k : ℕ) → tree.Node (k + 1) → D.K
  prediction_tendsto : ∀ k v, Tendsto
    (fun j => toWeakSpace ℝ X
      (evaluation.evaluate (k + 1)
        (evaluation.idealCutoff (k + 1) anchor
          (terminalSequence D.closed D.convex D.T D.nonexpansive anchor j) v)))
    (ultrafilter : Filter ℕ) (𝓝 (toWeakSpace ℝ X (predictionLimit k v)))
  prediction_detector : ∀ k v,
    1 - OrderedTree.retainedBudget label ⟨k, v⟩ ≤
      functional k v ((evaluation.map (k + 1) v anchor : X) - predictionLimit k v)
  dense_detector : ∀ k v i, i < k + 1 →
    1 - OrderedTree.retainedBudget label ⟨k, v⟩ ≤
      functional k v ((evaluation.map (k + 1) v anchor : X) - D.z i)

namespace SwitchingTreeData

variable {D : NormalizedMinimalData (X := X)} (A : SwitchingTreeData D)

/-- Extend the nonroot budget by zero at the root, which has no detector. -/
def budget : (k : ℕ) → A.tree.Node k → ℝ
  | 0, _ => 0
  | k + 1, v => OrderedTree.retainedBudget A.label ⟨k, v⟩

/-- Extend the actual nonroot functionals by the zero functional at the root. -/
def functionalAt : (k : ℕ) → A.tree.Node k → X →L[ℝ] ℝ
  | 0, _ => 0
  | k + 1, v => A.functional k v

/-- The actual anchor images labelling every node of the tree. -/
def nodeLabel (k : ℕ) (v : A.tree.Node k) : D.K :=
  A.evaluation.map k v A.anchor

/-- The single actual terminal sequence fixed for this constructed tree. -/
def terminal (j : ℕ) : D.K :=
  terminalSequence D.closed D.convex D.T D.nonexpansive A.anchor j

/-- All extended functionals still have norm at most one. -/
theorem functionalAt_norm (k : ℕ) (v : A.tree.Node k) :
    ‖A.functionalAt k v‖ ≤ 1 := by
  cases k with
  | zero => simp [functionalAt]
  | succ k => exact A.functional_norm k v

theorem budget_pos (k : ℕ) (v : A.tree.Node (k + 1)) :
    0 < A.budget (k + 1) v :=
  OrderedTree.retainedBudget_pos A.label ⟨k, v⟩

theorem summable_budget :
    Summable (fun v : A.tree.NonrootNode => A.budget (v.1 + 1) v.2) :=
  OrderedTree.summable_retainedBudget A.label A.label_injective

end SwitchingTreeData
end ReflexiveFixedPoints

end

end OAI
