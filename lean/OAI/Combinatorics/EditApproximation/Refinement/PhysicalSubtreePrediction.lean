import OAI.Combinatorics.EditApproximation.Refinement.PhysicalSubtreeCharges
import OAI.Combinatorics.EditApproximation.Refinement.StageComparisonPrediction
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalOnlineBand

namespace OAI

/-! The actual comparison charges and rational velocity predictor at a physical slot. -/

namespace EditApproximation

open Finset

section Stage

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hP : 66 ≤ P) (T : ℕ) (root : PhysicalNode M J) (K : ℕ)
  (hheight : root.1.val + K = J) (rootQ : TargetInterval target.length)

local notation "frontier" => comparisonFrontier source target hM P hP
  (some (physicalSourceInterval source.length root, rootQ))

noncomputable def subtreeComparisonPrediction (d : Fin K) (path : TreeLayer M d.val) : ℚ := by
  classical
  exact match frontier d.val path with
  | none => 0
  | some (parent, q) => if hstop : comparisonStopped source target parent q then 0 else
      let hc : 0 < stateEditCost (substring source parent.lo parent.hi) target q := by
        unfold comparisonStopped at hstop
        omega
      let node : PhysicalNode M J := physicalSubtreeNode root d.val path (by omega)
      let b := 2 ^ Nat.log 2 (stateEditCost (substring source parent.lo parent.hi) target q)
      let r := roundInterval (seedGridSpacing b P) q
      let action := comparisonChildren source target hM P hP parent q hc
      let hn : wideActionList M parent r b P ≠ [] := by
        have hmem := (comparisonChildren_spec source target hM P hP parent q hc).1
        intro heq
        rw [heq] at hmem
        exact List.not_mem_nil hmem
      rationalStateGap (substring source parent.lo parent.hi) target r /
        rationalWideActionMinimum parent r b P hn
          (physicalBandChildMassTable source target U N P F A T node (by dsimp only [node, physicalSubtreeNode]; omega))

 theorem subtreeComparisonPrediction_active (d : Fin K) (path : TreeLayer M d.val)
    (q : TargetInterval target.length)
    (heq : frontier d.val path = some (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path), q))
    (hactive : ¬ comparisonStopped source target (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)) q)
    (hn : wideActionList M (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path))
      (roundInterval (seedGridSpacing (2 ^ Nat.log 2 (stateEditCost
        (substring source (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)).lo
          (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)).hi) target q)) P) q)
      (2 ^ Nat.log 2 (stateEditCost (substring source (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)).lo
        (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)).hi) target q)) P ≠ []) :
    subtreeComparisonPrediction source target hM U N P F A hP T root K hheight rootQ d path =
      rationalStateGap (substring source (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)).lo
        (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)).hi) target
        (roundInterval (seedGridSpacing (2 ^ Nat.log 2 (stateEditCost
          (substring source (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)).lo
            (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)).hi) target q)) P) q) /
      rationalWideActionMinimum (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path))
        (roundInterval (seedGridSpacing (2 ^ Nat.log 2 (stateEditCost
          (substring source (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)).lo
            (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)).hi) target q)) P) q)
        (2 ^ Nat.log 2 (stateEditCost (substring source (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)).lo
          (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)).hi) target q)) P hn
        (physicalBandChildMassTable source target U N P F A T
          (physicalSubtreeNode root d.val path (by omega) : PhysicalNode M J) (by dsimp only [physicalSubtreeNode]; omega)) := by
  unfold subtreeComparisonPrediction
  rw [heq]
  simp only [dite_eq_right hactive]

 theorem subtreeComparisonCharges_active (d : Fin K) (path : TreeLayer M d.val)
    (q : TargetInterval target.length)
    (heq : frontier d.val path = some (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path), q))
    (hactive : ¬ comparisonStopped source target (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)) q)
    (hc : 0 < stateEditCost (substring source (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)).lo
      (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)).hi) target q)
    (hn : wideActionList M (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path))
      (roundInterval (seedGridSpacing (2 ^ Nat.log 2 (stateEditCost
        (substring source (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)).lo
          (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)).hi) target q)) P) q)
      (2 ^ Nat.log 2 (stateEditCost (substring source (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)).lo
        (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)).hi) target q)) P ≠ []) :
    let parent := sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)
    let node : PhysicalNode M J := physicalSubtreeNode root d.val path (by omega)
    let r := roundInterval (seedGridSpacing (2 ^ Nat.log 2 (stateEditCost (substring source parent.lo parent.hi) target q)) P) q
    let action := comparisonChildren source target hM P hP parent q hc
    let child := fun i s => (physicalBandChildMassTable source target U N P F A T node (by dsimp only [node, physicalSubtreeNode]; omega) i s : ℝ)
    subtreeComparisonCharges source target hM U N P F A hP T root K hheight rootQ d path =
      (comparisonActionCurvature source target parent r action child,
        comparisonActionMass action child - wideActionMinimum parent r
          (2 ^ Nat.log 2 (stateEditCost (substring source parent.lo parent.hi) target q)) P hn child) := by
  unfold subtreeComparisonCharges
  rw [heq]
  simp only [dite_eq_right hactive]
  rfl

end Stage

end EditApproximation

end OAI
