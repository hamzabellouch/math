import OAI.Combinatorics.EditApproximation.Refinement.StageComparisonBad
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalOnlineBand

namespace OAI

/-! The actual comparison charges and rational velocity predictor at a physical slot. -/

namespace EditApproximation

open Finset

section Stage

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hP : 66 ≤ P) (T : ℕ) (rootQ : TargetInterval target.length)

local notation "frontier" => comparisonFrontier source target hM P hP
  (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ))

noncomputable def stageComparisonPrediction (d : Fin J) (path : TreeLayer M d.val) : ℚ := by
  classical
  exact match frontier d.val path with
  | none => 0
  | some (parent, q) => if hstop : comparisonStopped source target parent q then 0 else
      let hc : 0 < stateEditCost (substring source parent.lo parent.hi) target q := by
        unfold comparisonStopped at hstop
        omega
      let node : PhysicalNode M J := ⟨⟨d.val, by omega⟩, path⟩
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
          (physicalBandChildMassTable source target U N P F A T node d.isLt)

 theorem stageComparisonPrediction_active (d : Fin J) (path : TreeLayer M d.val)
    (q : TargetInterval target.length)
    (heq : frontier d.val path = some (sourceIntervalAt M source.length d.val path, q))
    (hactive : ¬ comparisonStopped source target (sourceIntervalAt M source.length d.val path) q)
    (hn : wideActionList M (sourceIntervalAt M source.length d.val path)
      (roundInterval (seedGridSpacing (2 ^ Nat.log 2 (stateEditCost
        (substring source (sourceIntervalAt M source.length d.val path).lo
          (sourceIntervalAt M source.length d.val path).hi) target q)) P) q)
      (2 ^ Nat.log 2 (stateEditCost (substring source (sourceIntervalAt M source.length d.val path).lo
        (sourceIntervalAt M source.length d.val path).hi) target q)) P ≠ []) :
    stageComparisonPrediction source target hM U N P F A hP T rootQ d path =
      rationalStateGap (substring source (sourceIntervalAt M source.length d.val path).lo
        (sourceIntervalAt M source.length d.val path).hi) target
        (roundInterval (seedGridSpacing (2 ^ Nat.log 2 (stateEditCost
          (substring source (sourceIntervalAt M source.length d.val path).lo
            (sourceIntervalAt M source.length d.val path).hi) target q)) P) q) /
      rationalWideActionMinimum (sourceIntervalAt M source.length d.val path)
        (roundInterval (seedGridSpacing (2 ^ Nat.log 2 (stateEditCost
          (substring source (sourceIntervalAt M source.length d.val path).lo
            (sourceIntervalAt M source.length d.val path).hi) target q)) P) q)
        (2 ^ Nat.log 2 (stateEditCost (substring source (sourceIntervalAt M source.length d.val path).lo
          (sourceIntervalAt M source.length d.val path).hi) target q)) P hn
        (physicalBandChildMassTable source target U N P F A T
          (⟨⟨d.val, by omega⟩, path⟩ : PhysicalNode M J) d.isLt) := by
  unfold stageComparisonPrediction
  rw [heq]
  simp only [dite_eq_right hactive]

 theorem stageComparisonCharges_active (d : Fin J) (path : TreeLayer M d.val)
    (q : TargetInterval target.length)
    (heq : frontier d.val path = some (sourceIntervalAt M source.length d.val path, q))
    (hactive : ¬ comparisonStopped source target (sourceIntervalAt M source.length d.val path) q)
    (hc : 0 < stateEditCost (substring source (sourceIntervalAt M source.length d.val path).lo
      (sourceIntervalAt M source.length d.val path).hi) target q)
    (hn : wideActionList M (sourceIntervalAt M source.length d.val path)
      (roundInterval (seedGridSpacing (2 ^ Nat.log 2 (stateEditCost
        (substring source (sourceIntervalAt M source.length d.val path).lo
          (sourceIntervalAt M source.length d.val path).hi) target q)) P) q)
      (2 ^ Nat.log 2 (stateEditCost (substring source (sourceIntervalAt M source.length d.val path).lo
        (sourceIntervalAt M source.length d.val path).hi) target q)) P ≠ []) :
    let parent := sourceIntervalAt M source.length d.val path
    let node : PhysicalNode M J := ⟨⟨d.val, by omega⟩, path⟩
    let r := roundInterval (seedGridSpacing (2 ^ Nat.log 2 (stateEditCost (substring source parent.lo parent.hi) target q)) P) q
    let action := comparisonChildren source target hM P hP parent q hc
    let child := fun i s => (physicalBandChildMassTable source target U N P F A T node d.isLt i s : ℝ)
    stageComparisonCharges source target hM U N P F A hP T rootQ d path =
      (comparisonActionCurvature source target parent r action child,
        comparisonActionMass action child - wideActionMinimum parent r
          (2 ^ Nat.log 2 (stateEditCost (substring source parent.lo parent.hi) target q)) P hn child) := by
  unfold stageComparisonCharges
  rw [heq]
  simp only [dite_eq_right hactive]
  rfl

end Stage

theorem nonbad_charge_bounds (scale ratio K G : ℝ) (hratio : 0 < ratio)
    (hnotbad : ¬ (scale < ratio * K ∨ scale < ratio * G)) :
    K ≤ scale / ratio ∧ G ≤ scale / ratio := by
  have h := not_or.mp hnotbad
  constructor
  · apply (le_div_iff₀ hratio).2
    simpa only [mul_comm] using le_of_not_gt h.1
  · apply (le_div_iff₀ hratio).2
    simpa only [mul_comm] using le_of_not_gt h.2

end EditApproximation

end OAI
