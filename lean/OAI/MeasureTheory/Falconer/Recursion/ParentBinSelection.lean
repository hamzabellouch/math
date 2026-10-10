import OAI.MeasureTheory.Falconer.Recursion.ParentCellGeometry
import OAI.MeasureTheory.Falconer.Angular.RotatedBinPartition

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

noncomputable def sourceParentInactiveSelection (N : ℕ) (sig t : ℝ)
    (X Y : DyadicSquare) (A B : CellPath) : UnitCircle → ℂ :=
  rotatedBinSelection (angularBinCount (graphUncappedAngularScale N sig t))
    (inactiveAngularLabels (angularBinCount (graphUncappedAngularScale N sig t))
      (sourceCenteredCellDirection X Y (X.descendant A) (Y.descendant B))
      (3*graphUncappedAngularScale N sig t)) (sourceParentAxis X Y)

theorem sourceParentInactiveSelection_measurable (N : ℕ) (sig t : ℝ)
    (X Y : DyadicSquare) (A B : CellPath) :
    Measurable (sourceParentInactiveSelection N sig t X Y A B) :=
  measurable_rotatedBinSelection _ _ _

theorem sourceParentInactiveSelection_norm_le (N : ℕ) (sig t : ℝ)
    (X Y : DyadicSquare) (A B : CellPath) (dir : UnitCircle) :
    ‖sourceParentInactiveSelection N sig t X Y A B dir‖ ≤ 1 :=
  rotatedBinSelection_norm_le _ _ _ _

theorem sourceParentRetainedSelection_norm_le (N : ℕ) (sig t : ℝ)
    (X Y : DyadicSquare) (A B : CellPath) (dir : UnitCircle) :
    ‖1-sourceParentInactiveSelection N sig t X Y A B dir‖ ≤ 1 := by
  unfold sourceParentInactiveSelection
  rw [← inactive_rotated_complement _ (angularBinCount_pos (by
    unfold graphUncappedAngularScale
    positivity))]
  exact rotatedBinSelection_norm_le _ _ _ _

theorem DyadicSquare.descendant_side_at_depth (X : DyadicSquare) {a : ℝ}
    (hX : X.side ≤ (2:ℝ)^(-a)) {A : CellPath} {n : ℕ} (hA : A.length = n) :
    (X.descendant A).side ≤ (2:ℝ)^(-(a+n)) := by
  rw [X.descendant_side, hA]
  calc
    _ ≤ (2:ℝ)^(-a)/(2:ℝ)^n := div_le_div_of_nonneg_right hX (by positivity)
    _ = _ := by
      rw [show -(a+(n:ℝ)) = -a-(n:ℝ) by ring, Real.rpow_sub (by norm_num : (0:ℝ) < 2),
        Real.rpow_natCast]

end PlanarFalconer

end OAI
