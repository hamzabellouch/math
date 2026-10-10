import OAI.MeasureTheory.Falconer.Angular.SmoothRotatedCone
import OAI.MeasureTheory.Falconer.Estimates.DistanceFormRemoval

namespace OAI

namespace PlanarFalconer
attribute [local instance] Classical.propDecidable
open Set
open scoped ContDiff

theorem rotatedBinSelection_complement {n : ℕ} (hn : 0 < n) (S : Finset ℕ)
    (hS : S ⊆ Finset.range n) (axis : ℝ) (dir : UnitCircle) :
    rotatedBinSelection n (Finset.range n \ S) axis dir =
      1-rotatedBinSelection n S axis dir := by
  simp only [rotatedBinSelection, Finset.sum_sdiff_eq_sub hS, circleAngularBin_partition hn,
    Complex.ofReal_sub, Complex.ofReal_one]

theorem rotatedBinSelection_angular_contDiff (n : ℕ) (S : Finset ℕ) (axis : ℝ) :
    ContDiff ℝ ∞ (fun θ => rotatedBinSelection n S axis (sourceUnitDirection θ)) := by
  have he : (fun θ => rotatedBinSelection n S axis (sourceUnitDirection θ)) =
      fun θ => ((∑ j ∈ S, periodicAngularBin n j (θ-axis) : ℝ) : ℂ) := by
    funext θ
    simp only [rotatedBinSelection, sourceCircleRotate_comp, circleAngularBin_comp, sub_eq_add_neg]
  rw [he]
  exact Complex.ofRealCLM.contDiff.comp
    ((ContDiff.sum (fun j _ => periodicAngularBin_contDiff n j)).comp
      (contDiff_id.sub contDiff_const))

theorem inactive_rotated_complement (n : ℕ) (hn : 0 < n) (e : UnitCircle)
    (radius axis : ℝ) (dir : UnitCircle) :
    rotatedBinSelection n (Finset.range n \ inactiveAngularLabels n e radius) axis dir =
      1-rotatedBinSelection n (inactiveAngularLabels n e radius) axis dir :=
  rotatedBinSelection_complement hn _ (Finset.filter_subset _ _) axis dir

end PlanarFalconer

end OAI
