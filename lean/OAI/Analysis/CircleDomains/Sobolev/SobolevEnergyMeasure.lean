import OAI.Analysis.CircleDomains.Sobolev.SquarePoincareEnergy
import Mathlib.MeasureTheory.Measure.WithDensity

namespace OAI

/-! The actual local two-coordinate Sobolev energy as a measure. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

def coordinateSobolevEnergy (V : EuclideanPlane → EuclideanPlane) : Measure (ℝ × ℝ) :=
  volume.withDensity (fun p => ENNReal.ofReal
    ((|V (euclideanPlaneCoordinates.symm p) 0|+|V (euclideanPlaneCoordinates.symm p) 1|)^2))

lemma coordinateSobolevEnergy_square (V : EuclideanPlane → EuclideanPlane)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R)))
    (c : ℝ × ℝ) (r : ℝ) :
    coordinateSobolevEnergy V (coordinateSquare c r) = ENNReal.ofReal
      (∫ p in coordinateSquare c r,
        (|V (euclideanPlaneCoordinates.symm p) 0|+|V (euclideanPlaneCoordinates.symm p) 1|)^2) := by
  have hG := (local_partial_coordinate_memLp hLp (coordinateSquare_compact c r) 0).norm.add
    (local_partial_coordinate_memLp hLp (coordinateSquare_compact c r) 1).norm
  rw [coordinateSobolevEnergy, withDensity_apply _ (coordinateSquare_compact c r).measurableSet]
  exact (ofReal_integral_eq_lintegral_ofReal hG.integrable_sq
    (Eventually.of_forall fun _ => sq_nonneg _)).symm

end CircleDomainRigidity

end

end OAI
