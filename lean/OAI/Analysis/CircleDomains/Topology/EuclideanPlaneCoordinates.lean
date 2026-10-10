import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.ContDiff.Operations

namespace OAI

/-! The area-preserving linear coordinates connecting the physical plane
with the Euclidean-space Sobolev library. -/

open Set MeasureTheory

noncomputable section

namespace CircleDomainRigidity

abbrev EuclideanPlane := EuclideanSpace ℝ (Fin 2)

def euclideanPlaneCoordinates : EuclideanPlane ≃L[ℝ] ℝ × ℝ :=
  (EuclideanSpace.equiv (Fin 2) ℝ).trans (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)

@[simp] theorem euclideanPlaneCoordinates_apply (x : EuclideanPlane) :
    euclideanPlaneCoordinates x = (x 0, x 1) := rfl

@[simp] theorem euclideanPlaneCoordinates_single_zero :
    euclideanPlaneCoordinates (EuclideanSpace.single 0 1) = (1, 0) := by
  simp [euclideanPlaneCoordinates_apply]

@[simp] theorem euclideanPlaneCoordinates_single_one :
    euclideanPlaneCoordinates (EuclideanSpace.single 1 1) = (0, 1) := by
  simp [euclideanPlaneCoordinates_apply]

theorem euclideanPlaneCoordinates_measurePreserving :
    MeasurePreserving euclideanPlaneCoordinates volume volume := by
  change MeasurePreserving ((MeasurableEquiv.finTwoArrow :
    (Fin 2 → ℝ) ≃ᵐ (ℝ × ℝ)) ∘ WithLp.ofLp) volume volume
  exact (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))

theorem euclideanPlaneCoordinates_symm_measurePreserving :
    MeasurePreserving euclideanPlaneCoordinates.symm volume volume := by
  exact euclideanPlaneCoordinates_measurePreserving.symm
    euclideanPlaneCoordinates.toHomeomorph.toMeasurableEquiv

end CircleDomainRigidity

end

end OAI
