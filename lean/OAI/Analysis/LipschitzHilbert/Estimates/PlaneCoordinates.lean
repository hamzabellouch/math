import OAI.Analysis.LipschitzHilbert.Estimates.PublishedInputs
import Mathlib.MeasureTheory.Constructions.Pi

namespace OAI

/-! The measure-preserving bridge from the manuscript's real coordinate
pairs to the Euclidean plane used by the published maximal estimate. -/

noncomputable section
open MeasureTheory
namespace LipschitzHilbert

def planeCoordinates : (ℝ × ℝ) ≃ᵐ Plane :=
  MeasurableEquiv.finTwoArrow.symm.trans (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))

theorem planeCoordinates_apply (z : ℝ × ℝ) :
    planeCoordinates z = WithLp.toLp 2 ![z.1,z.2] := rfl

theorem planeCoordinates_symm_apply (z : Plane) :
    planeCoordinates.symm z = (z 0,z 1) := rfl

theorem planeCoordinates_measurePreserving :
    MeasurePreserving planeCoordinates (volume.prod volume) volume := by
  exact (PiLp.volume_preserving_toLp (Fin 2)).comp
    (measurePreserving_finTwoArrow (volume : Measure ℝ)).symm

theorem planeCoordinates_image_measure (s : Set (ℝ × ℝ)) :
    volume (planeCoordinates '' s) = (volume.prod volume) s := by
  have h := planeCoordinates_measurePreserving.measure_preimage_equiv (planeCoordinates '' s)
  rw [Set.preimage_image_eq s planeCoordinates.injective] at h
  exact h.symm

end LipschitzHilbert

end

end OAI
