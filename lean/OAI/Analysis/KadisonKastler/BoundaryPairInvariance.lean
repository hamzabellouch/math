import OAI.Analysis.KadisonKastler.HilbertInvariantFunctions
import OAI.Analysis.KadisonKastler.ProductBoundaryLifts

namespace OAI

/-! Hilbert-valued boundary functions are invariant under advancing either path. -/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable {X Y K : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {S : X → X} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [TopologicalSpace.SeparableSpace K]

theorem hilbert_boundary_first_invariance (hS : Measure.QuasiMeasurePreserving S μ μ)
    {f : ShiftBoundarySpace μ S × Y → K}
    (hf : AEStronglyMeasurable f ((shiftBoundaryMeasure μ S).prod ν)) :
    ∀ᵐ z ∂μ.prod ν,
      f (shiftBoundaryMap μ S (S z.1), z.2) = f (shiftBoundaryMap μ S z.1, z.2) := by
  have ht : AEStronglyMeasurable[firstInvariantSigma μ S]
      (fun z : X × Y => f (shiftBoundaryMap μ S z.1, z.2))
      ((μ.prod ν).trim (firstInvariantSigma_le (Y := Y) (μ := μ) (S := S))) := by
    rw [firstBoundaryMeasure_eq_trim μ S]
    exact hf
  exact firstInvariantSigma_fixed_hilbert hS (ht.of_trim (firstInvariantSigma_le (Y := Y) (μ := μ) (S := S)))

variable {f : ShiftBoundarySpace μ S × ShiftBoundarySpace μ S → K}

def boundaryPairLift (f : ShiftBoundarySpace μ S × ShiftBoundarySpace μ S → K)
    (z : X × X) : K := f (shiftBoundaryMap μ S z.1, shiftBoundaryMap μ S z.2)

omit [IsProbabilityMeasure ν] in
theorem boundaryPairLift_advance_left (hS : Measure.QuasiMeasurePreserving S μ μ)
    (hf : AEStronglyMeasurable f ((shiftBoundaryMeasure μ S).prod (shiftBoundaryMeasure μ S))) :
    ∀ᵐ z ∂μ.prod μ, boundaryPairLift f (S z.1, z.2) = boundaryPairLift f z := by
  have ht : AEStronglyMeasurable
      (fun z : ShiftBoundarySpace μ S × X => f (z.1, shiftBoundaryMap μ S z.2))
      ((shiftBoundaryMeasure μ S).prod μ) :=
    hf.comp_quasiMeasurePreserving ((MeasurePreserving.id (shiftBoundaryMeasure μ S)).prod
      (shiftBoundaryMap_measurePreserving μ S)).quasiMeasurePreserving
  exact hilbert_boundary_first_invariance hS ht

omit [IsProbabilityMeasure ν] in
theorem boundaryPairLift_advance_right (hS : Measure.QuasiMeasurePreserving S μ μ)
    (hf : AEStronglyMeasurable f ((shiftBoundaryMeasure μ S).prod (shiftBoundaryMeasure μ S))) :
    ∀ᵐ z ∂μ.prod μ, boundaryPairLift f (z.1, S z.2) = boundaryPairLift f z := by
  have hs := hf.comp_quasiMeasurePreserving (Measure.measurePreserving_swap
    (μ := shiftBoundaryMeasure μ S) (ν := shiftBoundaryMeasure μ S)).quasiMeasurePreserving
  have hi := boundaryPairLift_advance_left hS hs
  exact (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hi

end

end KadisonKastler

end OAI
