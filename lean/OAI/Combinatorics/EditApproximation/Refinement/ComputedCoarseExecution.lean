import OAI.Combinatorics.EditApproximation.Refinement.ComputedPhysicalWork
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalCoarseExecution
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation

open MeasureTheory





instance computedPhysicalCoarseLaw_probability (source target : List ℕ) (N : ℕ) :
    IsProbabilityMeasure (computedPhysicalCoarseLaw source target N) := by
  unfold computedPhysicalCoarseLaw
  infer_instance

noncomputable def computedPhysicalCoarseSeed (source target : List ℕ) (N : ℕ) :=
  physicalCoarseSeedTable (M := (integerParameters N).M)
    (J := intervalTreeDepth (integerParameters N).M source.length)
    source target N (integerParameters N).B (computedPhysicalCoarseDepth source target N)

end EditApproximation

end OAI
