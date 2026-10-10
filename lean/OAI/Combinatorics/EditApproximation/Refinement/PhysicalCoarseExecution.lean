import OAI.Combinatorics.EditApproximation.Refinement.PhysicalCoarseSeedLaw
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalFamilyRuntime
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation
open MeasureTheory

section Execution
variable {α : Type} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P H B : ℕ)
  (depth : PhysicalEntry M J target.length → ℕ)





variable [NeZero B] [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]

noncomputable def physicalCoarseExecutionLaw :
    Measure (PhysicalCoarseExecution (R := R) source target N P H B depth) :=
  (coarseFullSeedMeasure B depth
    (fun entry => physicalSource source entry.1)
    (fun entry => substring target entry.2.lo entry.2.hi)).prod
  (rejectionRuntimeArrayLaw (physicalFamilyRange (M := M) (J := J) (R := R)
    target N P (inputSmallLog N) (40 * smallLogExponent N) H
      (inputSmallLog N ^ 80) (computedSeedPassCount N) (H ^ 2)))

omit [NeZero M] [NeZero R] [NeZero B] in
 theorem physicalCoarseExecutionProjection_measurable :
    Measurable (physicalCoarseExecutionProjection (R := R) source target N P H B depth) := by
  unfold physicalCoarseExecutionProjection
  exact ((measurable_of_finite (physicalCoarseSeedTable source target N B depth)).comp
    measurable_fst).prodMk measurable_snd

omit [NeZero R] in
 theorem physicalCoarseExecutionProjection_law :
    (physicalCoarseExecutionLaw (R := R) source target N P H B depth).map
      (physicalCoarseExecutionProjection (R := R) source target N P H B depth) =
    physicalFamilyRuntimeLaw (R := R) target N P H
      (physicalCoarseSeedLaw source target N B depth) := by
  unfold physicalCoarseExecutionLaw physicalCoarseExecutionProjection physicalFamilyRuntimeLaw
  change ((_ : Measure (PhysicalCoarseDraw source target B depth)).prod _).map
    (Prod.map (physicalCoarseSeedTable source target N B depth) id) = _
  rw [← Measure.map_prod_map _ _ (measurable_of_finite _) measurable_id, Measure.map_id]
  rfl

end Execution
end EditApproximation

end OAI
