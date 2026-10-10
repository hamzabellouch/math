import OAI.Combinatorics.BalancedRyser.Local.GlobalPartialAlignment
import OAI.Combinatorics.BalancedRyser.Local.ReuseTargetSum

namespace OAI

namespace Balanced.PartialAlignment
open TupleAlignment ConditionalRestriction

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def canonicalExternalAlignmentProbability (T : FourTuple F) (p : Point F)
    (g : Direction F) (D : Finset (Direction F)) (a : MergedPairs F) : ℝ :=
  (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
    (canonical_exposure_supported D a)).toOuterMeasure
    {M | (∀ i, OnLine (tuplePoint M T i) (lineThrough g p)) ∧
      ∀ i, tuplePoint M T i ≠ p}).toReal

theorem canonicalExternalAlignmentProbability_eq (T : FourTuple F)
    (hT : Function.Injective T.generator) (p : Point F) (g : Direction F)
    (D : Finset (Direction F)) (a : MergedPairs F) :
    canonicalExternalAlignmentProbability T p g D a =
      externalAlignmentProbability T.generator (adjacent_ne_of_injective T hT)
        T.side p g (exposedTupleIndices T D) (fun i => a (T.generator i)) := by
  let hd := adjacent_ne_of_injective T hT
  let E : Set (Fin 4 → Bool → F) :=
    {o | (∀ i, OnLine (tuplePositionEquiv T.generator hd T.side o i)
      (lineThrough g p)) ∧ ∀ i, tuplePositionEquiv T.generator hd T.side o i ≠ p}
  have h := congrArg (fun law => (law.toOuterMeasure E).toReal)
    (global_exposed_tuple_law T hT D a)
  rw [PMF.toOuterMeasure_map_apply, partialOffsets_conditional_law,
    PMF.toOuterMeasure_map_apply] at h
  simpa only [canonicalExternalAlignmentProbability, offsetLaw_eq_uniform,
    externalAlignmentProbability, externalAlignmentEvent, E, Set.preimage_ofPred_eq,
    tuplePositionEquiv_apply, tuplePoint, constituent] using h

theorem sum_canonicalExternalAlignmentProbability_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (p : Point F)
    (D : Finset (Direction F)) (a : MergedPairs F) :
    (∑ g ∈ (Finset.univ.filter (fun g : Direction F => ∀ i, T.generator i ≠ g)),
      canonicalExternalAlignmentProbability T p g D a) ≤
      (if (fixedPositions (exposedTupleIndices T D)).card = 0 then
        (Fintype.card F : ℝ) + 1 else 1) *
      ((Fintype.card F : ℝ)⁻¹ ^ (4 - (fixedPositions (exposedTupleIndices T D)).card)) := by
  simp_rw [canonicalExternalAlignmentProbability_eq T hT]
  exact sum_externalAlignmentProbability_le T.generator
    (adjacent_ne_of_injective T hT) T.side p (exposedTupleIndices T D)
    (fun i => a (T.generator i))

end
end Balanced.PartialAlignment

end OAI
