import OAI.Combinatorics.BalancedRyser.Local.GlobalPartialAlignment

namespace OAI

namespace Balanced.TupleAlignment

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem unexposed_generator_offsets_law (T : FourTuple F)
    (hinj : Function.Injective T.generator)
    (D : Finset (Direction F)) (a : MergedPairs F)
    (hfresh : ∀ i, T.generator i ∉ D) :
    ((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
      (PartialAlignment.canonical_exposure_supported D a)).map
        (fun M i => M (T.generator i)) =
      PMF.uniformOfFintype (Fin 4 → Bool → F) := by
  have hempty : PartialAlignment.exposedTupleIndices T D = ∅ := by
    ext i
    simp [PartialAlignment.exposedTupleIndices, hfresh i]
  have hevent : {o : Fin 4 → Bool → F |
      ∀ i ∈ PartialAlignment.exposedTupleIndices T D,
        o i = a (T.generator i)} = Set.univ := by simp [hempty]
  have hfilter : (PMF.uniformOfFintype (Fin 4 → Bool → F)).filter
      {o | ∀ i ∈ PartialAlignment.exposedTupleIndices T D,
        o i = a (T.generator i)}
      (PartialAlignment.partialOffsets_supported
        (PartialAlignment.exposedTupleIndices T D) (fun i => a (T.generator i))) =
      PMF.uniformOfFintype (Fin 4 → Bool → F) := by
    ext o
    simp only [PMF.filter_apply, hevent, Set.indicator_univ, PMF.tsum_coe,
      inv_one, mul_one]
  simpa only [PartialAlignment.offsetLaw_eq_uniform] using
    (PartialAlignment.global_exposed_tuple_law T hinj D a).trans hfilter

theorem unexposed_tuplePoint_law (T : FourTuple F)
    (hinj : Function.Injective T.generator)
    (D : Finset (Direction F)) (a : MergedPairs F)
    (hfresh : ∀ i, T.generator i ∉ D) :
    ((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
      (PartialAlignment.canonical_exposure_supported D a)).map
        (fun M => tuplePoint M T) = PMF.uniformOfFintype (Fin 4 → Point F) := by
  let hd := adjacent_ne_of_injective T hinj
  let r : MergedPairs F → Fin 4 → Bool → F := fun M i => M (T.generator i)
  have hf : (fun M => tuplePoint M T) =
      (tuplePositionEquiv T.generator hd T.side) ∘ r := by
    funext M i
    rfl
  rw [hf, ← PMF.map_comp]
  change (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
    (PartialAlignment.canonical_exposure_supported D a)).map r).map
      (tuplePositionEquiv T.generator hd T.side) = _
  rw [unexposed_generator_offsets_law T hinj D a hfresh]
  exact tuplePosition_uniform T.generator hd T.side

theorem unexposed_tuplePoint_event_probability (T : FourTuple F)
    (hinj : Function.Injective T.generator)
    (D : Finset (Direction F)) (a : MergedPairs F)
    (hfresh : ∀ i, T.generator i ∉ D) (E : Set (Fin 4 → Point F)) :
    (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
      (PartialAlignment.canonical_exposure_supported D a)).toOuterMeasure
        {M | tuplePoint M T ∈ E}).toReal =
      offsetEventProbability {M | tuplePoint M T ∈ E} := by
  have hcond := congrArg (fun law : PMF (Fin 4 → Point F) =>
    (law.toOuterMeasure E).toReal) (unexposed_tuplePoint_law T hinj D a hfresh)
  have horiginal := congrArg (fun law : PMF (Fin 4 → Point F) =>
    (law.toOuterMeasure E).toReal) (tuplePoint_uniform T hinj)
  rw [PMF.toOuterMeasure_map_apply] at hcond horiginal
  exact hcond.trans horiginal.symm

end
end Balanced.TupleAlignment

end OAI
