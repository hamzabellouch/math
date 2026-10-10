import OAI.Combinatorics.BalancedRyser.Local.PartialAlignment
import OAI.Combinatorics.BalancedRyser.Probability.ConditionalRestriction
import OAI.Combinatorics.BalancedRyser.Probability.GlobalTupleLaw

namespace OAI

namespace Balanced.PartialAlignment
open TupleAlignment ConditionalRestriction

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def exposedTupleIndices (T : FourTuple F) (D : Finset (Direction F)) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => T.generator i ∈ D)

theorem offsetLaw_eq_uniform : offsetLaw F = PMF.uniformOfFintype (MergedPairs F) := by
  ext M
  simp only [offsetLaw, PMF.uniformOfFintype_apply, Fintype.card_fun,
    Fintype.card_option, Fintype.card_bool]

theorem global_exposed_tuple_law (T : FourTuple F)
    (hT : Function.Injective T.generator) (D : Finset (Direction F)) (a : MergedPairs F) :
    ((PMF.uniformOfFintype (MergedPairs F)).filter
      {M | ∀ d, d ∈ D → M d = a d} (fixed_supported (fun d => d ∈ D) a)).map
      (fun M i => M (T.generator i)) =
    (PMF.uniformOfFintype (Fin 4 → Bool → F)).filter
      {o | ∀ i ∈ exposedTupleIndices T D, o i = a (T.generator i)}
      (partialOffsets_supported (exposedTupleIndices T D) (fun i => a (T.generator i))) := by
  simpa only [exposedTupleIndices, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk] using
    uniform_conditional_restrict (A := Bool → F) ⟨T.generator, hT⟩
      (fun d => d ∈ D) a

theorem global_conditional_alignment_probability_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (g : Direction F)
    (hg : ∀ i, T.generator i ≠ g) (c : F)
    (D : Finset (Direction F)) (a : MergedPairs F) :
    (((PMF.uniformOfFintype (MergedPairs F)).filter
      {M | ∀ d, d ∈ D → M d = a d} (fixed_supported (fun d => d ∈ D) a)).toOuterMeasure
      {M | ∀ i, OnLine (tuplePoint M T i) (g,c)}).toReal ≤
      (Fintype.card F : ℝ)⁻¹ ^ (4 - (fixedPositions (exposedTupleIndices T D)).card) := by
  let hd := adjacent_ne_of_injective T hT
  let E : Set (Fin 4 → Bool → F) :=
    {o | ∀ i, OnLine (tuplePositionEquiv T.generator hd T.side o i) (g,c)}
  have h := congrArg (fun law => (law.toOuterMeasure E).toReal)
    (global_exposed_tuple_law T hT D a)
  rw [PMF.toOuterMeasure_map_apply] at h
  calc
    _ = (((PMF.uniformOfFintype (Fin 4 → Bool → F)).filter
        {o | ∀ i ∈ exposedTupleIndices T D, o i = a (T.generator i)}
        (partialOffsets_supported (exposedTupleIndices T D)
          (fun i => a (T.generator i)))).toOuterMeasure E).toReal := h
    _ ≤ _ := original_conditional_alignment_probability_le
      T.generator hd T.side g hg c (exposedTupleIndices T D) (fun i => a (T.generator i))

theorem canonical_exposure_supported (D : Finset (Direction F)) (a : MergedPairs F) :
    ∃ M ∈ {M : MergedPairs F | ∀ d, d ∈ D → M d = a d},
      M ∈ (offsetLaw F).support := by
  rw [offsetLaw_eq_uniform]
  exact fixed_supported (fun d => d ∈ D) a

theorem canonical_conditional_alignment_probability_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (g : Direction F)
    (hg : ∀ i, T.generator i ≠ g) (c : F)
    (D : Finset (Direction F)) (a : MergedPairs F) :
    (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
      (canonical_exposure_supported D a)).toOuterMeasure
      {M | ∀ i, OnLine (tuplePoint M T i) (g,c)}).toReal ≤
      (Fintype.card F : ℝ)⁻¹ ^ (4 - (fixedPositions (exposedTupleIndices T D)).card) := by
  simpa only [offsetLaw_eq_uniform] using
    global_conditional_alignment_probability_le T hT g hg c D a

end
end Balanced.PartialAlignment

end OAI
