import OAI.Combinatorics.BalancedRyser.Incidence.CandidateFreshIncidence
import OAI.Combinatorics.BalancedRyser.Probability.UnexposedTupleLaw

namespace OAI

namespace Balanced.CandidateFreshIncidence

noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem conditional_probability_eq_positionProbability (T : FourTuple F)
    (hT : Function.Injective T.generator) (D : Finset (Direction F))
    (a : MergedPairs F) (hfresh : ∀ i, T.generator i ∉ D)
    (P : (Fin 4 → Point F) → Prop) :
    (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
      (PartialAlignment.canonical_exposure_supported D a)).toOuterMeasure
        {M | P (tuplePoint M T)}).toReal = positionProbability P := by
  exact (TupleAlignment.unexposed_tuplePoint_event_probability T hT D a hfresh
    {p | P p}).trans (offset_probability_eq T hT P)

theorem conditional_tuple_hits_line_probability_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (D : Finset (Direction F))
    (a : MergedPairs F) (hfresh : ∀ i, T.generator i ∉ D)
    (g : Direction F) (l : Line F) :
    (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
      (PartialAlignment.canonical_exposure_supported D a)).toOuterMeasure
        {M | (∃ c, ∀ j, OnLine (tuplePoint M T j) (g,c)) ∧
          ∃ i, OnLine (tuplePoint M T i) l}).toReal ≤
      4 * (Fintype.card F : ℝ)⁻¹^4 := by
  rw [conditional_probability_eq_positionProbability T hT D a hfresh (fun p =>
    (∃ c, ∀ j, OnLine (p j) (g,c)) ∧ ∃ i, OnLine (p i) l)]
  exact same_direction_hits_line_le g l

theorem conditional_tuple_contains_point_probability_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (D : Finset (Direction F))
    (a : MergedPairs F) (hfresh : ∀ i, T.generator i ∉ D)
    (g : Direction F) (y : Point F) :
    (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
      (PartialAlignment.canonical_exposure_supported D a)).toOuterMeasure
        {M | (∃ c, ∀ j, OnLine (tuplePoint M T j) (g,c)) ∧
          ∃ i, tuplePoint M T i = y}).toReal ≤
      4 * (Fintype.card F : ℝ)⁻¹^5 := by
  rw [conditional_probability_eq_positionProbability T hT D a hfresh (fun p =>
    (∃ c, ∀ j, OnLine (p j) (g,c)) ∧ ∃ i, p i = y)]
  exact same_direction_contains_point_le g y

theorem conditional_tuple_through_point_hits_line_probability_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (D : Finset (Direction F))
    (a : MergedPairs F) (hfresh : ∀ i, T.generator i ∉ D)
    (g : Direction F) (y : Point F) (k : Line F) (hyk : ¬ OnLine y k) :
    (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
      (PartialAlignment.canonical_exposure_supported D a)).toOuterMeasure
        {M | (∀ j, OnLine (tuplePoint M T j) (lineThrough g y)) ∧
          ∃ i, OnLine (tuplePoint M T i) k}).toReal ≤
      4 * (Fintype.card F : ℝ)⁻¹^5 := by
  rw [conditional_probability_eq_positionProbability T hT D a hfresh (fun p =>
    (∀ j, OnLine (p j) (lineThrough g y)) ∧ ∃ i, OnLine (p i) k)]
  exact through_point_hits_line_le g y k hyk

theorem conditional_tuple_hits_two_lines_probability_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (D : Finset (Direction F))
    (a : MergedPairs F) (hfresh : ∀ i, T.generator i ∉ D)
    (g : Direction F) (l k : Line F) (hlk : l ≠ k) :
    (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
      (PartialAlignment.canonical_exposure_supported D a)).toOuterMeasure
        {M | (∃ c, ∀ j, OnLine (tuplePoint M T j) (g,c)) ∧
          ∃ i j : Fin 4, i ≠ j ∧ OnLine (tuplePoint M T i) l ∧ OnLine (tuplePoint M T j) k}).toReal ≤
      12 * (Fintype.card F : ℝ)⁻¹^5 := by
  rw [conditional_probability_eq_positionProbability T hT D a hfresh (fun p =>
    (∃ c, ∀ j, OnLine (p j) (g,c)) ∧
    ∃ i j : Fin 4, i ≠ j ∧ OnLine (p i) l ∧ OnLine (p j) k)]
  exact same_direction_hits_two_lines_le g l k hlk

end
end Balanced.CandidateFreshIncidence

end OAI
