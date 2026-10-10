import OAI.Combinatorics.BalancedRyser.Incidence.AffineIncidence
import OAI.Combinatorics.BalancedRyser.Incidence.PartialIncidence

namespace OAI

namespace Balanced.CandidatePartialPointIncidence

noncomputable section
open scoped Classical
open PartialAlignment

private theorem pmf_probability_mono {Ω : Type*} (μ : PMF Ω)
    {A B : Set Ω} (h : A ⊆ B) :
    (μ.toOuterMeasure A).toReal ≤ (μ.toOuterMeasure B).toReal := by
  have hu : μ.toOuterMeasure Set.univ = 1 :=
    (μ.toOuterMeasure_apply_eq_one_iff Set.univ).mpr (Set.subset_univ _)
  have hb : μ.toOuterMeasure B ≠ ⊤ := by
    apply ne_of_lt
    apply (μ.toOuterMeasure.mono (Set.subset_univ B)).trans_lt
    change μ.toOuterMeasure Set.univ < ⊤
    rw [hu]
    exact ENNReal.one_lt_top
  exact ENNReal.toReal_mono hb (μ.toOuterMeasure.mono h)

theorem fixedPositions_card_eq_zero_of_card_le_one (J : Finset (Fin 4))
    (hJ : J.card ≤ 1) : (fixedPositions J).card = 0 := by
  have h : ∀ K : Finset (Fin 4), K.card ≤ 1 → (fixedPositions K).card = 0 := by
    decide
  exact h J hJ

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem conditional_prescribed_line_probability_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (D : Finset (Direction F))
    (a : MergedPairs F) (hD : (exposedTupleIndices T D).card ≤ 1)
    (g : Direction F) (hg : ∀ i, T.generator i ≠ g) (c : F) :
    (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
      (canonical_exposure_supported D a)).toOuterMeasure
        {M | ∀ i, OnLine (tuplePoint M T i) (g,c)}).toReal ≤
      (Fintype.card F : ℝ)⁻¹^4 := by
  simpa only [fixedPositions_card_eq_zero_of_card_le_one _ hD, Nat.sub_zero] using
    canonical_conditional_alignment_probability_le T hT g hg c D a

theorem conditional_tuple_contains_point_probability_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (D : Finset (Direction F))
    (a : MergedPairs F) (hD : (exposedTupleIndices T D).card ≤ 1)
    (g : Direction F) (hg : ∀ i, T.generator i ≠ g) (y : Point F) :
    (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
      (canonical_exposure_supported D a)).toOuterMeasure
        {M | (∃ c, ∀ j, OnLine (tuplePoint M T j) (g,c)) ∧
          ∃ i, tuplePoint M T i = y}).toReal ≤
      (Fintype.card F : ℝ)⁻¹^4 := by
  apply le_trans (pmf_probability_mono _ (B :=
    {M | ∀ j, OnLine (tuplePoint M T j) (g, lineEval g y)}) ?_)
    (conditional_prescribed_line_probability_le T hT D a hD g hg _)
  rintro M ⟨⟨c, hc⟩, i, hi⟩ j
  have hy : lineEval g y = c := by simpa only [hi, OnLine] using hc i
  simpa only [hy] using hc j

theorem conditional_tuple_through_point_hits_line_probability_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (D : Finset (Direction F))
    (a : MergedPairs F) (hD : (exposedTupleIndices T D).card ≤ 1)
    (g : Direction F) (hg : ∀ i, T.generator i ≠ g) (y : Point F) (k : Line F) :
    (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
      (canonical_exposure_supported D a)).toOuterMeasure
        {M | (∀ j, OnLine (tuplePoint M T j) (lineThrough g y)) ∧
          ∃ i, OnLine (tuplePoint M T i) k}).toReal ≤
      (Fintype.card F : ℝ)⁻¹^4 := by
  apply le_trans (pmf_probability_mono _ (B :=
    {M | ∀ j, OnLine (tuplePoint M T j) (g, lineEval g y)}) ?_)
    (conditional_prescribed_line_probability_le T hT D a hD g hg _)
  exact fun _ h => h.1

theorem conditional_tuple_hits_line_probability_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (D : Finset (Direction F))
    (a : MergedPairs F) (hD : (exposedTupleIndices T D).card ≤ 1)
    (g : Direction F) (hg : ∀ i, T.generator i ≠ g) (L : Line F)
    (havoid : ∀ d ∈ D, ∀ b, constituent a d b ≠ L) :
    (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
      (canonical_exposure_supported D a)).toOuterMeasure
        {M | (∃ c, ∀ j, OnLine (tuplePoint M T j) (g,c)) ∧
          ∃ i, OnLine (tuplePoint M T i) L}).toReal ≤
      4 * (Fintype.card F : ℝ)⁻¹^4 := by
  by_cases htrans : g ≠ L.1
  · exact canonical_conditional_one_exposed_hit_probability_le
      T hT D a g hg hD L htrans havoid
  · have hdir : g = L.1 := by simpa only [ne_eq, not_not] using htrans
    have hb := conditional_prescribed_line_probability_le T hT D a hD g hg L.2
    have hm : (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
        (canonical_exposure_supported D a)).toOuterMeasure
        {M | (∃ c, ∀ j, OnLine (tuplePoint M T j) (g,c)) ∧
          ∃ i, OnLine (tuplePoint M T i) L}).toReal ≤
        (Fintype.card F : ℝ)⁻¹^4 := by
      apply le_trans (pmf_probability_mono _ (B :=
        {M | ∀ j, OnLine (tuplePoint M T j) (g,L.2)}) ?_) hb
      rintro M ⟨⟨c,hc⟩,i,hi⟩ j
      have heq : (g,c) = L :=
        eq_of_onLine_same_direction (tuplePoint M T i) (g,c) L hdir (hc i) hi
      have hcL : c = L.2 := congrArg Prod.snd heq
      simpa only [hcL] using hc j
    have hn : 0 ≤ (Fintype.card F : ℝ)⁻¹^4 := by positivity
    linarith

theorem conditional_tuple_hits_two_lines_probability_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (D : Finset (Direction F))
    (a : MergedPairs F) (hD : (exposedTupleIndices T D).card ≤ 1)
    (g : Direction F) (hg : ∀ i, T.generator i ≠ g) (L K : Line F)
    (havoid : ∀ d ∈ D, ∀ b, constituent a d b ≠ L) :
    (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
      (canonical_exposure_supported D a)).toOuterMeasure
        {M | (∃ c, ∀ j, OnLine (tuplePoint M T j) (g,c)) ∧
          ∃ i j : Fin 4, i ≠ j ∧ OnLine (tuplePoint M T i) L ∧
            OnLine (tuplePoint M T j) K}).toReal ≤
      4 * (Fintype.card F : ℝ)⁻¹^4 := by
  apply le_trans (pmf_probability_mono _ (B :=
    {M | (∃ c, ∀ j, OnLine (tuplePoint M T j) (g,c)) ∧
      ∃ i, OnLine (tuplePoint M T i) L}) ?_)
    (conditional_tuple_hits_line_probability_le T hT D a hD g hg L havoid)
  rintro M ⟨hc,i,j,hij,hi,hj⟩
  exact ⟨hc,i,hi⟩

end
end Balanced.CandidatePartialPointIncidence

end OAI
