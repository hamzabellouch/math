import Mathlib.Data.Fintype.BigOperators
import OAI.Combinatorics.BalancedRyser.Incidence.AffineIncidence
import OAI.Combinatorics.BalancedRyser.Local.GlobalPartialAlignment

namespace OAI

namespace Balanced.PartialAlignment
open TupleAlignment
noncomputable section
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] in
private theorem card_fixed_function_coordinate {ι : Type*} [Fintype ι]
    [DecidableEq ι] (i : ι) (x : F) :
    Fintype.card {f : ι → F // f i = x} =
      Fintype.card F ^ (Fintype.card ι - 1) := by
  rw [Fintype.card_subtype]
  simpa only [Fintype.piFinset_univ, Finset.card_univ] using
    Fintype.card_filter_piFinset_const_eq_of_mem (Finset.univ : Finset F) i
      (Finset.mem_univ x)

abbrev MarkedPartialOffsets (d : Fin 4 → Direction F)
    (hd : ∀ j, d j ≠ d (j + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (c : F) (J : Finset (Fin 4)) (a : Fin 4 → Bool → F)
    (i : Fin 4) (y : Point F) :=
  {o : PartialOffsets J a //
    (∀ j, OnLine (tuplePositionEquiv d hd σ o.1 j) (g,c)) ∧
      tuplePositionEquiv d hd σ o.1 i = y}

theorem card_markedPartialOffsets_le (d : Fin 4 → Direction F)
    (hd : ∀ j, d j ≠ d (j + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : ∀ j, d j ≠ g) (c : F)
    (J : Finset (Fin 4)) (a : Fin 4 → Bool → F)
    (i : Fin 4) (hi : i ∈ freePositions J) (y : Point F) :
    Fintype.card (MarkedPartialOffsets d hd σ g c J a i y) ≤
      Fintype.card F ^ ((freePositions J).card - 1) := by
  classical
  by_cases hy : OnLine y (g,c)
  · let coord : F := (linePointEquiv g c) ⟨y,hy⟩
    let k : {j : Fin 4 // j ∈ freePositions J} := ⟨i,hi⟩
    let record : MarkedPartialOffsets d hd σ g c J a i y →
        {f : {j : Fin 4 // j ∈ freePositions J} → F // f k = coord} := fun o =>
      ⟨alignedFreeCoordinates d hd σ g c J a ⟨o.1,o.2.1⟩, by
        change (linePointEquiv g c)
          ⟨tuplePositionEquiv d hd σ o.1.1 i, o.2.1 i⟩ = coord
        apply congrArg (linePointEquiv g c)
        exact Subtype.ext o.2.2⟩
    have hinj : Function.Injective record := by
      intro o p h
      have hcoords := congrArg Subtype.val h
      have hpartial := alignedFreeCoordinates_injective d hd σ g hg c J a hcoords
      exact Subtype.ext (congrArg
        (fun z : AlignedPartialOffsets d hd σ g c J a => z.1) hpartial)
    calc
      _ ≤ Fintype.card
          {f : {j : Fin 4 // j ∈ freePositions J} → F // f k = coord} :=
        Fintype.card_le_of_injective record hinj
      _ = _ := by rw [card_fixed_function_coordinate]; simp
  · let : IsEmpty (MarkedPartialOffsets d hd σ g c J a i y) :=
      ⟨fun o => hy (o.2.2 ▸ o.2.1 i)⟩
    rw [Fintype.card_of_isEmpty]
    exact Nat.zero_le _

theorem partial_marked_alignment_probability_le (d : Fin 4 → Direction F)
    (hd : ∀ j, d j ≠ d (j + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : ∀ j, d j ≠ g) (c : F)
    (J : Finset (Fin 4)) (a : Fin 4 → Bool → F)
    (i : Fin 4) (hi : i ∈ freePositions J) (y : Point F) :
    ((PMF.uniformOfFintype (PartialOffsets J a)).toOuterMeasure
      {o | (∀ j, OnLine (tuplePositionEquiv d hd σ o.1 j) (g,c)) ∧
        tuplePositionEquiv d hd σ o.1 i = y}).toReal ≤
      (Fintype.card F : ℝ)⁻¹ ^ (5 - (fixedPositions J).card) := by
  rw [PMF.toOuterMeasure_uniformOfFintype_apply, ENNReal.toReal_div]
  simp only [ENNReal.toReal_natCast]
  change (Fintype.card (MarkedPartialOffsets d hd σ g c J a i y) : ℝ) /
    (Fintype.card (PartialOffsets J a) : ℝ) ≤ _
  rw [card_partialOffsets, Nat.cast_pow]
  have hcard : (Fintype.card (MarkedPartialOffsets d hd σ g c J a i y) : ℝ) ≤
      (Fintype.card F : ℝ) ^ ((freePositions J).card - 1) := by
    exact_mod_cast card_markedPartialOffsets_le d hd σ g hg c J a i hi y
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hfree : 0 < (freePositions J).card := Finset.card_pos.mpr ⟨i,hi⟩
  have hfixed : (fixedPositions J).card ≤ 4 := by
    simpa only [Fintype.card_fin] using (fixedPositions J).card_le_univ
  have hexp : ((freePositions J).card - 1) + (5 - (fixedPositions J).card) =
      2 * (freshGenerators J).card := by
    have := alignment_exponent_identity J
    omega
  calc
    _ ≤ (Fintype.card F : ℝ) ^ ((freePositions J).card - 1) /
        (Fintype.card F : ℝ) ^ (2 * (freshGenerators J).card) :=
      div_le_div_of_nonneg_right hcard (by positivity)
    _ = _ := by
      rw [← hexp, pow_add, div_mul_eq_div_div, div_self (pow_ne_zero _ hq),
        one_div, inv_pow]

theorem original_conditional_marked_alignment_probability_le
    (d : Fin 4 → Direction F) (hd : ∀ j, d j ≠ d (j + 1))
    (σ : Fin 4 → Bool) (g : Direction F) (hg : ∀ j, d j ≠ g) (c : F)
    (J : Finset (Fin 4)) (a : Fin 4 → Bool → F)
    (i : Fin 4) (hi : i ∈ freePositions J) (y : Point F) :
    (((PMF.uniformOfFintype (Fin 4 → Bool → F)).filter
      {o | ∀ j ∈ J, o j = a j} (partialOffsets_supported J a)).toOuterMeasure
      {o | (∀ j, OnLine (tuplePositionEquiv d hd σ o j) (g,c)) ∧
        tuplePositionEquiv d hd σ o i = y}).toReal ≤
      (Fintype.card F : ℝ)⁻¹ ^ (5 - (fixedPositions J).card) := by
  rw [partialOffsets_conditional_law, PMF.toOuterMeasure_map_apply]
  exact partial_marked_alignment_probability_le d hd σ g hg c J a i hi y

theorem canonical_conditional_marked_alignment_probability_le
    (T : FourTuple F) (hT : Function.Injective T.generator)
    (g : Direction F) (hg : ∀ j, T.generator j ≠ g) (c : F)
    (D : Finset (Direction F)) (a : MergedPairs F)
    (i : Fin 4) (hi : i ∈ freePositions (exposedTupleIndices T D)) (y : Point F) :
    (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
      (canonical_exposure_supported D a)).toOuterMeasure
      {M | (∀ j, OnLine (tuplePoint M T j) (g,c)) ∧
        tuplePoint M T i = y}).toReal ≤
      (Fintype.card F : ℝ)⁻¹ ^ (5 - (fixedPositions (exposedTupleIndices T D)).card) := by
  let hd := adjacent_ne_of_injective T hT
  let E : Set (Fin 4 → Bool → F) := {o |
    (∀ j, OnLine (tuplePositionEquiv T.generator hd T.side o j) (g,c)) ∧
      tuplePositionEquiv T.generator hd T.side o i = y}
  have h := congrArg (fun law => (law.toOuterMeasure E).toReal)
    (global_exposed_tuple_law T hT D a)
  rw [PMF.toOuterMeasure_map_apply] at h
  have hle := original_conditional_marked_alignment_probability_le
    T.generator hd T.side g hg c (exposedTupleIndices T D)
      (fun j => a (T.generator j)) i hi y
  have hresult := h.trans_le hle
  simpa only [offsetLaw_eq_uniform, E, Set.preimage_ofPred_eq,
    tuplePositionEquiv_apply, tuplePoint, constituent] using hresult

theorem canonical_conditional_transverse_hit_probability_le
    (T : FourTuple F) (hT : Function.Injective T.generator)
    (g : Direction F) (hg : ∀ j, T.generator j ≠ g) (c : F)
    (D : Finset (Direction F)) (a : MergedPairs F)
    (i : Fin 4) (hi : i ∈ freePositions (exposedTupleIndices T D))
    (L : Line F) (htrans : g ≠ L.1) :
    (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
      (canonical_exposure_supported D a)).toOuterMeasure
      {M | (∀ j, OnLine (tuplePoint M T j) (g,c)) ∧
        OnLine (tuplePoint M T i) L}).toReal ≤
      (Fintype.card F : ℝ)⁻¹ ^ (5 - (fixedPositions (exposedTupleIndices T D)).card) := by
  have hevent : {M : MergedPairs F |
      (∀ j, OnLine (tuplePoint M T j) (g,c)) ∧ OnLine (tuplePoint M T i) L} =
      {M | (∀ j, OnLine (tuplePoint M T j) (g,c)) ∧
        tuplePoint M T i = lineIntersection (g,c) L} := by
    ext M
    constructor
    · intro h
      refine ⟨h.1, ?_⟩
      exact common_point_eq_of_lines_ne (g,c) L
        (fun heq => htrans (congrArg Prod.fst heq))
        (tuplePoint M T i) (lineIntersection (g,c) L) (h.1 i) h.2
        (onLine_lineIntersection_left _ _ htrans)
        (onLine_lineIntersection_right _ _ htrans)
    · intro h
      refine ⟨h.1, ?_⟩
      rw [h.2]
      exact onLine_lineIntersection_right _ _ htrans
  rw [hevent]
  exact canonical_conditional_marked_alignment_probability_le T hT g hg c D a i hi _

private theorem pmf_outer_ne_top {α : Type*} (p : PMF α) (E : Set α) :
    p.toOuterMeasure E ≠ ⊤ := by
  have h : p.toOuterMeasure E ≤ 1 := by
    calc
      _ ≤ p.toOuterMeasure Set.univ := p.toOuterMeasure.mono (Set.subset_univ _)
      _ = 1 := by simp [PMF.toOuterMeasure_apply]
  exact ne_of_lt (h.trans_lt (by simp))

private theorem pmf_real_mono {α : Type*} (p : PMF α) {E G : Set α}
    (h : E ⊆ G) : (p.toOuterMeasure E).toReal ≤ (p.toOuterMeasure G).toReal :=
  ENNReal.toReal_mono (pmf_outer_ne_top p G) (p.toOuterMeasure.mono h)

def conditionalHitProbability (T : FourTuple F) (D : Finset (Direction F))
    (a : MergedPairs F) (g : Direction F) (i : Fin 4) (L : Line F) (c : F) : ℝ :=
  (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
    (canonical_exposure_supported D a)).toOuterMeasure
    {M | (∀ j, OnLine (tuplePoint M T j) (g,c)) ∧ OnLine (tuplePoint M T i) L}).toReal

theorem conditionalHitProbability_le_alignment (T : FourTuple F)
    (hT : Function.Injective T.generator) (D : Finset (Direction F))
    (a : MergedPairs F) (g : Direction F) (hg : ∀ j, T.generator j ≠ g)
    (i : Fin 4) (L : Line F) (c : F) :
    conditionalHitProbability T D a g i L c ≤
      (Fintype.card F : ℝ)⁻¹ ^ (4 - (fixedPositions (exposedTupleIndices T D)).card) := by
  exact (pmf_real_mono _ (fun _ h => h.1)).trans
    (canonical_conditional_alignment_probability_le T hT g hg c D a)

def possibleHitOffsets (T : FourTuple F) (D : Finset (Direction F))
    (a : MergedPairs F) (g : Direction F) (i : Fin 4) (L : Line F) : Finset F :=
  Finset.univ.filter (fun c => ∃ M : MergedPairs F,
    (∀ d, d ∈ D → M d = a d) ∧
    (∀ j, OnLine (tuplePoint M T j) (g,c)) ∧ OnLine (tuplePoint M T i) L)

theorem card_possibleHitOffsets_le_one (T : FourTuple F)
    (hT : Function.Injective T.generator) (D : Finset (Direction F))
    (a : MergedPairs F) (g : Direction F) (i : Fin 4) (L : Line F)
    (hincident : T.generator i ∈ D ∨ T.generator (i + 1) ∈ D)
    (havoid : ∀ d ∈ D, ∀ b, constituent a d b ≠ L) :
    (possibleHitOffsets T D a g i L).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro c hc e he
  obtain ⟨M,hM,hMc,hML⟩ := (Finset.mem_filter.mp hc).2
  obtain ⟨N,hN,hNe,hNL⟩ := (Finset.mem_filter.mp he).2
  have hpoints : tuplePoint M T i = tuplePoint N T i := by
    rcases hincident with hi | hi
    · have hm : OnLine (tuplePoint M T i)
          (constituent a (T.generator i) (T.side i)) := by
        have h := onLine_lineIntersection_left
          (constituent M (T.generator i) (T.side i))
          (constituent M (T.generator (i + 1)) (!(T.side (i + 1))))
          (adjacent_ne_of_injective T hT i)
        simpa only [tuplePoint, constituent, hM _ hi] using h
      have hn : OnLine (tuplePoint N T i)
          (constituent a (T.generator i) (T.side i)) := by
        have h := onLine_lineIntersection_left
          (constituent N (T.generator i) (T.side i))
          (constituent N (T.generator (i + 1)) (!(T.side (i + 1))))
          (adjacent_ne_of_injective T hT i)
        simpa only [tuplePoint, constituent, hN _ hi] using h
      exact common_point_eq_of_lines_ne _ L (havoid _ hi _) _ _ hm hML hn hNL
    · have hm : OnLine (tuplePoint M T i)
          (constituent a (T.generator (i + 1)) (!(T.side (i + 1)))) := by
        have h := onLine_lineIntersection_right
          (constituent M (T.generator i) (T.side i))
          (constituent M (T.generator (i + 1)) (!(T.side (i + 1))))
          (adjacent_ne_of_injective T hT i)
        simpa only [tuplePoint, constituent, hM _ hi] using h
      have hn : OnLine (tuplePoint N T i)
          (constituent a (T.generator (i + 1)) (!(T.side (i + 1)))) := by
        have h := onLine_lineIntersection_right
          (constituent N (T.generator i) (T.side i))
          (constituent N (T.generator (i + 1)) (!(T.side (i + 1))))
          (adjacent_ne_of_injective T hT i)
        simpa only [tuplePoint, constituent, hN _ hi] using h
      exact common_point_eq_of_lines_ne _ L (havoid _ hi _) _ _ hm hML hn hNL
  exact (hMc i).symm.trans ((congrArg (lineEval g) hpoints).trans (hNe i))

theorem conditionalHitProbability_eq_zero_of_not_possible (T : FourTuple F)
    (D : Finset (Direction F)) (a : MergedPairs F)
    (g : Direction F) (i : Fin 4) (L : Line F) (c : F)
    (hc : c ∉ possibleHitOffsets T D a g i L) :
    conditionalHitProbability T D a g i L c = 0 := by
  unfold conditionalHitProbability
  have hz : ((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
      (canonical_exposure_supported D a)).toOuterMeasure
      {M | (∀ j, OnLine (tuplePoint M T j) (g,c)) ∧
        OnLine (tuplePoint M T i) L} = 0 := by
    apply (PMF.toOuterMeasure_apply_eq_zero_iff _ _).mpr
    apply Set.disjoint_left.mpr
    intro M hM hE
    have hexposed := (PMF.mem_support_filter_iff _).mp hM
    exact hc (Finset.mem_filter.mpr ⟨Finset.mem_univ _, M, hexposed.1, hE⟩)
  rw [hz, ENNReal.toReal_zero]

private theorem fixedPositions_card_zero_of_le_one (J : Finset (Fin 4))
    (hJ : J.card ≤ 1) : (fixedPositions J).card = 0 := by
  have h : ∀ J : Finset (Fin 4), J.card ≤ 1 → (fixedPositions J).card = 0 := by decide
  exact h J hJ

theorem sum_conditionalHitProbability_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (D : Finset (Direction F))
    (a : MergedPairs F) (g : Direction F) (hg : ∀ j, T.generator j ≠ g)
    (hsmall : (exposedTupleIndices T D).card ≤ 1)
    (i : Fin 4) (L : Line F) (htrans : g ≠ L.1)
    (havoid : ∀ d ∈ D, ∀ b, constituent a d b ≠ L) :
    (∑ c : F, conditionalHitProbability T D a g i L c) ≤
      (Fintype.card F : ℝ)⁻¹ ^ 4 := by
  have hfixed := fixedPositions_card_zero_of_le_one (exposedTupleIndices T D) hsmall
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  by_cases hfree : i ∈ freePositions (exposedTupleIndices T D)
  · calc
      _ ≤ ∑ _c : F, (Fintype.card F : ℝ)⁻¹ ^ 5 := by
        apply Finset.sum_le_sum
        intro c _
        simpa only [conditionalHitProbability, hfixed, Nat.sub_zero] using
          canonical_conditional_transverse_hit_probability_le T hT g hg c D a i hfree L htrans
      _ = (Fintype.card F : ℝ) * (Fintype.card F : ℝ)⁻¹ ^ 5 := by simp
      _ = _ := by field_simp
  · have hincident : T.generator i ∈ D ∨ T.generator (i + 1) ∈ D := by
      by_contra h
      push Not at h
      apply hfree
      simp [freePositions, exposedTupleIndices, h.1, h.2]
    have hcount := card_possibleHitOffsets_le_one T hT D a g i L hincident havoid
    have hsum : (∑ c ∈ possibleHitOffsets T D a g i L,
        conditionalHitProbability T D a g i L c) =
        ∑ c : F, conditionalHitProbability T D a g i L c := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro c _ hc
      exact conditionalHitProbability_eq_zero_of_not_possible T D a g i L c hc
    rw [← hsum]
    calc
      _ ≤ ∑ _c ∈ possibleHitOffsets T D a g i L, (Fintype.card F : ℝ)⁻¹ ^ 4 := by
        apply Finset.sum_le_sum
        intro c _
        simpa only [hfixed, Nat.sub_zero] using
          conditionalHitProbability_le_alignment T hT D a g hg i L c
      _ = ((possibleHitOffsets T D a g i L).card : ℝ) *
          (Fintype.card F : ℝ)⁻¹ ^ 4 := by simp
      _ ≤ 1 * (Fintype.card F : ℝ)⁻¹ ^ 4 :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) (by positivity)
      _ = _ := one_mul _

private theorem pmf_real_iUnion_le {α ι : Type*} [Fintype ι]
    (p : PMF α) (E : ι → Set α) :
    (p.toOuterMeasure (⋃ i, E i)).toReal ≤ ∑ i, (p.toOuterMeasure (E i)).toReal := by
  have htop : (∑ i, p.toOuterMeasure (E i)) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun i _ => pmf_outer_ne_top p (E i))
  have h := ENNReal.toReal_mono htop
    (MeasureTheory.measure_iUnion_fintype_le p.toOuterMeasure E)
  rw [ENNReal.toReal_sum (fun i _ => pmf_outer_ne_top p (E i))] at h
  exact h

theorem sum_conditional_any_hit_probability_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (D : Finset (Direction F))
    (a : MergedPairs F) (g : Direction F) (hg : ∀ j, T.generator j ≠ g)
    (hsmall : (exposedTupleIndices T D).card ≤ 1)
    (L : Line F) (htrans : g ≠ L.1)
    (havoid : ∀ d ∈ D, ∀ b, constituent a d b ≠ L) :
    (∑ c : F,
      (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
        (canonical_exposure_supported D a)).toOuterMeasure
        {M | (∀ j, OnLine (tuplePoint M T j) (g,c)) ∧
          ∃ i, OnLine (tuplePoint M T i) L}).toReal) ≤
      4 * (Fintype.card F : ℝ)⁻¹ ^ 4 := by
  calc
    _ ≤ ∑ c : F, ∑ i : Fin 4, conditionalHitProbability T D a g i L c := by
      apply Finset.sum_le_sum
      intro c _
      have hevent : {M : MergedPairs F |
          (∀ j, OnLine (tuplePoint M T j) (g,c)) ∧ ∃ i, OnLine (tuplePoint M T i) L} =
          ⋃ i : Fin 4, {M | (∀ j, OnLine (tuplePoint M T j) (g,c)) ∧
            OnLine (tuplePoint M T i) L} := by
        ext M
        simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
        constructor
        · rintro ⟨ha,i,hi⟩
          exact ⟨i,ha,hi⟩
        · rintro ⟨i,ha,hi⟩
          exact ⟨ha,i,hi⟩
      rw [hevent]
      exact pmf_real_iUnion_le _ _
    _ = ∑ i : Fin 4, ∑ c : F, conditionalHitProbability T D a g i L c :=
      Finset.sum_comm
    _ ≤ ∑ _i : Fin 4, (Fintype.card F : ℝ)⁻¹ ^ 4 := by
      apply Finset.sum_le_sum
      intro i _
      exact sum_conditionalHitProbability_le T hT D a g hg hsmall i L htrans havoid
    _ = _ := by simp

theorem canonical_conditional_one_exposed_hit_probability_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (D : Finset (Direction F))
    (a : MergedPairs F) (g : Direction F) (hg : ∀ j, T.generator j ≠ g)
    (hsmall : (exposedTupleIndices T D).card ≤ 1)
    (L : Line F) (htrans : g ≠ L.1)
    (havoid : ∀ d ∈ D, ∀ b, constituent a d b ≠ L) :
    (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
      (canonical_exposure_supported D a)).toOuterMeasure
      {M | (∃ c, ∀ j, OnLine (tuplePoint M T j) (g,c)) ∧
        ∃ i, OnLine (tuplePoint M T i) L}).toReal ≤
      4 * (Fintype.card F : ℝ)⁻¹ ^ 4 := by
  have hevent : {M : MergedPairs F |
      (∃ c, ∀ j, OnLine (tuplePoint M T j) (g,c)) ∧ ∃ i, OnLine (tuplePoint M T i) L} =
      ⋃ c : F, {M | (∀ j, OnLine (tuplePoint M T j) (g,c)) ∧
        ∃ i, OnLine (tuplePoint M T i) L} := by
    ext M
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨⟨c,hc⟩,hi⟩
      exact ⟨c,hc,hi⟩
    · rintro ⟨c,hc,hi⟩
      exact ⟨⟨c,hc⟩,hi⟩
  rw [hevent]
  exact (pmf_real_iUnion_le _ _).trans
    (sum_conditional_any_hit_probability_le T hT D a g hg hsmall L htrans havoid)

end
end Balanced.PartialAlignment

end OAI
