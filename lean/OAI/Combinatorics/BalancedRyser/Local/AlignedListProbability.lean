import OAI.Combinatorics.BalancedRyser.Local.GlobalPartialAlignment
import OAI.Combinatorics.BalancedRyser.Local.Local
import OAI.Combinatorics.BalancedRyser.Local.LowReuseOrder
import OAI.Combinatorics.BalancedRyser.Probability.FiniteUniformFibers

namespace OAI

namespace Balanced.AlignedListProbability

open TupleAlignment PartialAlignment ConditionalRestriction
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem partial_alignment_probability_eq (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : ∀ i, d i ≠ g) (c : F)
    (J : Finset (Fin 4)) (hJ : J.card ≤ 1) (a : Fin 4 → Bool → F) :
    ((PMF.uniformOfFintype (PartialOffsets J a)).toOuterMeasure
      {o | ∀ i, OnLine (tuplePositionEquiv d hd σ o.1 i) (g,c)}).toReal =
      (Fintype.card F : ℝ)⁻¹ ^ 4 := by
  rcases J.eq_empty_or_nonempty with rfl | ⟨j, hj⟩
  · let e : PartialOffsets ∅ a ≃ (Fin 4 → Bool → F) :=
      Equiv.subtypeUnivEquiv (by simp)
    have h := congrArg (fun law => (law.toOuterMeasure
      {o | ∀ i, OnLine (tuplePositionEquiv d hd σ o i) (g,c)}).toReal)
      (uniform_map_equiv e)
    rw [PMF.toOuterMeasure_map_apply] at h
    exact h.trans (alignedOffsets_outer_probability d hd σ g c)
  · have heq : J = {j} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      exact ⟨hj, fun k hk => Finset.card_le_one.mp hJ k hk j hj⟩
    subst J
    let e : PartialOffsets {j} a ≃ ChildOffsetsAt j (a j) :=
      Equiv.subtypeEquivRight (by intro o; simp)
    have h := congrArg (fun law => (law.toOuterMeasure
      {o : ChildOffsetsAt j (a j) |
        ∀ i, OnLine (tuplePositionEquiv d hd σ o.1 i) (g,c)}).toReal)
      (uniform_map_equiv e)
    rw [PMF.toOuterMeasure_map_apply] at h
    exact h.trans (alignedChildOffsetsAt_pmf_probability d hd σ g j (hg j) c (a j))

theorem global_conditional_alignment_probability_eq (T : FourTuple F)
    (hT : Function.Injective T.generator) (g : Direction F)
    (hg : ∀ i, T.generator i ≠ g) (c : F)
    (D : Finset (Direction F)) (hD : (exposedTupleIndices T D).card ≤ 1)
    (a : MergedPairs F) :
    (((PMF.uniformOfFintype (MergedPairs F)).filter {M | ∀ d, d ∈ D → M d = a d}
      (fixed_supported (fun d => d ∈ D) a)).toOuterMeasure
      {M | ∀ i, OnLine (tuplePoint M T i) (g,c)}).toReal =
      (Fintype.card F : ℝ)⁻¹ ^ 4 := by
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
    _ = _ := by
      rw [partialOffsets_conditional_law, PMF.toOuterMeasure_map_apply]
      exact partial_alignment_probability_eq T.generator hd T.side g hg c
        (exposedTupleIndices T D) hD (fun i => a (T.generator i))

theorem canonical_conditional_alignment_probability_eq (T : FourTuple F)
    (hT : Function.Injective T.generator) (g : Direction F)
    (hg : ∀ i, T.generator i ≠ g) (c : F)
    (D : Finset (Direction F)) (hD : (exposedTupleIndices T D).card ≤ 1)
    (a : MergedPairs F) :
    (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
      (canonical_exposure_supported D a)).toOuterMeasure
      {M | ∀ i, OnLine (tuplePoint M T i) (g,c)}).toReal =
      (Fintype.card F : ℝ)⁻¹ ^ 4 := by
  simpa only [offsetLaw_eq_uniform] using
    global_conditional_alignment_probability_eq T hT g hg c D hD a

omit [Field F] [Fintype F] in

theorem card_exposedTupleIndices (T : FourTuple F)
    (hT : Function.Injective T.generator) (D : Finset (Direction F)) :
    (exposedTupleIndices T D).card = (generatorSet T ∩ D).card := by
  have heq : (exposedTupleIndices T D).image T.generator = generatorSet T ∩ D := by
    ext d
    simp only [exposedTupleIndices, generatorSet, Finset.mem_image,
      Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, rfl⟩, hi⟩
    · rintro ⟨⟨i, rfl⟩, hi⟩
      exact ⟨i, hi, rfl⟩
  rw [← heq, Finset.card_image_of_injective _ hT]

omit [Fintype F] in

theorem tuplePoint_eq_of_agree (T : FourTuple F) (M N : MergedPairs F)
    (h : ∀ d ∈ generatorSet T, M d = N d) (j : Fin 4) :
    tuplePoint M T j = tuplePoint N T j := by
  have hj : T.generator j ∈ generatorSet T := by simp [generatorSet]
  have hn : T.generator (j+1) ∈ generatorSet T := by simp [generatorSet]
  simp only [tuplePoint, constituent, h _ hj, h _ hn]

def ListAligned {ι : Type*} (T : ι → FourTuple F) (L : ι → Line F)
    (l : List ι) (M : MergedPairs F) : Prop :=
  ∀ i ∈ l, ∀ j, OnLine (tuplePoint M (T i) j) (L i)

omit [Fintype F] in
theorem listAligned_agree {ι : Type*} [DecidableEq ι]
    (T : ι → FourTuple F) (L : ι → Line F) (l : List ι)
    (M N : MergedPairs F)
    (h : ∀ d ∈ l.toFinset.biUnion (fun i => generatorSet (T i)), M d = N d) :
    ListAligned T L l M ↔ ListAligned T L l N := by
  have hp (i : ι) (hi : i ∈ l) (j : Fin 4) :
      tuplePoint M (T i) j = tuplePoint N (T i) j := by
    apply tuplePoint_eq_of_agree
    intro d hd
    exact h d (Finset.mem_biUnion.mpr ⟨i, List.mem_toFinset.mpr hi, hd⟩)
  constructor <;> intro ha i hi j
  · rw [← hp i hi j]
    exact ha i hi j
  · rw [hp i hi j]
    exact ha i hi j

theorem fixed_alignment_probability_eq (T : FourTuple F)
    (hT : Function.Injective T.generator) (g : Direction F)
    (hg : ∀ i, T.generator i ≠ g) (c : F)
    (D : Finset (Direction F)) (hD : (exposedTupleIndices T D).card ≤ 1)
    (a : MergedPairs F) :
    ((PMF.uniformOfFintype (FixedArray (fun d => d ∈ D) a)).toOuterMeasure
      {M | ∀ j, OnLine (tuplePoint M.1 T j) (g,c)}).toReal =
        (Fintype.card F : ℝ)⁻¹ ^ 4 := by
  have h := global_conditional_alignment_probability_eq T hT g hg c D hD a
  rw [uniform_fixed_filter, PMF.toOuterMeasure_map_apply] at h
  convert h using 1
  exact FiniteUniformFibers.probability_fintype_congr _ _ rfl

theorem alignment_inter_probability_eq (T : FourTuple F)
    (hT : Function.Injective T.generator) (g : Direction F)
    (hg : ∀ i, T.generator i ≠ g) (c : F)
    (D : Finset (Direction F)) (hD : (exposedTupleIndices T D).card ≤ 1)
    (E : MergedPairs F → Prop)
    (hE : ∀ M N, (∀ d ∈ D, M d = N d) → (E M ↔ E N)) :
    ((PMF.uniformOfFintype (MergedPairs F)).toOuterMeasure
      {M | E M ∧ ∀ j, OnLine (tuplePoint M T j) (g,c)}).toReal =
      (Fintype.card F : ℝ)⁻¹ ^ 4 *
        ((PMF.uniformOfFintype (MergedPairs F)).toOuterMeasure {M | E M}).toReal := by
  apply FiniteUniformFibers.fixed_probability_inter D E _ _ hE
  intro a
  convert fixed_alignment_probability_eq T hT g hg c D hD a using 1
  exact FiniteUniformFibers.probability_fintype_congr _ _ rfl

theorem list_alignment_probability {ι : Type*} [DecidableEq ι]
    (T : ι → FourTuple F) (L : ι → Line F) (l : List ι)
    (hT : ∀ i ∈ l, Function.Injective (T i).generator)
    (hg : ∀ i ∈ l, ∀ j, (T i).generator j ≠ (L i).1)
    (horder : SmallReuseOrder (fun i => generatorSet (T i)) l) :
    ((PMF.uniformOfFintype (MergedPairs F)).toOuterMeasure
      {M | ListAligned T L l M}).toReal =
      ((Fintype.card F : ℝ)⁻¹ ^ 4) ^ l.length := by
  induction l with
  | nil =>
      simp [ListAligned]
  | cons i l ih =>
      have hTi := hT i (by simp)
      have hgi := hg i (by simp)
      have htailT : ∀ j ∈ l, Function.Injective (T j).generator :=
        fun j hj => hT j (by simp [hj])
      have htailg : ∀ j ∈ l, ∀ k, (T j).generator k ≠ (L j).1 :=
        fun j hj => hg j (by simp [hj])
      have hD : (exposedTupleIndices (T i)
          (l.toFinset.biUnion (fun j => generatorSet (T j)))).card ≤ 1 := by
        rw [card_exposedTupleIndices (T i) hTi]
        exact horder.2
      have hevent : {M | ListAligned T L (i :: l) M} =
          {M | ListAligned T L l M ∧ ∀ j, OnLine (tuplePoint M (T i) j) (L i)} := by
        ext M
        simp only [ListAligned, List.mem_cons, forall_eq_or_imp, Set.mem_ofPred_eq]
        exact and_comm
      rw [hevent]
      have hstep := alignment_inter_probability_eq (T i) hTi (L i).1 hgi (L i).2
        (l.toFinset.biUnion (fun j => generatorSet (T j))) hD (ListAligned T L l)
        (listAligned_agree T L l)
      simpa only [Prod.eta, ih htailT htailg horder.1, List.length_cons,
        pow_succ, mul_comm] using hstep

end
end Balanced.AlignedListProbability

end OAI
