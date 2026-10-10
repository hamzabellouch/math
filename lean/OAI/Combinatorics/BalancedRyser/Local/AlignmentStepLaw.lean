import OAI.Combinatorics.BalancedRyser.Local.AlignedFreeCoordinates
import OAI.Combinatorics.BalancedRyser.Local.AlignmentNoBias
import OAI.Combinatorics.BalancedRyser.Probability.FiniteConditionalRatios

namespace OAI

namespace Balanced.AlignedListProbability

open Local PartialAlignment

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem conditioned_alignment_suffix_observed {ι : Type*} [DecidableEq ι]
    (T : ι → FourTuple F) (L : ι → Line F) (post pre : List ι)
    (hT : ∀ i ∈ post ++ pre, Function.Injective (T i).generator)
    (hg : ∀ i ∈ post ++ pre, ∀ j, (T i).generator j ≠ (L i).1)
    (horder : SmallReuseOrder (fun i => generatorSet (T i)) (post ++ pre))
    (H E : MergedPairs F → Prop)
    (hH : ∀ M N, (∀ d ∈ pre.toFinset.biUnion (fun i => generatorSet (T i)),
      M d = N d) → (H M ↔ H N))
    (hE : ∀ M N, (∀ d ∈ pre.toFinset.biUnion (fun i => generatorSet (T i)),
      M d = N d) → (E M ↔ E N)) :
    conditionedOffsetProbability (fun M => ListAligned T L (post ++ pre) M ∧ H M) E =
      conditionedOffsetProbability (fun M => ListAligned T L pre M ∧ H M) E := by
  have hnum := list_alignment_append_weighted T L post pre hT hg horder
    (fun M => H M ∧ E M) (fun M N h => and_congr (hH M N h) (hE M N h))
  have hden := list_alignment_append_weighted T L post pre hT hg horder H hH
  have hn :
      offsetProbability (fun M => (ListAligned T L (post ++ pre) M ∧ H M) ∧ E M) =
        ((Fintype.card F : ℝ)⁻¹ ^ 4) ^ post.length *
          offsetProbability (fun M => (ListAligned T L pre M ∧ H M) ∧ E M) := by
    simpa only [and_assoc, and_left_comm, and_comm] using hnum
  have hd : offsetProbability (fun M => ListAligned T L (post ++ pre) M ∧ H M) =
      ((Fintype.card F : ℝ)⁻¹ ^ 4) ^ post.length *
        offsetProbability (fun M => ListAligned T L pre M ∧ H M) := by
    simpa only [and_comm] using hden
  unfold conditionedOffsetProbability
  rw [hn, hd]
  have hc : ((Fintype.card F : ℝ)⁻¹ ^ 4) ^ post.length ≠ 0 := by positivity
  exact mul_div_mul_left _ _ hc

theorem conditioned_alignment_step {ι : Type*} [DecidableEq ι]
    (T : ι → FourTuple F) (L : ι → Line F) (post pre : List ι) (i : ι)
    (hT : ∀ k ∈ post ++ i :: pre, Function.Injective (T k).generator)
    (hg : ∀ k ∈ post ++ i :: pre, ∀ j, (T k).generator j ≠ (L k).1)
    (horder : SmallReuseOrder (fun k => generatorSet (T k)) (post ++ i :: pre))
    (a : MergedPairs F) (ha : ListAligned T L pre a)
    (E : MergedPairs F → Prop)
    (hE : ∀ M N, (∀ d ∈ (i :: pre).toFinset.biUnion (fun k => generatorSet (T k)),
      M d = N d) → (E M ↔ E N)) :
    conditionedOffsetProbability
      (fun M => ListAligned T L (post ++ i :: pre) M ∧
        ∀ d ∈ pre.toFinset.biUnion (fun k => generatorSet (T k)), M d = a d) E =
    conditionedOffsetProbability
      (fun M => (∀ j, OnLine (tuplePoint M (T i) j) (L i)) ∧
        ∀ d ∈ pre.toFinset.biUnion (fun k => generatorSet (T k)), M d = a d) E := by
  let H : MergedPairs F → Prop :=
    fun M => ∀ d ∈ pre.toFinset.biUnion (fun k => generatorSet (T k)), M d = a d
  have hH (M N : MergedPairs F)
      (h : ∀ d ∈ (i :: pre).toFinset.biUnion (fun k => generatorSet (T k)),
        M d = N d) : H M ↔ H N := by
    have heq (d) (hd : d ∈ pre.toFinset.biUnion (fun k => generatorSet (T k))) :
        M d = N d := by
      apply h
      rcases Finset.mem_biUnion.mp hd with ⟨k, hk, hdk⟩
      exact Finset.mem_biUnion.mpr ⟨k, by simpa using Or.inr hk, hdk⟩
    constructor <;> intro hm d hd
    · exact (heq d hd).symm.trans (hm d hd)
    · exact (heq d hd).trans (hm d hd)
  have hs := conditioned_alignment_suffix_observed T L post (i :: pre)
    hT hg horder H E hH hE
  have hcollapse : (fun M => ListAligned T L (i :: pre) M ∧ H M) =
      (fun M => (∀ j, OnLine (tuplePoint M (T i) j) (L i)) ∧ H M) := by
    funext M
    apply propext
    constructor
    · rintro ⟨hal, hfix⟩
      exact ⟨hal i (by simp), hfix⟩
    · rintro ⟨hcur, hfix⟩
      refine ⟨?_, hfix⟩
      have hp : ListAligned T L pre M :=
        (listAligned_agree T L pre M a hfix).mpr ha
      intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · exact hcur
      · exact hp k hk
  rw [hcollapse] at hs
  exact hs

theorem current_tuple_conditional_ratio
    (T : FourTuple F) (hT : Function.Injective T.generator)
    (g : Direction F) (c : F) (D : Finset (Direction F)) (a : MergedPairs F)
    (E : (Fin 4 → Bool → F) → Prop) :
    conditionedOffsetProbability
      (fun M => (∀ d ∈ D, M d = a d) ∧ ∀ j, OnLine (tuplePoint M T j) (g,c))
      (fun M => E (fun j => M (T.generator j))) =
      ((PMF.uniformOfFintype (PartialOffsets (exposedTupleIndices T D)
        (fun j => a (T.generator j)))).toOuterMeasure
        {o | (∀ j, OnLine (TupleAlignment.tuplePositionEquiv T.generator
          (TupleAlignment.adjacent_ne_of_injective T hT) T.side o.1 j) (g,c)) ∧ E o.1}).toReal /
      ((PMF.uniformOfFintype (PartialOffsets (exposedTupleIndices T D)
        (fun j => a (T.generator j)))).toOuterMeasure
        {o | ∀ j, OnLine (TupleAlignment.tuplePositionEquiv T.generator
          (TupleAlignment.adjacent_ne_of_injective T hT) T.side o.1 j) (g,c)}).toReal := by
  let P := PartialOffsets (exposedTupleIndices T D) (fun j => a (T.generator j))
  let B : Set (Fin 4 → Bool → F) :=
    {o | ∀ j, OnLine (TupleAlignment.tuplePositionEquiv T.generator
      (TupleAlignment.adjacent_ne_of_injective T hT) T.side o j) (g,c)}
  have hm := global_exposed_tuple_law T hT D a
  rw [partialOffsets_conditional_law] at hm
  have hr := marginal_conditional_ratio (PMF.uniformOfFintype (MergedPairs F))
    ((PMF.uniformOfFintype P).map Subtype.val)
    {M | ∀ d ∈ D, M d = a d} (ConditionalRestriction.fixed_supported (fun d => d ∈ D) a)
    (fun M j => M (T.generator j)) hm B {o | E o}
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply] at hr
  have hp (K : MergedPairs F → Prop) : offsetProbability K =
      ((PMF.uniformOfFintype (MergedPairs F)).toOuterMeasure {M | K M}).toReal :=
    (FiniteUniformFibers.probability_eq_sum K).symm
  unfold conditionedOffsetProbability
  rw [hp, hp]
  simpa only [P, B, Set.preimage_ofPred_eq, ← Set.ofPred_and, and_assoc,
    tuplePoint, constituent, TupleAlignment.tuplePositionEquiv_apply] using hr

abbrev CurrentFreeCoordinates (T : FourTuple F) (D : Finset (Direction F)) :=
  {j : Fin 4 // j ∈ freePositions (exposedTupleIndices T D)} → F

def generateCurrentTupleOffsets
    (T : FourTuple F) (hT : Function.Injective T.generator)
    (g : Direction F) (hg : ∀ j, T.generator j ≠ g) (c : F)
    (D : Finset (Direction F)) (hD : (exposedTupleIndices T D).card ≤ 1)
    (a : MergedPairs F) (x : CurrentFreeCoordinates T D) : Fin 4 → Bool → F :=
  ((alignedFreeCoordinatesEquiv T.generator (TupleAlignment.adjacent_ne_of_injective T hT)
    T.side g hg c (exposedTupleIndices T D) hD (fun j => a (T.generator j))).symm x).1.1

theorem current_tuple_generated_probability
    (T : FourTuple F) (hT : Function.Injective T.generator)
    (g : Direction F) (hg : ∀ j, T.generator j ≠ g) (c : F)
    (D : Finset (Direction F)) (hD : (exposedTupleIndices T D).card ≤ 1)
    (a : MergedPairs F) (E : (Fin 4 → Bool → F) → Prop) :
    conditionedOffsetProbability
      (fun M => (∀ d ∈ D, M d = a d) ∧ ∀ j, OnLine (tuplePoint M T j) (g,c))
      (fun M => E (fun j => M (T.generator j))) =
    ((PMF.uniformOfFintype (CurrentFreeCoordinates T D)).toOuterMeasure
      {x | E (generateCurrentTupleOffsets T hT g hg c D hD a x)}).toReal := by
  rw [current_tuple_conditional_ratio T hT g c D a E]
  have hm := alignedPartial_conditional_law T.generator
    (TupleAlignment.adjacent_ne_of_injective T hT) T.side g hg c
    (exposedTupleIndices T D) hD (fun j => a (T.generator j))
  have h := congrArg (fun law => (law.toOuterMeasure {o | E o.1}).toReal) hm
  rw [filter_outer_ratio, ENNReal.toReal_div, PMF.toOuterMeasure_map_apply] at h
  exact h

omit [Field F] [Fintype F] in

theorem step_exposed_count {ι : Type*} [DecidableEq ι]
    (T : ι → FourTuple F) (post pre : List ι) (i : ι)
    (hi : Function.Injective (T i).generator)
    (horder : SmallReuseOrder (fun k => generatorSet (T k)) (post ++ i :: pre)) :
    (exposedTupleIndices (T i) (pre.toFinset.biUnion (fun k => generatorSet (T k)))).card ≤ 1 := by
  rw [card_exposedTupleIndices (T i) hi]
  exact (smallReuseOrder_suffix (fun k => generatorSet (T k)) post (i :: pre) horder).2

theorem full_aligned_step_generated_probability {ι : Type*} [DecidableEq ι]
    (T : ι → FourTuple F) (L : ι → Line F) (post pre : List ι) (i : ι)
    (hT : ∀ k ∈ post ++ i :: pre, Function.Injective (T k).generator)
    (hg : ∀ k ∈ post ++ i :: pre, ∀ j, (T k).generator j ≠ (L k).1)
    (horder : SmallReuseOrder (fun k => generatorSet (T k)) (post ++ i :: pre))
    (a : MergedPairs F) (ha : ListAligned T L pre a)
    (E : (Fin 4 → Bool → F) → Prop) :
    let D := pre.toFinset.biUnion (fun k => generatorSet (T k))
    conditionedOffsetProbability
      (fun M => ListAligned T L (post ++ i :: pre) M ∧ ∀ d ∈ D, M d = a d)
      (fun M => E (fun j => M ((T i).generator j))) =
    ((PMF.uniformOfFintype (CurrentFreeCoordinates (T i) D)).toOuterMeasure
      {x | E (generateCurrentTupleOffsets (T i) (hT i (by simp)) (L i).1
        (hg i (by simp)) (L i).2 D (step_exposed_count T post pre i (hT i (by simp)) horder)
        a x)}).toReal := by
  let D := pre.toFinset.biUnion (fun k => generatorSet (T k))
  have hE (M N : MergedPairs F)
      (h : ∀ d ∈ (i :: pre).toFinset.biUnion (fun k => generatorSet (T k)), M d = N d) :
      E (fun j => M ((T i).generator j)) ↔ E (fun j => N ((T i).generator j)) := by
    have heq : (fun j => M ((T i).generator j)) = (fun j => N ((T i).generator j)) := by
      funext j
      apply h
      exact Finset.mem_biUnion.mpr ⟨i, by simp, by simp [generatorSet]⟩
    rw [heq]
  have hs := conditioned_alignment_step T L post pre i hT hg horder a ha
    (fun M => E (fun j => M ((T i).generator j))) hE
  have hc := current_tuple_generated_probability (T i) (hT i (by simp)) (L i).1
    (hg i (by simp)) (L i).2 D (step_exposed_count T post pre i (hT i (by simp)) horder) a E
  exact hs.trans (by simpa only [and_comm, Prod.eta] using hc)

end
end Balanced.AlignedListProbability

end OAI
