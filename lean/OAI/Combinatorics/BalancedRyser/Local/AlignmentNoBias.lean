import OAI.Combinatorics.BalancedRyser.Local.AlignmentNormalization

namespace OAI

namespace Balanced.AlignedListProbability

open Local PartialAlignment
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private theorem offsetProbability_eq_uniform (E : MergedPairs F → Prop) :
    offsetProbability E =
      ((PMF.uniformOfFintype (MergedPairs F)).toOuterMeasure {M | E M}).toReal :=
  (FiniteUniformFibers.probability_eq_sum E).symm

theorem smallReuseOrder_suffix {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (A : ι → Finset α) (post pre : List ι)
    (h : SmallReuseOrder A (post ++ pre)) : SmallReuseOrder A pre := by
  induction post with
  | nil => exact h
  | cons i post ih => exact ih h.1

theorem list_offset_alignment_probability {ι : Type*} [DecidableEq ι]
    (T : ι → FourTuple F) (L : ι → Line F) (l : List ι)
    (hT : ∀ i ∈ l, Function.Injective (T i).generator)
    (hg : ∀ i ∈ l, ∀ j, (T i).generator j ≠ (L i).1)
    (horder : SmallReuseOrder (fun i => generatorSet (T i)) l) :
    offsetProbability (ListAligned T L l) =
      ((Fintype.card F : ℝ)⁻¹ ^ 4) ^ l.length := by
  rw [offsetProbability_eq_uniform]
  exact list_alignment_probability T L l hT hg horder

theorem list_alignment_append_weighted {ι : Type*} [DecidableEq ι]
    (T : ι → FourTuple F) (L : ι → Line F) (post pre : List ι)
    (hT : ∀ i ∈ post ++ pre, Function.Injective (T i).generator)
    (hg : ∀ i ∈ post ++ pre, ∀ j, (T i).generator j ≠ (L i).1)
    (horder : SmallReuseOrder (fun i => generatorSet (T i)) (post ++ pre))
    (E : MergedPairs F → Prop)
    (hE : ∀ M N, (∀ d ∈ pre.toFinset.biUnion (fun i => generatorSet (T i)),
      M d = N d) → (E M ↔ E N)) :
    offsetProbability (fun M => E M ∧ ListAligned T L (post ++ pre) M) =
      ((Fintype.card F : ℝ)⁻¹ ^ 4) ^ post.length *
        offsetProbability (fun M => E M ∧ ListAligned T L pre M) := by
  induction post with
  | nil => simp
  | cons i post ih =>
      have hTi := hT i (by simp)
      have hgi := hg i (by simp)
      have htailT : ∀ j ∈ post ++ pre, Function.Injective (T j).generator :=
        fun j hj => hT j (by simpa using Or.inr hj)
      have htailg : ∀ j ∈ post ++ pre, ∀ k, (T j).generator k ≠ (L j).1 :=
        fun j hj => hg j (by simpa using Or.inr hj)
      let D := (post ++ pre).toFinset.biUnion (fun j => generatorSet (T j))
      have hD : (exposedTupleIndices (T i) D).card ≤ 1 := by
        rw [card_exposedTupleIndices (T i) hTi]
        exact horder.2
      have hpre : pre.toFinset.biUnion (fun j => generatorSet (T j)) ⊆ D := by
        apply Finset.biUnion_subset_biUnion_of_subset_left
        simp only [List.toFinset_append]
        exact Finset.subset_union_right
      have hconst (M N : MergedPairs F) (hMN : ∀ d ∈ D, M d = N d) :
          (E M ∧ ListAligned T L (post ++ pre) M) ↔
            (E N ∧ ListAligned T L (post ++ pre) N) :=
        and_congr (hE M N (fun d hd => hMN d (hpre hd)))
          (listAligned_agree T L (post ++ pre) M N hMN)
      have hstep := alignment_inter_probability_eq (T i) hTi (L i).1 hgi (L i).2
        D hD (fun M => E M ∧ ListAligned T L (post ++ pre) M) hconst
      rw [← offsetProbability_eq_uniform, ← offsetProbability_eq_uniform] at hstep
      have hevent :
          (fun M => E M ∧ ListAligned T L ((i :: post) ++ pre) M) =
          (fun M => (E M ∧ ListAligned T L (post ++ pre) M) ∧
            ∀ j, OnLine (tuplePoint M (T i) j) ((L i).1,(L i).2)) := by
        funext M
        apply propext
        simp only [ListAligned, List.cons_append, List.mem_cons,
          forall_eq_or_imp, Prod.eta]
        tauto
      rw [hevent, hstep, ih htailT htailg horder.1]
      simp only [List.length_cons, pow_succ]
      ring

theorem conditioned_alignment_suffix {ι : Type*} [DecidableEq ι]
    (T : ι → FourTuple F) (L : ι → Line F) (post pre : List ι)
    (hT : ∀ i ∈ post ++ pre, Function.Injective (T i).generator)
    (hg : ∀ i ∈ post ++ pre, ∀ j, (T i).generator j ≠ (L i).1)
    (horder : SmallReuseOrder (fun i => generatorSet (T i)) (post ++ pre))
    (E : MergedPairs F → Prop)
    (hE : ∀ M N, (∀ d ∈ pre.toFinset.biUnion (fun i => generatorSet (T i)),
      M d = N d) → (E M ↔ E N)) :
    conditionedOffsetProbability (ListAligned T L (post ++ pre)) E =
      conditionedOffsetProbability (ListAligned T L pre) E := by
  have hnum := list_alignment_append_weighted T L post pre hT hg horder E hE
  have hden := list_alignment_append_weighted T L post pre hT hg horder
    (fun _ => True) (fun _ _ _ => Iff.rfl)
  simp only [true_and] at hden
  have hnum' :
      offsetProbability (fun M => ListAligned T L (post ++ pre) M ∧ E M) =
        ((Fintype.card F : ℝ)⁻¹ ^ 4) ^ post.length *
          offsetProbability (fun M => ListAligned T L pre M ∧ E M) := by
    simpa only [and_comm] using hnum
  unfold conditionedOffsetProbability
  rw [hnum', hden]
  have hc : ((Fintype.card F : ℝ)⁻¹ ^ 4) ^ post.length ≠ 0 := by positivity
  exact mul_div_mul_left _ _ hc

end
end Balanced.AlignedListProbability

end OAI
