import Mathlib
import OAI.Probability.Perceptron.Variational.FocusedSampleLaw

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal BigOperators Topology
namespace SphericalPerceptronFreeEnergy

def indexedBlockSample {I : Type} [Fintype I] (k : ℕ)
    (A : I → I → Fin (k+1)) (b : IndexedCascadeBase k) : ℝ≥0∞ :=
  ∑' xs : I → IndexedLeaf k, (∏ i, (indexedLeafProbability k b) {xs i}) *
    if (fun i j => indexedCommonDepth k (xs i) (xs j)) = A then 1 else 0

def indexedBlockFocused {I : Type} [Fintype I] (k d : ℕ)
    (A : I → I → Fin (k+1)) (i₀ : I) (b : IndexedCascadeBase k) : ℝ≥0∞ :=
  ∑' xs : I → IndexedLeaf k, ((∏ i, (indexedLeafProbability k b) {xs i}) *
    if (fun i j => indexedCommonDepth k (xs i) (xs j)) = A then 1 else 0) *
      ∑' l : IndexedLeaf k, (indexedLeafProbability k b) {l} *
        if d ≤ (indexedCommonDepth k (xs i₀) l).val then 1 else 0

lemma reindexed_shape_matches {I : Type} [Fintype I] (k : ℕ)
    (s : CascadeVisitShape k) (e : I ≃ CascadeShapeReplicas k s)
    (A : I → I → Fin (k+1))
    (hA : ∀ i j, A i j = indexedCommonDepth k (cascadeShapeLeaves k s (e i))
      (cascadeShapeLeaves k s (e j))) (ys : CascadeShapeReplicas k s → IndexedLeaf k) :
    (fun i j => indexedCommonDepth k (ys (e i)) (ys (e j))) = A ↔
      CascadeShapeMatches k s ys := by
  rw [cascadeShapeMatches_iff]
  constructor
  · intro h i j
    obtain ⟨i,rfl⟩ := e.surjective i
    obtain ⟨j,rfl⟩ := e.surjective j
    exact congrFun (congrFun h i) j |>.trans (hA i j)
  · intro h
    funext i j
    exact (h (e i) (e j)).trans (hA i j).symm

lemma indexedBlockSample_shape {I : Type} [Fintype I] (k : ℕ)
    (s : CascadeVisitShape k) (e : I ≃ CascadeShapeReplicas k s)
    (A : I → I → Fin (k+1))
    (hA : ∀ i j, A i j = indexedCommonDepth k (cascadeShapeLeaves k s (e i))
      (cascadeShapeLeaves k s (e j))) (b : IndexedCascadeBase k) :
    indexedBlockSample k A b = indexedSampleShape k s b := by
  unfold indexedBlockSample indexedSampleShape
  rw [← (Equiv.arrowCongr e.symm (Equiv.refl (IndexedLeaf k))).tsum_eq]
  apply tsum_congr
  intro ys
  change ((∏ i, (indexedLeafProbability k b) {ys (e i)}) *
    if (fun i j => indexedCommonDepth k (ys (e i)) (ys (e j))) = A then 1 else 0) = _
  rw [e.prod_comp (fun i => (indexedLeafProbability k b) {ys i})]
  simp only [reindexed_shape_matches k s e A hA ys]

lemma indexedBlockFocused_shape {I : Type} [Fintype I] (k d : ℕ)
    (s : CascadeVisitShape k) (hs : s.Valid k) (e : I ≃ CascadeShapeReplicas k s)
    (A : I → I → Fin (k+1)) (i₀ : I) (hi₀ : e i₀ = cascadeShapeFocus k s hs)
    (hA : ∀ i j, A i j = indexedCommonDepth k (cascadeShapeLeaves k s (e i))
      (cascadeShapeLeaves k s (e j))) (b : IndexedCascadeBase k) :
    indexedBlockFocused k d A i₀ b = indexedSampleFocused k d s hs b := by
  unfold indexedBlockFocused indexedSampleFocused
  rw [← (Equiv.arrowCongr e.symm (Equiv.refl (IndexedLeaf k))).tsum_eq]
  apply tsum_congr
  intro ys
  change (((∏ i, (indexedLeafProbability k b) {ys (e i)}) *
    if (fun i j => indexedCommonDepth k (ys (e i)) (ys (e j))) = A then 1 else 0) *
    ∑' l, (indexedLeafProbability k b) {l} * if d ≤ (indexedCommonDepth k (ys (e i₀)) l).val then 1 else 0) = _
  rw [e.prod_comp (fun i => (indexedLeafProbability k b) {ys i})]
  simp only [reindexed_shape_matches k s e A hA ys,hi₀]

lemma indexedBlockSample_measurable {I : Type} [Fintype I] (k : ℕ)
    (A : I → I → Fin (k+1)) : Measurable (indexedBlockSample k A) := by
  unfold indexedBlockSample
  refine Measurable.tsum (fun xs => ?_)
  exact (Finset.measurable_prod Finset.univ (fun i _ =>
    (Measure.measurable_coe (measurableSet_singleton (xs i))).comp
      (indexedLeafProbability_measurable k))).mul_const _

lemma indexedBlockFocused_measurable {I : Type} [Fintype I] (k d : ℕ)
    (A : I → I → Fin (k+1)) (i₀ : I) : Measurable (indexedBlockFocused k d A i₀) := by
  unfold indexedBlockFocused
  refine Measurable.tsum (fun xs => ?_)
  exact ((Finset.measurable_prod Finset.univ (fun i _ =>
    (Measure.measurable_coe (measurableSet_singleton (xs i))).comp
      (indexedLeafProbability_measurable k))).mul_const _).mul
        (Measurable.tsum (fun l => ((Measure.measurable_coe (measurableSet_singleton l)).comp
          (indexedLeafProbability_measurable k)).mul_const _))

lemma indexedBlockSample_eq_measure {I : Type} [Fintype I] (k : ℕ)
    (A : I → I → Fin (k+1)) (b : IndexedCascadeBase k) :
    indexedBlockSample k A b = (Measure.pi (fun _ : I => indexedLeafProbability k b))
      {xs | (fun i j => indexedCommonDepth k (xs i) (xs j)) = A} := by
  rw [← lintegral_indicator_one ((Set.to_countable _).measurableSet),lintegral_countable']
  unfold indexedBlockSample
  apply tsum_congr
  intro xs
  rw [Measure.pi_singleton]
  simp only [Set.indicator,Set.mem_ofPred_eq,Pi.one_apply]
  split_ifs <;> simp

lemma indexedBlockFocused_eq_measure {I : Type} [Fintype I] (k d : ℕ)
    (A : I → I → Fin (k+1)) (i₀ : I) (b : IndexedCascadeBase k) :
    indexedBlockFocused k d A i₀ b =
      ((Measure.pi (fun _ : I => indexedLeafProbability k b)).prod (indexedLeafProbability k b))
      {p | (fun i j => indexedCommonDepth k (p.1 i) (p.1 j)) = A ∧
        d ≤ (indexedCommonDepth k (p.1 i₀) p.2).val} := by
  rw [← lintegral_indicator_one ((Set.to_countable _).measurableSet),lintegral_countable',
    ENNReal.tsum_prod']
  unfold indexedBlockFocused
  apply tsum_congr
  intro xs
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro l
  rw [← Set.singleton_prod_singleton,Measure.prod_prod,Measure.pi_singleton]
  simp only [Set.indicator,Set.mem_ofPred_eq,Pi.one_apply]
  split_ifs <;> simp_all

theorem indexedBlockFocused_integral {I : Type} [Fintype I] (k : ℕ)
    (z : Fin k → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (d : ℕ) (hd : d ≤ k) (A : I → I → Fin (k+1)) (i₀ : I) :
    (∫⁻ b, indexedBlockFocused k d A i₀ b ∂indexedCascadeBaseLaw k z) =
      (∫⁻ b, indexedBlockSample k A b ∂indexedCascadeBaseLaw k z) *
        ENNReal.ofReal (((∑ j, if d ≤ (A i₀ j).val then (1:ℝ) else 0) -
          (if h : d = 0 then 0 else z ⟨d-1,by omega⟩)) / Fintype.card I) := by
  by_cases hxs : ∃ xs : I → IndexedLeaf k, (fun i j => indexedCommonDepth k (xs i) (xs j)) = A
  · obtain ⟨xs,hxs⟩ := hxs
    obtain ⟨s,hs,e,he,hm⟩ := finite_leaf_tuple_pointed_shape k I xs i₀
    have hA (i j : I) : A i j = indexedCommonDepth k (cascadeShapeLeaves k s (e i))
        (cascadeShapeLeaves k s (e j)) := (congrFun (congrFun hxs i) j).symm.trans (hm i j)
    simp_rw [indexedBlockFocused_shape k d s hs e A i₀ he hA,
      indexedBlockSample_shape k s e A hA]
    rw [indexedSampleFocused_integral k z hz hz0 hz1 d hd s hs,
      indexedSampleShape_integral k z hz hz0 hz1 s hs,
      focusedShapeNumerator_eq_count k z 0 d hd s hs]
    have hc : Fintype.card I = cascadeVisitCount k s :=
      (Fintype.card_congr e).trans (cascadeShapeReplicas_card k s)
    rw [hc]
    congr 3
    unfold cascadeFocusCount
    rw [← e.sum_comp]
    apply congrArg (fun a : ℝ => a - (if h : d = 0 then 0 else z ⟨d-1,by omega⟩))
    apply Finset.sum_congr rfl
    intro j hj
    rw [hA,he]
  · have ha (xs : I → IndexedLeaf k) :
        ¬ (fun i j => indexedCommonDepth k (xs i) (xs j)) = A := fun h => hxs ⟨xs,h⟩
    simp [indexedBlockFocused,indexedBlockSample,ha]

end SphericalPerceptronFreeEnergy

end

end OAI
