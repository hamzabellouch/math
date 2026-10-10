import Mathlib
import OAI.Probability.SKFluctuations.ProjectionResidual
import OAI.Probability.SKFluctuations.VarianceTestZeroRoot

namespace OAI

/-! Segment Test. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal ENNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

omit [Fintype ι] in
theorem OrderedSteps.mem_pos {a : ℝ} {steps : List (GaussianStep ι)}
    (ha : OrderedSteps a steps) : ∀ st ∈ steps, 0 < st.1 := by
  induction steps generalizing a with
  | nil => simp
  | cons st rest ih =>
    intro t ht
    rcases List.mem_cons.mp ht with rfl|ht
    · exact ha.2.2.1
    · exact ih ha.2.2.2 t ht

 
theorem integral_scaledTransition_test {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {A : (ι → ℝ) → ℝ} (hA : Continuous A)
    (steps : List (GaussianStep ι)) {a m : ℝ} (ha : OrderedSteps a steps)
    (hm : m ≠ 0) (q : ι → ℝ≥0) (x : ι → ℝ) :
    (∫ z, A (x+scaleDriver q z)
      ∂(standardDrivers ι).withDensity (hierarchyTransitions w φ ((m,q)::steps) 0 x)) =
      shiftedMean (Measure.pi fun i => gaussianReal 0 (q i)) m (gaussianHierarchy w φ steps) A x := by
  have hF : Continuous (fun z => gaussianHierarchy w φ steps (x+z)) := (gaussianHierarchy_continuous hw φ steps ha).comp (continuous_const.add continuous_id)
  have hAsh : Continuous (fun z => A (x+z)) := hA.comp (continuous_const.add continuous_id)
  have he : (∫ z, Real.exp (m*gaussianHierarchy w φ steps (x+scaleDriver q z)) ∂standardDrivers ι) =
      ∫ z, Real.exp (m*gaussianHierarchy w φ steps (x+z)) ∂Measure.pi (fun i => gaussianReal 0 (q i)) := by
    rw [← (scaleDriver_gaussian q).map_eq]
    exact (integral_map (scaleDriver q).measurable.aemeasurable
      (hF.const_mul m |>.rexp |>.aestronglyMeasurable)).symm
  have hn : (∫ z, A (x+scaleDriver q z)*Real.exp (m*gaussianHierarchy w φ steps (x+scaleDriver q z))
      ∂standardDrivers ι) =
      ∫ z, A (x+z)*Real.exp (m*gaussianHierarchy w φ steps (x+z))
        ∂Measure.pi (fun i => gaussianReal 0 (q i)) := by
    rw [← (scaleDriver_gaussian q).map_eq]
    exact (integral_map (scaleDriver q).measurable.aemeasurable
      (hAsh.mul (hF.const_mul m |>.rexp) |>.aestronglyMeasurable)).symm
  obtain ⟨C,hL⟩ := gaussianHierarchy_lipschitz hw φ steps ha
  have hshift : LipschitzWith _ (fun z => gaussianHierarchy w φ steps (x+scaleDriver q z)) :=
    hL.comp ((isometry_add_left x).lipschitzWith.comp (scaleDriver q).lipschitzWith)
  rw [scaledTransitionLaw_eq hw φ steps ha hm]
  have hi : Integrable (fun z => Real.exp (m*gaussianHierarchy w φ steps (x+scaleDriver q z)))
      (standardDrivers ι) := (ExpNormBounded.exp_lipschitz hshift m).integrable (fun _ => 1)
  rw [integral_tiltedLaw hshift.continuous.measurable hi]
  simp only [shiftedMean,tiltedMean,he,hn]

theorem integral_segmentLaw_test {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {A : (ι → ℝ) → ℝ} (hA : BddSmooth 0 A)
    (tail pre : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a (pre++tail)) (x : ι → ℝ) :
    (∫ p, A (forwardEnd pre.length (hierarchyIncrements pre) x p) ∂segmentLaw w φ tail pre x) =
      prefixTest pre (gaussianHierarchy w φ tail) A x := by
  induction pre generalizing a x with
  | nil =>
    have := segmentLaw_isProbability hw φ tail [] ha x
    simp [forwardEnd,prefixTest]
  | cons step rest ih =>
    rcases step with ⟨m,q⟩
    have := segmentLaw_isProbability hw φ tail ((m,q)::rest) ha x
    have hf := hA.integrable_comp_measurable
      (f := forwardEnd (((m,q)::rest).length) (hierarchyIncrements ((m,q)::rest)) x)
      ((measurable_forwardEnd _ (hierarchyIncrements_measurable ((m,q)::rest))).comp
        (measurable_const.prodMk measurable_id)) (μ := segmentLaw w φ tail ((m,q)::rest) x)
    rw [integral_segmentLaw_cons hw φ tail rest q ha x hf]
    simp only [List.length_cons,forwardEnd,hierarchyIncrements,Fin.cons_zero,Fin.cons_succ,Fin.tail_cons]
    simp_rw [ih ha.2.2.2]
    obtain ⟨b,hb⟩ := orderedSteps_append_right ((m,q)::rest) tail ha
    obtain ⟨C,hF⟩ := gaussianHierarchy_lipschitz hw φ tail hb
    have hmrest : ∀st ∈ rest, 0 < st.1 := fun st hs =>
      ha.2.2.2.mem_pos st (List.mem_append_left tail hs)
    have ht := prefixTest_smooth0 hF hA rest hmrest
    rw [integral_scaledTransition_test hw φ ht.continuous (rest++tail) ha.2.2.2 ha.2.2.1.ne']
    simp only [prefixTest,prefixContinuation_hierarchy]

 
theorem integral_segmentLaw_append {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {A : (ι → ℝ) → ℝ} (hA : BddSmooth 0 A)
    (tail pre post : List (GaussianStep ι)) {a : ℝ}
    (ha : OrderedSteps a ((pre++post)++tail)) (x : ι → ℝ) :
    (∫ p, A (forwardEnd (pre++post).length (hierarchyIncrements (pre++post)) x p)
      ∂segmentLaw w φ tail (pre++post) x) =
    ∫ p, (∫ q, A (forwardEnd post.length (hierarchyIncrements post)
        (forwardEnd pre.length (hierarchyIncrements pre) x p) q)
      ∂segmentLaw w φ tail post (forwardEnd pre.length (hierarchyIncrements pre) x p))
      ∂segmentLaw w φ (post++tail) pre x := by
  obtain ⟨b,hb⟩ := orderedSteps_append_right pre (post++tail) (by simpa only [List.append_assoc] using ha)
  obtain ⟨c,hc⟩ := orderedSteps_append_right post tail hb
  obtain ⟨C,hF⟩ := gaussianHierarchy_lipschitz hw φ tail hc
  have hpost : ∀st∈post, 0 < st.1 := fun st hs => hb.mem_pos st (List.mem_append_left tail hs)
  rw [integral_segmentLaw_test hw φ hA tail (pre++post) ha]
  simp_rw [integral_segmentLaw_test hw φ hA tail post hb]
  rw [integral_segmentLaw_test hw φ (prefixTest_smooth0 hF hA post hpost) (post++tail) pre
    (by simpa only [List.append_assoc] using ha)]
  rw [prefixTest_append,prefixContinuation_hierarchy]

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal ENNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

omit [Fintype ι] in
theorem OrderedSteps.suffix {a : ℝ} (pre tail : List (GaussianStep ι))
    (ha : OrderedSteps a (pre++tail)) : OrderedSteps a tail := by
  induction pre generalizing a with
  | nil => exact ha
  | cons step rest ih => exact (ih ha.2.2.2).lower ha.1 ha.2.1

theorem prefixTest_mono {F A B : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hA : BddSmooth 0 A) (hB : BddSmooth 0 B)
    (hAB : ∀ x, A x ≤ B x) (pre : List (GaussianStep ι))
    (hm : ∀st∈pre, 0 < st.1) (x : ι → ℝ) :
    prefixTest pre F A x ≤ prefixTest pre F B x := by
  induction pre generalizing x with
  | nil => exact hAB x
  | cons step rest ih =>
    rcases step with ⟨m,q⟩
    have hr : ∀st∈rest, 0 < st.1 := fun st hs => hm st (List.mem_cons_of_mem _ hs)
    exact shiftedMean_mono (prefixTest_smooth0 hF hA rest hr) (prefixTest_smooth0 hF hB rest hr)
      (ih hr) ((exponentialIncrement_gaussian q).integrable_shift
        (prefixContinuation_lipschitz hF rest hr) m x)

 

def AlignedFieldClock (u : ι → ℝ) (δ : ℝ) (pre : List (GaussianStep ι)) : Prop :=
  ∃d : Fin pre.length → ℝ, (∀i, 0 ≤ d i) ∧ (∑i, d i) = δ ∧
    ∀i j, u j ≠ 0 → (hierarchyClocks pre i j : ℝ) = d i

noncomputable def projectionBlockConstant (a δ U : ℝ) (k : ℕ) : ℝ :=
  (2*((2:ℝ)^(2*k+2)*(2:ℝ)^(2*k))/(a*δ))^(2*k+2) *
    (subgaussianMomentConstant k*(δ*U)^(k+1))

theorem projection_aligned_block {n : ℕ} {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (tail pre : List (GaussianStep (Fin (n+1))))
    {a δ : ℝ} (ha : OrderedSteps a (pre++tail)) (ha0 : 0 < a) (hδ : 0 < δ)
    (u : Fin (n+1) → ℝ) (hc : AlignedFieldClock u δ pre) (k : ℕ) (x : Fin (n+1) → ℝ) :
    prefixTest pre (gaussianHierarchy w φ tail) (hierarchyCenteredEvenMoment w φ (fun s => φ s u) tail k) x ≤
      hierarchyCenteredEvenMoment w φ (fun s => φ s u) (pre++tail) k x/2 +
        projectionBlockConstant a δ (∑j, (u j)^2) k/2 := by
  obtain ⟨d,hd,hD,hc⟩ := hc
  have hDP : 0 < ∑i, d i := by rwa [hD]
  have hh := hierarchy_projection_segment_half hw φ tail pre ha ha0 u
    (fun i j => Real.sqrt (d i)*u j) d hd hDP (alignedSegment_direction pre d hd u hc) k x
  have htail := ha.suffix pre tail
  rw [← integral_segmentLaw_test hw φ (hierarchyCenteredEvenMoment_smooth_zero hw φ
    (fun s => φ s u) tail htail k) tail pre ha]
  simpa only [segmentCenteredEvenMoment,alignedSegment_variance pre d hd u,hD,projectionBlockConstant] using hh

theorem projection_aligned_blocks_prefix {n : ℕ} {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (tail : List (GaussianStep (Fin (n+1))))
    (blocks : List (List (GaussianStep (Fin (n+1))))) {a δ : ℝ}
    (ha0 : 0 < a) (hδ : 0 < δ) (ha : OrderedSteps a (blocks.flatten++tail))
    (u : Fin (n+1) → ℝ) (hc : ∀pre∈blocks, AlignedFieldClock u δ pre)
    (k : ℕ) (x : Fin (n+1) → ℝ) :
    prefixTest blocks.flatten (gaussianHierarchy w φ tail)
      (hierarchyCenteredEvenMoment w φ (fun s => φ s u) tail k) x ≤
    (1/2:ℝ)^blocks.length*hierarchyCenteredEvenMoment w φ (fun s => φ s u) (blocks.flatten++tail) k x +
      (1-(1/2:ℝ)^blocks.length)*projectionBlockConstant a δ (∑j, (u j)^2) k := by
  induction blocks generalizing a x with
  | nil => simp [prefixTest]
  | cons pre rest ih =>
    have hp : OrderedSteps a (pre++(rest.flatten++tail)) := by
      simpa only [List.flatten_cons,List.append_assoc] using ha
    have hrest : OrderedSteps a (rest.flatten++tail) := hp.suffix pre (rest.flatten++tail)
    have hrclock : ∀b∈rest, AlignedFieldClock u δ b := fun b hb => hc b (List.mem_cons_of_mem _ hb)
    have hmono := ih ha0 hrest hrclock
    have htail := hrest.suffix rest.flatten tail
    obtain ⟨C,hF⟩ := gaussianHierarchy_lipschitz hw φ tail htail
    obtain ⟨Cr,hFr⟩ := gaussianHierarchy_lipschitz hw φ (rest.flatten++tail) hrest
    have hM := hierarchyCenteredEvenMoment_smooth_zero hw φ (fun s => φ s u) tail htail k
    have hMr := hierarchyCenteredEvenMoment_smooth_zero hw φ (fun s => φ s u) (rest.flatten++tail) hrest k
    have hmrest : ∀st∈rest.flatten, 0 < st.1 := fun st hs =>
      hrest.mem_pos st (List.mem_append_left tail hs)
    have hmpre : ∀st∈pre, 0 < st.1 := fun st hs => hp.mem_pos st (List.mem_append_left _ hs)
    let B := projectionBlockConstant a δ (∑j, (u j)^2) k
    let q : ℝ := (1/2)^rest.length
    have hR := prefixTest_smooth0 hF hM rest.flatten hmrest
    have hupper := (hMr.const_mul q).add (BddSmooth.const 0 ((1-q)*B))
    have hb := projection_aligned_block hw φ (rest.flatten++tail) pre hp ha0 hδ u
      (hc pre List.mem_cons_self) k x
    have hmean := prefixTest_mono hFr hR hupper hmono pre hmpre x
    have heq : prefixTest pre (gaussianHierarchy w φ (rest.flatten++tail))
        (fun y => q*hierarchyCenteredEvenMoment w φ (fun s => φ s u) (rest.flatten++tail) k y+(1-q)*B) x =
        q*prefixTest pre (gaussianHierarchy w φ (rest.flatten++tail))
          (hierarchyCenteredEvenMoment w φ (fun s => φ s u) (rest.flatten++tail) k) x+(1-q)*B := by
      have hh := prefixTest_affine hFr hMr pre hmpre ((1-q)*B) q x
      simpa only [add_comm] using hh
    rw [heq] at hmean
    change prefixTest (pre++rest.flatten) _ _ x ≤ _
    rw [prefixTest_append,prefixContinuation_hierarchy]
    have hq : 0 ≤ q := by dsimp [q]; positivity
    have hh := hmean.trans (add_le_add (mul_le_mul_of_nonneg_left hb hq) le_rfl)
    refine hh.trans_eq ?_
    simp only [List.length_cons,List.flatten_cons,List.append_assoc,pow_succ]
    dsimp [q,B]
    ring_nf

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal ENNReal BigOperators
variable {ι κ S : Type*} [Fintype ι] [Fintype κ] [Fintype S] [Nonempty S]

theorem prefixContinuation_reindex_steps (e : κ ≃ ι) (F : (ι → ℝ) → ℝ)
    (pre : List (GaussianStep ι)) :
    prefixContinuation (reindexSteps e pre) (fun x => F (coordinateEquiv e x)) =
      fun x => prefixContinuation pre F (coordinateEquiv e x) := by
  induction pre with
  | nil => rfl
  | cons st rest ih =>
    funext x
    change shiftedContinuation _ st.1
      (prefixContinuation (reindexSteps e rest) (fun x => F (coordinateEquiv e x))) x = _
    rw [ih]
    exact shiftedContinuation_reindex e st.2 st.1 _ x

theorem prefixTest_reindex_steps (e : κ ≃ ι) (F A : (ι → ℝ) → ℝ)
    (pre : List (GaussianStep ι)) :
    prefixTest (reindexSteps e pre) (fun x => F (coordinateEquiv e x)) (fun x => A (coordinateEquiv e x)) =
      fun x => prefixTest pre F A (coordinateEquiv e x) := by
  induction pre with
  | nil => rfl
  | cons st rest ih =>
    funext x
    change shiftedMean _ st.1
      (prefixContinuation (reindexSteps e rest) (fun x => F (coordinateEquiv e x)))
      (prefixTest (reindexSteps e rest) (fun x => F (coordinateEquiv e x)) (fun x => A (coordinateEquiv e x))) x = _
    rw [prefixContinuation_reindex_steps,ih]
    exact shiftedMean_reindex e st.2 st.1 _ _ x

omit [Nonempty S] in
theorem hierarchyCenteredEvenMoment_reindex (e : κ ≃ ι) (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (Y : S → ℝ) (steps : List (GaussianStep ι)) (k : ℕ) :
    hierarchyCenteredEvenMoment w (reindexFeature e φ) Y (reindexSteps e steps) k =
      fun x => hierarchyCenteredEvenMoment w φ Y steps k (coordinateEquiv e x) := by
  funext x
  simp only [hierarchyCenteredEvenMoment,hierarchyAtom,gaussianHierarchyMean_reindex_steps]

omit [Fintype ι] [Fintype κ] in
theorem AlignedFieldClock.reindex (e : κ ≃ ι) (u : ι → ℝ) {δ : ℝ}
    (pre : List (GaussianStep ι)) (hc : AlignedFieldClock u δ pre) :
    AlignedFieldClock (fun j => u (e j)) δ (reindexSteps e pre) := by
  induction pre generalizing δ with
  | nil =>
    change AlignedFieldClock (fun j => u (e j)) δ []
    simpa [AlignedFieldClock] using hc
  | cons step rest ih =>
    rcases step with ⟨m,q⟩
    obtain ⟨d,hd,hD,hc⟩ := hc
    have hr : AlignedFieldClock u (∑ i : Fin rest.length, d i.succ) rest :=
      ⟨Fin.tail d,fun i => hd i.succ,rfl,fun i j hj => hc i.succ j hj⟩
    obtain ⟨dr,hdr,hsr,hcr⟩ := ih hr
    refine ⟨Fin.cons (d 0) dr,Fin.cases (hd 0) (fun i => hdr i),?_,?_⟩
    · change (∑ i : Fin ((reindexSteps e rest).length+1), Fin.cons (d 0) dr i) = δ
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero,Fin.cons_succ,hsr]
      exact (Fin.sum_univ_succ d).symm.trans hD
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · intro j hj
        exact hc 0 (e j) hj
      · intro j' hj
        exact hcr j j' hj

omit [Fintype ι] [Fintype κ] in
theorem reindexSteps_append (e : κ ≃ ι) (pre tail : List (GaussianStep ι)) :
    reindexSteps e (pre++tail) = reindexSteps e pre++reindexSteps e tail := by
  simp only [reindexSteps,List.map_append]

omit [Fintype ι] [Fintype κ] in
theorem reindexSteps_flatten (e : κ ≃ ι) (blocks : List (List (GaussianStep ι))) :
    reindexSteps e blocks.flatten = (blocks.map (reindexSteps e)).flatten := by
  induction blocks with
  | nil => rfl
  | cons pre rest ih => simp only [List.flatten_cons,List.map_cons,reindexSteps_append,ih]

 

theorem projection_aligned_blocks_finite [Nonempty ι] {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (tail : List (GaussianStep ι))
    (blocks : List (List (GaussianStep ι))) {a δ : ℝ}
    (ha0 : 0 < a) (hδ : 0 < δ) (ha : OrderedSteps a (blocks.flatten++tail))
    (u : ι → ℝ) (hc : ∀pre∈blocks, AlignedFieldClock u δ pre)
    (k : ℕ) (x : ι → ℝ) :
    prefixTest blocks.flatten (gaussianHierarchy w φ tail)
      (hierarchyCenteredEvenMoment w φ (fun s => φ s u) tail k) x ≤
    (1/2:ℝ)^blocks.length*hierarchyCenteredEvenMoment w φ (fun s => φ s u) (blocks.flatten++tail) k x +
      (1-(1/2:ℝ)^blocks.length)*projectionBlockConstant a δ (∑j, (u j)^2) k := by
  classical
  let r := Fintype.card ι-1
  have hr : r+1 = Fintype.card ι := Nat.sub_add_cancel (Fintype.card_pos_iff.mpr ‹Nonempty ι›)
  let e : Fin (r+1) ≃ ι := (finCongr hr).trans (Fintype.equivFin ι).symm
  have hc' : ∀pre∈blocks.map (reindexSteps e), AlignedFieldClock (fun j => u (e j)) δ pre := by
    intro pre hp
    rcases List.mem_map.mp hp with ⟨p,hpm,heq⟩
    rw [← heq]
    exact AlignedFieldClock.reindex e u p (hc p hpm)
  have ha' : OrderedSteps a ((blocks.map (reindexSteps e)).flatten++reindexSteps e tail) := by
    rw [← reindexSteps_flatten,← reindexSteps_append]
    exact reindexSteps_ordered e ha
  have hu : (fun s => reindexFeature e φ s (fun j => u (e j))) = fun s => φ s u := by
    funext s
    change φ s (coordinateEquiv e (fun j => u (e j))) = φ s u
    congr 1
    ext j
    simp only [coordinateEquiv_apply,e.apply_symm_apply]
  have hh := projection_aligned_blocks_prefix hw (reindexFeature e φ) (reindexSteps e tail)
    (blocks.map (reindexSteps e)) ha0 hδ ha' (fun j => u (e j)) hc' k ((coordinateEquiv e).symm x)
  simp only [hu,← reindexSteps_flatten,← reindexSteps_append,gaussianHierarchy_reindex_steps,
    hierarchyCenteredEvenMoment_reindex,prefixTest_reindex_steps,List.length_map,
    ContinuousLinearEquiv.apply_symm_apply] at hh
  simpa only [e.sum_comp (fun j => (u j)^2)] using hh

end SKFluctuations.Hierarchy

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Hierarchy
open scoped Topology NNReal ENNReal BigOperators

 

noncomputable def fieldProjectionDirection (n : ℕ) (V : Fin n → ℝ) : FeatureIndex n → ℝ
  | Sum.inl i => V i / Real.sqrt (n : ℝ)
  | Sum.inr _ => 0

noncomputable def spinProjection (n : ℕ) (V : Fin n → ℝ) (σ : Spin n) : ℝ :=
  (∑i, V i*spinValue (σ i))/Real.sqrt (n : ℝ)

noncomputable def projectionEuclideanNorm (n : ℕ) (V : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑i, (V i)^2)

theorem finiteFeature_fieldProjectionDirection (n : ℕ) (V : Fin n → ℝ) (σ : Spin n) :
    finiteFeature n σ (fieldProjectionDirection n V) = spinProjection n V σ := by
  simp only [finiteFeature_apply,Fintype.sum_sum_type,featureCoefficient,fieldProjectionDirection,
    mul_zero,Finset.sum_const_zero,add_zero,spinProjection,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem fieldProjectionDirection_sqsum (n : ℕ) (V : Fin n → ℝ) :
    (∑j, (fieldProjectionDirection n V j)^2) = (∑i, (V i)^2)/(n:ℝ) := by
  simp only [Fintype.sum_sum_type,fieldProjectionDirection,zero_pow (by omega : 2 ≠ 0),
    Finset.sum_const_zero,add_zero,div_pow,Real.sq_sqrt (Nat.cast_nonneg n),Finset.sum_div]

theorem spinProjection_abs_le (n : ℕ) (V : Fin n → ℝ) (σ : Spin n) :
    |spinProjection n V σ| ≤ projectionEuclideanNorm n V := by
  have hsum : 0 ≤ ∑i, (V i)^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  by_cases hn : n = 0
  · simp [spinProjection,hn,projectionEuclideanNorm]
  have hn' : (0:ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hsq := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ V (fun i => spinValue (σ i))
  have hspin : ∑i, (spinValue (σ i))^2 = (n:ℝ) := by
    simp only [pow_two,spinValue_sq,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  rw [hspin] at hsq
  have hbound : (spinProjection n V σ)^2 ≤ ∑i, (V i)^2 := by
    dsimp [spinProjection]
    rw [div_pow,Real.sq_sqrt hn'.le]
    exact (div_le_iff₀ hn').mpr hsq
  exact (Real.le_sqrt (abs_nonneg _) hsum).mpr (by simpa only [sq_abs] using hbound)

namespace Hierarchy
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

theorem hierarchyCenteredEvenMoment_bound {w : S → ℝ} (hw : ∀s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (Y : S → ℝ) {R : ℝ} (hY : ∀s, |Y s| ≤ R)
    (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps) (k : ℕ) (x : ι → ℝ) :
    hierarchyCenteredEvenMoment w φ Y steps k x ≤ (2*R)^(2*k+2) := by
  have hmean := gaussianHierarchyMean_abs_le hw φ hY steps ha x
  rw [hierarchyCenteredEvenMoment]
  calc
    _ ≤ ∑s, hierarchyAtom w φ steps s x*(2*R)^(2*k+2) := by
      apply Finset.sum_le_sum
      intro s _
      apply mul_le_mul_of_nonneg_left _ (hierarchyAtom_nonneg hw φ steps ha s x)
      apply pow_le_pow_left₀ (abs_nonneg _)
      exact (abs_sub _ _).trans (by linarith [hY s])
    _ = _ := by rw [← Finset.sum_mul,hierarchyAtom_sum hw φ steps ha x,one_mul]

noncomputable def projectionOrderConstant (k : ℕ) : ℝ :=
  (2*((2:ℝ)^(2*k+2)*(2:ℝ)^(2*k)))^(2*k+2)*subgaussianMomentConstant k

omit [Fintype ι] [Fintype S] [Nonempty S] in
theorem projectionBlockConstant_eq {a δ U : ℝ} (ha : a ≠ 0) (hδ : δ ≠ 0) (k : ℕ) :
    projectionBlockConstant a δ U k = projectionOrderConstant k*(U/(a^2*δ))^(k+1) := by
  let K := 2*((2:ℝ)^(2*k+2)*(2:ℝ)^(2*k))
  have hp : 2*k+2 = 2*(k+1) := by omega
  change (K/(a*δ))^(2*k+2)*(subgaussianMomentConstant k*(δ*U)^(k+1)) =
    K^(2*k+2)*subgaussianMomentConstant k*(U/(a^2*δ))^(k+1)
  rw [hp,pow_mul,pow_mul]
  have hbase : (K/(a*δ))^2*(δ*U) = K^2*(U/(a^2*δ)) := by
    field_simp
  calc
    _ = subgaussianMomentConstant k*((K/(a*δ))^2*(δ*U))^(k+1) := by rw [mul_pow]; ring
    _ = _ := by rw [hbase,mul_pow]; ring

end Hierarchy

 

theorem finiteSK_projection_blocks (n : ℕ) (V : Fin n → ℝ)
    (tail : List (GaussianStep (FeatureIndex n)))
    (blocks : List (List (GaussianStep (FeatureIndex n)))) {a δ : ℝ}
    (ha0 : 0 < a) (hδ : 0 < δ) (ha : OrderedSteps a (blocks.flatten++tail))
    (hc : ∀pre∈blocks, AlignedFieldClock (fieldProjectionDirection n V) δ pre)
    (k : ℕ) (x : FeatureIndex n → ℝ) :
    prefixTest blocks.flatten (finiteSKHierarchy n tail)
      (hierarchyCenteredEvenMoment (uniformWeight n) (finiteFeature n) (spinProjection n V) tail k) x ≤
    (1/2:ℝ)^blocks.length*(2*projectionEuclideanNorm n V)^(2*k+2) +
      projectionOrderConstant k*((∑i, (V i)^2)/((n:ℝ)*a^2*δ))^(k+1) := by
  let : Nonempty (FeatureIndex n) := ⟨Sum.inr none⟩
  have hh := projection_aligned_blocks_finite (uniformWeight_pos n) (finiteFeature n)
    tail blocks ha0 hδ ha (fieldProjectionDirection n V) hc k x
  have hY : (fun s => finiteFeature n s (fieldProjectionDirection n V)) = spinProjection n V :=
    funext (finiteFeature_fieldProjectionDirection n V)
  rw [hY] at hh
  have hinit := hierarchyCenteredEvenMoment_bound (uniformWeight_pos n) (finiteFeature n)
    (spinProjection n V) (spinProjection_abs_le n V) (blocks.flatten++tail) ha k x
  have ht : 0 ≤ (1/2:ℝ)^blocks.length := by positivity
  have hB : 0 ≤ projectionBlockConstant a δ (∑j, (fieldProjectionDirection n V j)^2) k := by
    dsimp [projectionBlockConstant,subgaussianMomentConstant]
    positivity
  have hcoef : 1-(1/2:ℝ)^blocks.length ≤ 1 := by linarith
  have hh' := hh.trans (add_le_add (mul_le_mul_of_nonneg_left hinit ht)
    (mul_le_mul_of_nonneg_right hcoef hB))
  rw [one_mul,projectionBlockConstant_eq ha0.ne' hδ.ne',fieldProjectionDirection_sqsum] at hh'
  convert hh' using 1 <;> congr 3
  rw [div_div]
  congr 1
  ring

end SKFluctuations

 

namespace SKFluctuations
open Filter Set
open scoped Topology

 
noncomputable def projectionLogBlocks (n : ℕ) : ℕ := ⌈(Real.log (n:ℝ))^2⌉₊

theorem projectionLogBlocks_ge (n : ℕ) :
    (Real.log (n:ℝ))^2 ≤ (projectionLogBlocks n:ℝ) := Nat.le_ceil _

theorem projectionLogBlocks_le (n : ℕ) (h : 2 ≤ Real.log (n:ℝ)) :
    (projectionLogBlocks n:ℝ) ≤ (Real.log (n:ℝ))^4 := by
  have hc := Nat.ceil_lt_add_one (sq_nonneg (Real.log (n:ℝ)))
  change (projectionLogBlocks n:ℝ) < _ at hc
  have hh : 4 ≤ (Real.log (n:ℝ))^2 := by nlinarith
  have h4 : (Real.log (n:ℝ))^2+1 ≤ (Real.log (n:ℝ))^4 := by nlinarith [sq_nonneg ((Real.log (n:ℝ))^2-2)]
  exact hc.le.trans h4

theorem projectionLogBlocks_pos (n : ℕ) (h : 2 ≤ Real.log (n:ℝ)) :
    0 < projectionLogBlocks n := by
  have hg := projectionLogBlocks_ge n
  have : (0:ℝ) < projectionLogBlocks n := by nlinarith
  exact_mod_cast this

theorem projectionLogBlocks_suppression (n q : ℕ) (hn : 0 < n)
    (h : (q:ℝ)/Real.log 2 ≤ Real.log (n:ℝ)) :
    (n:ℝ)^q*(1/2:ℝ)^(projectionLogBlocks n) ≤ 1 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn' : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hl : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hq : (q:ℝ) ≤ Real.log (n:ℝ)*Real.log 2 := (div_le_iff₀ h2).mp h
  have hg := mul_le_mul_of_nonneg_right (projectionLogBlocks_ge n) h2.le
  have hmul := mul_le_mul_of_nonneg_right hq hl
  have hp : 0 < (n:ℝ)^q*(1/2:ℝ)^(projectionLogBlocks n) := by positivity
  have he : Real.log ((n:ℝ)^q*(1/2:ℝ)^(projectionLogBlocks n)) =
      (q:ℝ)*Real.log (n:ℝ)-(projectionLogBlocks n:ℝ)*Real.log 2 := by
    rw [Real.log_mul (pow_ne_zero _ hn'.ne') (pow_ne_zero _ (by norm_num)),Real.log_pow,Real.log_pow]
    norm_num [Real.log_div]
    ring
  have hh : Real.log ((n:ℝ)^q*(1/2:ℝ)^(projectionLogBlocks n)) ≤ 0 := by rw [he]; nlinarith
  exact (Real.log_nonpos_iff hp.le).mp hh

 

theorem eventually_projectionLogBlocks (q : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ 2 ≤ Real.log (n:ℝ) ∧
      0 < projectionLogBlocks n ∧ (projectionLogBlocks n:ℝ) ≤ (Real.log (n:ℝ))^4 ∧
      (1/2:ℝ)^(projectionLogBlocks n)*((n:ℝ)^q)*B ≤ 1 := by
  have ht : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hn : ∀ᶠ n : ℕ in atTop, (max 1 B:ℝ) ≤ n := tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [hn,ht.eventually_ge_atTop 2,ht.eventually_ge_atTop ((q+1:ℕ)/Real.log 2)] with n hn hlog hq
  have hn0 : 0 < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) ((le_max_left _ _).trans hn))
  refine ⟨hn0,hlog,projectionLogBlocks_pos n hlog,projectionLogBlocks_le n hlog,?_⟩
  have hh := projectionLogBlocks_suppression n (q+1) hn0 hq
  have hB : B ≤ (n:ℝ) := (le_max_right _ _).trans hn
  have hnonneg : 0 ≤ (1/2:ℝ)^(projectionLogBlocks n)*(n:ℝ)^q := by positivity
  calc
    _ ≤ (1/2:ℝ)^(projectionLogBlocks n)*(n:ℝ)^q*(n:ℝ) := mul_le_mul_of_nonneg_left hB hnonneg
    _ ≤ 1 := by simpa only [pow_succ,mul_comm,mul_left_comm,mul_assoc] using hh

end SKFluctuations

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Hierarchy
open scoped Topology NNReal ENNReal BigOperators

 

theorem eventually_finiteSK_projection_log (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (V : Fin n → ℝ)
      (tail : List (GaussianStep (FeatureIndex n)))
      (blocks : List (List (GaussianStep (FeatureIndex n)))) (a D : ℝ),
      0 < a → 0 < D → D ≤ B →
      OrderedSteps a (blocks.flatten++tail) →
      blocks.length = projectionLogBlocks n →
      (∀pre∈blocks, AlignedFieldClock (fieldProjectionDirection n V)
        (D/(projectionLogBlocks n:ℝ)) pre) →
      ∀ x : FeatureIndex n → ℝ,
      prefixTest blocks.flatten (finiteSKHierarchy n tail)
        (hierarchyCenteredEvenMoment (uniformWeight n) (finiteFeature n) (spinProjection n V) tail k) x ≤
      (1+projectionOrderConstant k)*
        ((Real.log (n:ℝ))^4*(∑i, (V i)^2)/((n:ℝ)*a^2*D))^(k+1) := by
  filter_upwards [eventually_projectionLogBlocks (k+1) ((2:ℝ)^(2*k+2)*B^(k+1))] with n hn
  rcases hn with ⟨hn,hlog,hN,hNlog,hsupp⟩
  intro V tail blocks a D ha0 hD hDB ha hlen hc x
  have hn' : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hN' : (0:ℝ) < projectionLogBlocks n := Nat.cast_pos.mpr hN
  have hδ : 0 < D/(projectionLogBlocks n:ℝ) := div_pos hD hN'
  have hh := finiteSK_projection_blocks n V tail blocks ha0 hδ ha hc k x
  rw [hlen] at hh
  let U : ℝ := ∑i, (V i)^2
  let den : ℝ := (n:ℝ)*a^2*D
  let X : ℝ := U/den
  let L : ℝ := (Real.log (n:ℝ))^4
  let N : ℝ := projectionLogBlocks n
  have hU : 0 ≤ U := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hden : 0 < den := by dsimp [den]; positivity
  have hX : 0 ≤ X := div_nonneg hU hden.le
  have hL : 1 ≤ L := by
    dsimp [L]
    have hsq : 4 ≤ (Real.log (n:ℝ))^2 := by nlinarith
    nlinarith [sq_nonneg ((Real.log (n:ℝ))^2-2)]
  have ha1 : a ≤ 1 := ha.bounds.2
  have ha2 : a^2 ≤ 1 := by nlinarith
  have hAD : a^2*D ≤ B := (mul_le_mul_of_nonneg_right ha2 hD.le).trans (by simpa using hDB)
  have hpow : (a^2*D)^(k+1) ≤ B^(k+1) := pow_le_pow_left₀ (by positivity) hAD _
  have hdenpow : den^(k+1) = (n:ℝ)^(k+1)*(a^2*D)^(k+1) := by dsimp [den]; rw [mul_assoc,mul_pow]
  have hcoeff : ((1/2:ℝ)^projectionLogBlocks n*(2:ℝ)^(2*k+2))*den^(k+1) ≤ 1 := by
    rw [hdenpow]
    have hm := mul_le_mul_of_nonneg_left hpow
      (show 0 ≤ (1/2:ℝ)^projectionLogBlocks n*(2:ℝ)^(2*k+2)*(n:ℝ)^(k+1) by positivity)
    calc
      _ ≤ (1/2:ℝ)^projectionLogBlocks n*(2:ℝ)^(2*k+2)*(n:ℝ)^(k+1)*B^(k+1) := by
        simpa only [mul_assoc] using hm
      _ ≤ 1 := by simpa only [mul_assoc,mul_left_comm,mul_comm] using hsupp
  have hcoef := (le_div_iff₀ (pow_pos hden (k+1))).mpr hcoeff
  have hiniteq : (2*projectionEuclideanNorm n V)^(2*k+2) = (2:ℝ)^(2*k+2)*U^(k+1) := by
    rw [mul_pow]
    congr 1
    rw [show 2*k+2 = 2*(k+1) by omega,pow_mul]
    change ((Real.sqrt U)^2)^(k+1) = U^(k+1)
    rw [Real.sq_sqrt hU]
  have hinit : (1/2:ℝ)^projectionLogBlocks n*(2*projectionEuclideanNorm n V)^(2*k+2) ≤ X^(k+1) := by
    rw [hiniteq]
    have hm := mul_le_mul_of_nonneg_right hcoef (pow_nonneg hU (k+1))
    calc
      _ ≤ 1/den^(k+1)*U^(k+1) := by simpa only [mul_assoc] using hm
      _ = X^(k+1) := by dsimp [X]; rw [div_pow]; ring
  have hforceeq : U/((n:ℝ)*a^2*(D/(projectionLogBlocks n:ℝ))) = N*X := by
    dsimp [X,N,den]
    field_simp
  have hC : 0 ≤ projectionOrderConstant k := by
    dsimp [projectionOrderConstant,subgaussianMomentConstant]
    positivity
  have hNX : N*X ≤ L*X := mul_le_mul_of_nonneg_right hNlog hX
  have hXX : X ≤ L*X := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hL hX
  have hLX : 0 ≤ L*X := mul_nonneg (le_trans (by norm_num) hL) hX
  calc
    _ ≤ _ := hh
    _ ≤ X^(k+1)+projectionOrderConstant k*(N*X)^(k+1) := by
      rw [← hforceeq]
      exact add_le_add hinit le_rfl
    _ ≤ (L*X)^(k+1)+projectionOrderConstant k*(L*X)^(k+1) :=
      add_le_add (pow_le_pow_left₀ hX hXX _) (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (mul_nonneg hN'.le hX) hNX _) hC)
    _ = _ := by dsimp [L,X,den,U]; ring

end SKFluctuations

end

end OAI
