import Mathlib
import OAI.Probability.SKFluctuations.CompletedFeatureKernel

namespace OAI

/-! Physical Layer Sum. -/

noncomputable section


namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 def physicalLayerIncrement (n : ℕ) (bs : List (GaussianLayer (FeatureIndex n)))
    (x : FeatureIndex n → ℝ)
    (p : ForwardPath (FeatureIndex n → ℝ) (Spin n) (layerSteps bs).length)
    (i : Fin (layerCutSchedule bs).length) : Fin n → ℝ :=
  cutIncrement (layerCutSchedule bs)
    (fun k l => actualSpinPath n (layerSteps bs) (fun _ : Unit => x) k ((),p) l) 0 i

 theorem sum_physicalLayerIncrement (n : ℕ) (bs : List (GaussianLayer (FeatureIndex n)))
    (x : FeatureIndex n → ℝ)
    (p : ForwardPath (FeatureIndex n → ℝ) (Spin n) (layerSteps bs).length) :
    (∑ i, physicalLayerIncrement n bs x p i) =
      normalizedSpin n (ForwardPath.spin (layerSteps bs).length p)-actualSpinMean n (layerSteps bs) x := by
  unfold physicalLayerIncrement
  rw [sum_cutIncrement,lastLayerCut_schedule]
  simp only [actualSpinPath_terminal,actualSpinPath_zero]

 theorem dot_physicalLayerIncrement (n : ℕ) (bs : List (GaussianLayer (FeatureIndex n)))
    {a : ℝ} (ha : OrderedSteps a (layerSteps bs)) (V : Fin n → ℝ)
    (x : FeatureIndex n → ℝ)
    (p : ForwardPath (FeatureIndex n → ℝ) (Spin n) (layerSteps bs).length)
    (i : Fin (layerCutSchedule bs).length) :
    (∑ l, V l*physicalLayerIncrement n bs x p i l) =
      hierarchyMeanPath (uniformWeight n) (finiteFeature n) (spinProjection n V) (layerSteps bs)
        (fun _ : Unit => x) ((layerCutSchedule bs).get i).2 ((),p) -
      hierarchyMeanPath (uniformWeight n) (finiteFeature n) (spinProjection n V) (layerSteps bs)
        (fun _ : Unit => x) (cutPredecessor (layerCutSchedule bs) 0 i) ((),p) := by
  simp only [physicalLayerIncrement,cutIncrement,Pi.sub_apply,mul_sub,Finset.sum_sub_distrib,
    spinProjection_actualSpinPath n V (layerSteps bs) ha]

 theorem physicalLayerIncrement_dot_sq_integrable (n : ℕ)
    (bs : List (GaussianLayer (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a (layerSteps bs))
    (V : Fin n → ℝ) (x : FeatureIndex n → ℝ) (i : Fin (layerCutSchedule bs).length) :
    Integrable (fun p => (∑ l, V l*physicalLayerIncrement n bs x p i l)^2)
      (hierarchyPathKernel (uniformWeight n) (finiteFeature n) (layerSteps bs) x) := by
  have := hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) (layerSteps bs) ha
  simp_rw [dot_physicalLayerIncrement n bs ha V x]
  have hm k := (hierarchyMeanPath_measurable (uniformWeight_pos n) (finiteFeature n)
    (spinProjection n V) (layerSteps bs) ha (fun _ : Unit => x) measurable_const k).mono
      (forwardPrefixSpace_le _ _ _ _ _) le_rfl
  have hmfull k := (hm k).comp ((measurable_const (a := ())).prodMk measurable_id)
  apply Integrable.of_bound (((hmfull _).sub (hmfull _)).pow_const 2).aestronglyMeasurable
    ((2*projectionEuclideanNorm n V)^2)
  exact Eventually.of_forall fun p => by
    rw [Real.norm_of_nonneg (sq_nonneg _), ← sq_abs]
    apply pow_le_pow_left₀ (abs_nonneg _)
    have h k := hierarchyMeanPath_abs_le (uniformWeight_pos n) (finiteFeature n)
      (spinProjection n V) (spinProjection_abs_le n V) (layerSteps bs) ha (fun _ : Unit => x) k ((),p)
    have h1 := h (((layerCutSchedule bs).get i).2)
    have h0 := h (cutPredecessor (layerCutSchedule bs) 0 i)
    exact (abs_sub _ _).trans (by simp only [Function.comp_apply, id_eq]; linarith)

 theorem physicalSusceptibility_le_double_sum (n : ℕ)
    (bs : List (GaussianLayer (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a (layerSteps bs))
    (hm : ∀ B ∈ bs, ∀ st ∈ B.2, st.1 ≤ B.1) (x : FeatureIndex n → ℝ)
    (p : ForwardPath (FeatureIndex n → ℝ) (Spin n) (layerSteps bs).length) :
    physicalSusceptibility n (layerSteps bs) x p ≤
      (bs.length+1:ℕ) * ∑ i : Fin (layerCutSchedule bs).length,
        ∑ j : Fin (layerCutSchedule bs).length, ((layerCutSchedule bs).get j).1 *
          ∫ q, (∑ l, physicalLayerIncrement n bs x p i l * physicalLayerIncrement n bs x q j l)^2
            ∂hierarchyPathKernel (uniformWeight n) (finiteFeature n) (layerSteps bs) x := by
  let V := physicalLayerIncrement n bs x p
  have he : (∑ i, fieldProjectionDirection n (V i)) =
      fieldProjectionDirection n (normalizedSpin n (ForwardPath.spin (layerSteps bs).length p)-
        actualSpinMean n (layerSteps bs) x) := by
    change (∑ i, fieldProjectionLinearMap n (V i)) = _
    rw [← map_sum, sum_physicalLayerIncrement]
    rfl
  have hh := gaussianHierarchyHessian_fork_layer_bound (uniformWeight_pos n) (finiteFeature n)
    bs ha hm x Finset.univ (fun i => fieldProjectionDirection n (V i))
  rw [he] at hh
  simp only [Finset.card_univ,Fintype.card_fin,length_layerCutSchedule] at hh
  simp_rw [← integral_pathLayerEnergy (uniformWeight_pos n) (finiteFeature n) bs ha,
    physicalLayerEnergy_projection n bs ha,weightedPathIncrements_eq_sum,dot_cutIncrement] at hh
  have hf i : (∫ q, ∑ j : Fin (layerCutSchedule bs).length, ((layerCutSchedule bs).get j).1 *
      (∑ l, V i l*physicalLayerIncrement n bs x q j l)^2
      ∂hierarchyPathKernel (uniformWeight n) (finiteFeature n) (layerSteps bs) x) =
      ∑ j : Fin (layerCutSchedule bs).length, ((layerCutSchedule bs).get j).1 *
      ∫ q, (∑ l, V i l*physicalLayerIncrement n bs x q j l)^2
      ∂hierarchyPathKernel (uniformWeight n) (finiteFeature n) (layerSteps bs) x := by
    rw [integral_finsetSum]
    · simp only [integral_const_mul]
    · intro j _
      exact (physicalLayerIncrement_dot_sq_integrable n bs ha (V i) x j).const_mul _
  change _ ≤ (bs.length+1:ℕ) * ∑ i, ∫ q, ∑ j, ((layerCutSchedule bs).get j).1 *
    (∑ l, V i l*physicalLayerIncrement n bs x q j l)^2
    ∂hierarchyPathKernel (uniformWeight n) (finiteFeature n) (layerSteps bs) x at hh
  simp_rw [hf] at hh
  exact hh

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 def physicalFutureLayerIncrement (n : ℕ) (common : List (GaussianStep (FeatureIndex n)))
    (bs : List (GaussianLayer (FeatureIndex n))) {P : Type} (x : P → FeatureIndex n → ℝ)
    (p : PhysicalPathState P n (common++layerSteps bs)) (i : Fin (layerCutSchedule bs).length) : Fin n → ℝ :=
  physicalLayerIncrement n bs (continuationState common (layerSteps bs) (x p.1) p.2).1
    (continuationState common (layerSteps bs) (x p.1) p.2).2 i

 def physicalFutureSusceptibility (n : ℕ) (common : List (GaussianStep (FeatureIndex n)))
    (tail : List (GaussianStep (FeatureIndex n))) {P : Type} (x : P → FeatureIndex n → ℝ)
    (p : PhysicalPathState P n (common++tail)) : ℝ :=
  physicalSusceptibility n tail (continuationState common tail (x p.1) p.2).1
    (continuationState common tail (x p.1) p.2).2

 theorem physicalFutureSusceptibility_le_double_sum (n : ℕ)
    (common : List (GaussianStep (FeatureIndex n))) (bs : List (GaussianLayer (FeatureIndex n)))
    {a : ℝ} (ha : OrderedSteps a (layerSteps bs))
    (hm : ∀ B ∈ bs, ∀ st ∈ B.2, st.1 ≤ B.1)
    {P : Type} (x : P → FeatureIndex n → ℝ) (p : PhysicalPathState P n (common++layerSteps bs)) :
    physicalFutureSusceptibility n common (layerSteps bs) x p ≤
      (bs.length+1:ℕ) * ∑ i : Fin (layerCutSchedule bs).length,
        ∑ j : Fin (layerCutSchedule bs).length, ((layerCutSchedule bs).get j).1 *
          conditionalPathAverage (uniformWeight n) (finiteFeature n) (common++layerSteps bs) x common.length
            (fun q => (∑ l, physicalFutureLayerIncrement n common bs x p i l *
              physicalFutureLayerIncrement n common bs x q j l)^2) p := by
  have hh := physicalSusceptibility_le_double_sum n bs ha hm
    (continuationState common (layerSteps bs) (x p.1) p.2).1
    (continuationState common (layerSteps bs) (x p.1) p.2).2
  have he (i j : Fin (layerCutSchedule bs).length) :=
    conditionalPathAverage_continuation (uniformWeight n) (finiteFeature n) common (layerSteps bs) x
      (fun q => (∑ l, physicalFutureLayerIncrement n common bs x p i l *
        physicalLayerIncrement n bs q.1 q.2 j l)^2) p
  change physicalFutureSusceptibility n common (layerSteps bs) x p ≤ _ at hh
  simpa only [physicalFutureLayerIncrement,continuationState_fst] using
    (hh.trans_eq (by
      apply congrArg (fun t : ℝ => (bs.length+1:ℕ)*t)
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      simpa only [physicalFutureLayerIncrement,continuationState_fst] using (he i j).symm))

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators RealInnerProductSpace

 theorem actualSpinPath_source (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {P : Type} (x : P → FeatureIndex n → ℝ) (k : ℕ) (p : PhysicalPathState P n steps) :
    actualSpinPath n steps x k p = actualSpinPath n steps (fun _ : Unit => x p.1) k ((),p.2) := by
  apply PiLp.ext
  intro i
  exact hierarchyMeanPath_source _ _ _ steps x k p.1 p.2

 theorem physicalFutureLayerIncrement_eq_cut (n : ℕ)
    (common : List (GaussianStep (FeatureIndex n))) (bs : List (GaussianLayer (FeatureIndex n)))
    {P : Type} (x : P → FeatureIndex n → ℝ) (p : PhysicalPathState P n (common++layerSteps bs))
    (i : Fin (layerCutSchedule bs).length) :
    WithLp.toLp 2 (physicalFutureLayerIncrement n common bs x p i) =
      physicalCutIncrement n (common++layerSteps bs) x
        (common.length+cutPredecessor (layerCutSchedule bs) 0 i)
        (common.length+((layerCutSchedule bs).get i).2) p := by
  unfold physicalCutIncrement
  rw [actualSpinPath_after_prefix,actualSpinPath_after_prefix,
    actualSpinPath_source n (layerSteps bs) id ((layerCutSchedule bs).get i).2,
    actualSpinPath_source n (layerSteps bs) id (cutPredecessor (layerCutSchedule bs) 0 i)]
  rfl

 theorem physicalFutureSusceptibility_le_cut_sum (n : ℕ)
    (common : List (GaussianStep (FeatureIndex n))) (bs : List (GaussianLayer (FeatureIndex n)))
    {u : ℝ} (hu : OrderedSteps u (layerSteps bs))
    (hm : ∀ B ∈ bs, ∀ st ∈ B.2, st.1 ≤ B.1)
    {P : Type} (x : P → FeatureIndex n → ℝ) (p : PhysicalPathState P n (common++layerSteps bs)) :
    physicalFutureSusceptibility n common (layerSteps bs) x p ≤
      (bs.length+1:ℕ) * ∑ i : Fin (layerCutSchedule bs).length,
        ∑ j : Fin (layerCutSchedule bs).length, ((layerCutSchedule bs).get j).1 *
          physicalCutPairSquare n (common++layerSteps bs) x common.length
            (common.length+cutPredecessor (layerCutSchedule bs) 0 i)
            (common.length+((layerCutSchedule bs).get i).2)
            (common.length+cutPredecessor (layerCutSchedule bs) 0 j)
            (common.length+((layerCutSchedule bs).get j).2) p := by
  have hh := physicalFutureSusceptibility_le_double_sum n common bs hu hm x p
  simpa only [physicalCutPairSquare,← physicalFutureLayerIncrement_eq_cut,
    PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_comm] using hh

end SKFluctuations

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 inductive CutPartition {α : Type*} (steps : List α) : ℕ → List (ℝ × ℕ) → Prop
  | nil : CutPartition steps steps.length []
  | cons {a b : ℕ} {m : ℝ} {cs : List (ℝ × ℕ)} (hab : a ≤ b)
      (tail : CutPartition steps b cs) : CutPartition steps a ((m,b)::cs)

 def layersOfCuts {ι : Type} (steps : List (GaussianStep ι)) : ℕ → List (ℝ × ℕ) → List (GaussianLayer ι)
  | _, [] => []
  | a, (m,b)::cs => (m,cutSlice steps a b)::layersOfCuts steps b cs

 theorem CutPartition.start_le {α : Type*} {steps : List α} {a : ℕ} {cs : List (ℝ × ℕ)}
    (h : CutPartition steps a cs) : a ≤ steps.length := by
  induction h with
  | nil => exact le_rfl
  | cons hab _ ih => exact hab.trans ih

 theorem CutPartition.all_steps {ι : Type} {steps : List (GaussianStep ι)} {a : ℕ}
    {cs : List (ℝ × ℕ)} (h : CutPartition steps a cs) :
    layerSteps (layersOfCuts steps a cs) = steps.drop a := by
  induction h with
  | nil => simp [layersOfCuts,layerSteps]
  | @cons a b m cs hab ht ih =>
    change cutSlice steps a b++layerSteps (layersOfCuts steps b cs) = steps.drop a
    rw [ih,cutSlice_append_drop steps hab]

 theorem length_layersOfCuts {ι : Type} (steps : List (GaussianStep ι)) (a : ℕ)
    (cs : List (ℝ × ℕ)) : (layersOfCuts steps a cs).length = cs.length := by
  induction cs generalizing a with
  | nil => rfl
  | cons c cs ih => exact congrArg Nat.succ (ih c.2)

 theorem CutPartition.shifted_schedule {ι : Type} {steps : List (GaussianStep ι)} {a : ℕ}
    {cs : List (ℝ × ℕ)} (h : CutPartition steps a cs) :
    (layerCutSchedule (layersOfCuts steps a cs)).map (fun c => (c.1,a+c.2)) =
      cs++[(1,steps.length+1)] := by
  induction h with
  | nil => rfl
  | @cons a b m cs hab ht ih =>
    simp only [layersOfCuts,layerCutSchedule,List.map_cons,List.map_map,List.cons_append,
      length_cutSlice steps hab ht.start_le]
    have hab' : a+(b-a)=b := Nat.add_sub_of_le hab
    rw [hab']
    congr 1
    convert ih using 1
    apply List.map_congr_left
    intro d _
    simp only [Function.comp_apply]
    congr 1
    omega

 theorem CutPartition.take_append_layers {ι : Type} {steps : List (GaussianStep ι)} {a : ℕ}
    {cs : List (ℝ × ℕ)} (h : CutPartition steps a cs) :
    steps.take a++layerSteps (layersOfCuts steps a cs) = steps := by
  rw [h.all_steps,List.take_append_drop]

 theorem CutPartition.ofFn {α : Type*} (steps : List α) {N : ℕ}
    (t : Fin (N+1) → ℕ) (m : Fin N → ℝ) (ht : Monotone t)
    (hend : t (Fin.last N) = steps.length) :
    CutPartition steps (t 0) (List.ofFn fun i => (m i,t i.succ)) := by
  induction N with
  | zero =>
    have ht0 : t 0 = steps.length := hend
    simpa only [List.ofFn_zero,ht0] using (CutPartition.nil (steps := steps))
  | succ N ih =>
    rw [List.ofFn_succ]
    apply CutPartition.cons (ht (by simp : (0 : Fin (N+2)) ≤ (0 : Fin (N+1)).succ))
    exact ih (fun i => t i.succ) (fun i => m i.succ)
      (fun i j hij => ht (Fin.succ_le_succ_iff.mpr hij)) hend

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

theorem cutSlice_mass_le {ι : Type} (steps : List (GaussianStep ι))
    {c : ℝ} (hc : OrderedSteps c steps) (a b : ℕ) (st : GaussianStep ι)
    (hst : st ∈ cutSlice steps a b) : st.1 ≤ physicalCutMass c steps b := by
  induction steps generalizing c a b with
  | nil => simp [cutSlice] at hst
  | cons h steps ih =>
    cases b with
    | zero => simp [cutSlice] at hst
    | succ b =>
      cases a with
      | zero =>
        simp only [cutSlice,List.drop_zero,Nat.sub_zero,List.take_succ_cons,List.mem_cons] at hst
        rcases hst with rfl | ht
        · simpa only [physicalCutMass] using physicalCutMass_monotone steps hc.2.2.2 (Nat.zero_le b)
        · simpa only [physicalCutMass] using ih hc.2.2.2 0 b (by simpa [cutSlice] using ht)
      | succ a =>
        simpa only [physicalCutMass] using ih hc.2.2.2 a b (by simpa [cutSlice] using hst)

theorem layersOfCuts_mass_bound {ι : Type} (steps : List (GaussianStep ι))
    {c : ℝ} (hc : OrderedSteps c steps) (a : ℕ) (cs : List (ℝ × ℕ))
    (hm : ∀ z ∈ cs, z.1 = physicalCutMass c steps z.2) :
    ∀ B ∈ layersOfCuts steps a cs, ∀ st ∈ B.2, st.1 ≤ B.1 := by
  induction cs generalizing a with
  | nil => simp [layersOfCuts]
  | cons z cs ih =>
    intro B hB st hst
    simp only [layersOfCuts,List.mem_cons] at hB
    rcases hB with rfl | hB
    · rw [hm z (by simp)]
      exact cutSlice_mass_le steps hc a z.2 st hst
    · exact ih z.2 (fun z hz => hm z (by simp [hz])) B hB st hst

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

def dyadicRadiusNode (s η : ℝ) (j : ℕ) : ℝ :=
  if j=0 then s else if j=1 then s+η else (2:ℝ)^(j-1)*s

@[simp] theorem dyadicRadiusNode_zero (s η : ℝ) : dyadicRadiusNode s η 0 = s := by
  simp [dyadicRadiusNode]
@[simp] theorem dyadicRadiusNode_one (s η : ℝ) : dyadicRadiusNode s η 1 = s+η := by
  simp [dyadicRadiusNode]

theorem dyadicRadiusNode_succ_succ (s η : ℝ) (j : ℕ) :
    dyadicRadiusNode s η (j+2) = (2:ℝ)^(j+1)*s := by simp [dyadicRadiusNode]

theorem dyadicRadiusNode_monotone {s η : ℝ} (hs : 0 ≤ s) (hη : 0 ≤ η) (hηs : η ≤ s) :
    Monotone (dyadicRadiusNode s η) := by
  apply monotone_nat_of_le_succ
  intro j
  rcases j with _ | j
  · simp; exact hη
  rcases j with _ | j
  · simp [dyadicRadiusNode]; linarith
  rw [dyadicRadiusNode_succ_succ,show j+2+1=(j+1)+2 by omega,dyadicRadiusNode_succ_succ]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega)) hs

theorem dyadicRadiusNode_pos {s η : ℝ} (hs : 0 < s) (hη : 0 ≤ η) (j : ℕ) :
    0 < dyadicRadiusNode s η j := by
  unfold dyadicRadiusNode
  split_ifs <;> positivity

def dyadicCutIndex (J : ℕ) (τ : ℝ → ℕ) (L : ℕ) (s η : ℝ) (j : ℕ) : ℕ :=
  if j ≤ J+1 then τ (dyadicRadiusNode s η j) else if j=J+2 then L else L+1

theorem dyadicCutIndex_zero (J : ℕ) (τ : ℝ → ℕ) (L : ℕ) (s η : ℝ) :
    dyadicCutIndex J τ L s η 0 = τ s := by simp [dyadicCutIndex]
theorem dyadicCutIndex_one (J : ℕ) (τ : ℝ → ℕ) (L : ℕ) (s η : ℝ) :
    dyadicCutIndex J τ L s η 1 = τ (s+η) := by simp [dyadicCutIndex]
theorem dyadicCutIndex_end (J : ℕ) (τ : ℝ → ℕ) (L : ℕ) (s η : ℝ) :
    dyadicCutIndex J τ L s η (J+2) = L := by simp [dyadicCutIndex]
theorem dyadicCutIndex_terminal (J : ℕ) (τ : ℝ → ℕ) (L : ℕ) (s η : ℝ) :
    dyadicCutIndex J τ L s η (J+3) = L+1 := by simp [dyadicCutIndex]

theorem dyadicCutIndex_monotone (J : ℕ) {τ : ℝ → ℕ} (hτ : Monotone τ) (L : ℕ)
    (hL : ∀ r, τ r ≤ L) {s η : ℝ} (hs : 0 ≤ s) (hη : 0 ≤ η) (hηs : η ≤ s) :
    Monotone (dyadicCutIndex J τ L s η) := by
  intro i j hij
  unfold dyadicCutIndex
  split_ifs with hi hj hj' hi' hj hj'
  · exact hτ (dyadicRadiusNode_monotone hs hη hηs hij)
  · exact hL _
  · exact (hL _).trans (Nat.le_succ L)
  all_goals omega

theorem dyadicCutIndex_measurable (J : ℕ) {τ : ℝ → ℕ} (hτ : Measurable τ)
    (L : ℕ) (η : ℝ) (j : ℕ) : Measurable (fun s => dyadicCutIndex J τ L s η j) := by
  unfold dyadicCutIndex
  split_ifs <;> try exact measurable_const
  apply hτ.comp
  unfold dyadicRadiusNode
  split_ifs <;> fun_prop

theorem physicalCutMass_terminal {ι : Type} (steps : List (GaussianStep ι)) (c : ℝ) :
    physicalCutMass c steps (steps.length+1) = 1 := by
  induction steps generalizing c with
  | nil => rfl
  | cons st steps ih => exact ih st.1

def physicalDyadicCuts (J : ℕ) (τ : ℝ → ℕ) (L : ℕ) (η : ℝ) : Fin (J+4) → ℝ → ℕ :=
  fun i s => dyadicCutIndex J τ L s η i.val

def physicalDyadicMass {ι : Type} (steps : List (GaussianStep ι)) (c : ℝ)
    (J : ℕ) (τ : ℝ → ℕ) (η : ℝ) : Fin (J+3) → ℝ → ℝ :=
  fun i s => physicalCutMass c steps (physicalDyadicCuts J τ steps.length η i.succ s)

theorem physicalDyadicCuts_partition {ι : Type} (steps : List (GaussianStep ι)) (c : ℝ)
    (J : ℕ) {τ : ℝ → ℕ} (hτ : Monotone τ) (hL : ∀ r, τ r ≤ steps.length)
    {s η : ℝ} (hs : 0 ≤ s) (hη : 0 ≤ η) (hηs : η ≤ s) :
    CutPartition steps (physicalDyadicCuts J τ steps.length η 0 s)
      (List.ofFn fun i : Fin (J+2) =>
        (physicalDyadicMass steps c J τ η i.castSucc s,
          physicalDyadicCuts J τ steps.length η i.succ.castSucc s)) := by
  apply CutPartition.ofFn steps
    (fun i : Fin (J+3) => physicalDyadicCuts J τ steps.length η i.castSucc s)
    (fun i => physicalDyadicMass steps c J τ η i.castSucc s)
  · exact fun i j hij => dyadicCutIndex_monotone J hτ steps.length hL hs hη hηs hij
  · exact dyadicCutIndex_end J τ steps.length s η

theorem physicalDyadicCuts_mass_bound {ι : Type} (steps : List (GaussianStep ι))
    {c : ℝ} (hc : OrderedSteps c steps) (J : ℕ) (τ : ℝ → ℕ) (s η : ℝ) :
    ∀ B ∈ layersOfCuts steps (physicalDyadicCuts J τ steps.length η 0 s)
      (List.ofFn fun i : Fin (J+2) =>
        (physicalDyadicMass steps c J τ η i.castSucc s,
          physicalDyadicCuts J τ steps.length η i.succ.castSucc s)),
      ∀ st ∈ B.2, st.1 ≤ B.1 := by
  apply layersOfCuts_mass_bound steps hc
  intro z hz
  rw [List.mem_ofFn] at hz
  obtain ⟨i,rfl⟩ := hz
  rfl

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

variable {r₀ u₀ c : ℝ} {k M : ℝ → ℝ}
variable (hr : r₀≤1) (hu : u₀≤1) (hc : 0<c) (hk : ContinuousOn k (Icc r₀ 1))
  (hkc : ∀ t ∈ Icc r₀ 1, c≤k t) (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)
  (α : inverseIntegralConstraints r₀ u₀ k M)

 def physicalQuantileGrid {ι : Type} (steps : List (GaussianStep ι)) (ha : OrderedSteps 0 steps)
    (j : Fin (steps.length+2)) : ℝ :=
  (constrainedQuantile hr hc hk hkc hm hM α
    ⟨max u₀ (physicalCutMass 0 steps j.val),le_max_left _ _,
      max_le hu (physicalCutMass_mem steps ha j.val).2⟩).val

 theorem physicalQuantileGrid_spec {ι : Type} (steps : List (GaussianStep ι)) (ha : OrderedSteps 0 steps)
    (j : Fin (steps.length+2)) :
    α.val.val (physicalQuantileGrid hr hu hc hk hkc hm hM α steps ha j)=
      max u₀ (physicalCutMass 0 steps j.val) := constrainedQuantile_spec ..

 theorem physicalQuantileGrid_mem {ι : Type} (steps : List (GaussianStep ι)) (ha : OrderedSteps 0 steps)
    (j : Fin (steps.length+2)) :
    physicalQuantileGrid hr hu hc hk hkc hm hM α steps ha j ∈ Icc r₀ 1 :=
  (constrainedQuantile hr hc hk hkc hm hM α _).property

 theorem physicalQuantileGrid_mono {ι : Type} (steps : List (GaussianStep ι)) (ha : OrderedSteps 0 steps) :
    Monotone (physicalQuantileGrid hr hu hc hk hkc hm hM α steps ha) := by
  intro i j hij
  exact (inverseConstraintOrderIso hr hc hk hkc hm hM α).symm.monotone
    (max_le_max_left u₀ (physicalCutMass_monotone steps ha hij))

 theorem physicalQuantileGrid_coord {ι : Type} (steps : List (GaussianStep ι)) (ha : OrderedSteps 0 steps)
    (j : Fin (steps.length+2)) (hj : u₀ ≤ physicalCutMass 0 steps j.val) :
    physicalCutMass 0 steps j.val=α.val.val (physicalQuantileGrid hr hu hc hk hkc hm hM α steps ha j) := by
  rw [physicalQuantileGrid_spec,max_eq_right hj]

 theorem physicalQuantileGrid_last {ι : Type} (steps : List (GaussianStep ι)) (ha : OrderedSteps 0 steps) :
    physicalQuantileGrid hr hu hc hk hkc hm hM α steps ha (Fin.last (steps.length+1))=1 := by
  have hs := physicalQuantileGrid_spec hr hu hc hk hkc hm hM α steps ha (Fin.last (steps.length+1))
  have ht := physicalCutMass_terminal steps 0
  simp only [Fin.val_last,ht,max_eq_right hu] at hs
  apply (inverseConstraint_strictMonoOn hc hk hkc α.property).injOn
    (physicalQuantileGrid_mem hr hu hc hk hkc hm hM α steps ha _) ⟨hr,le_rfl⟩
  simpa only [α.property.2.1] using hs

 theorem physicalQuantileGrid_first {ι : Type} (steps : List (GaussianStep ι)) (ha : OrderedSteps 0 steps)
    (hu₀ : 0≤u₀) : physicalQuantileGrid hr hu hc hk hkc hm hM α steps ha 0=r₀ := by
  have hs := physicalQuantileGrid_spec hr hu hc hk hkc hm hM α steps ha 0
  have hz : physicalCutMass 0 steps 0=0 := by cases steps <;> rfl
  simp only [Fin.val_zero,hz,max_eq_left hu₀] at hs
  apply (inverseConstraint_strictMonoOn hc hk hkc α.property).injOn
    (physicalQuantileGrid_mem hr hu hc hk hkc hm hM α steps ha _) ⟨le_rfl,hr⟩
  simpa only [α.property.1] using hs

 theorem physicalQuantileGrid_mesh {ι : Type} (steps : List (GaussianStep ι)) (ha : OrderedSteps 0 steps)
    {ε : ℝ} (hmesh : ∀ j : Fin (steps.length+1),
      physicalCutMass 0 steps (j.val+1)-physicalCutMass 0 steps j.val ≤ ε) :
    ∀ j : Fin (steps.length+1),
      physicalQuantileGrid hr hu hc hk hkc hm hM α steps ha j.succ-
        physicalQuantileGrid hr hu hc hk hkc hm hM α steps ha j.castSucc ≤ ε/c := by
  intro j
  have hjs : j.castSucc ≤ j.succ := by change j.val ≤ j.val+1; omega
  have hb := inverseConstraint_lower_slope hk hkc α.property
    (physicalQuantileGrid_mem hr hu hc hk hkc hm hM α steps ha j.castSucc)
    (physicalQuantileGrid_mem hr hu hc hk hkc hm hM α steps ha j.succ)
    (physicalQuantileGrid_mono hr hu hc hk hkc hm hM α steps ha hjs)
  rw [physicalQuantileGrid_spec,physicalQuantileGrid_spec] at hb
  have hmd : physicalCutMass 0 steps j.val ≤ physicalCutMass 0 steps (j.val+1) :=
    physicalCutMass_monotone steps ha (Nat.le_succ _)
  have hmax : max u₀ (physicalCutMass 0 steps (j.val+1))-max u₀ (physicalCutMass 0 steps j.val) ≤
      physicalCutMass 0 steps (j.val+1)-physicalCutMass 0 steps j.val := by
    rcases le_total u₀ (physicalCutMass 0 steps j.val) with h | h
    · rw [max_eq_right h,max_eq_right (h.trans hmd)]
    · rw [max_eq_left h]
      rcases le_total u₀ (physicalCutMass 0 steps (j.val+1)) with h' | h'
      · rw [max_eq_right h']; linarith
      · rw [max_eq_left h']; linarith
  apply (le_div_iff₀ hc).mpr
  have he := (hb.trans hmax).trans (hmesh j)
  simpa only [mul_comm] using he

 theorem sampled_physicalMass_mesh {ι : Type} (q : ℝ → ι → ℝ≥0)
    {a ε : ℝ} (as : List PositiveMass) (hm : PartitionMesh ε a as)
    (j : Fin ((sampleClockSteps q a as).length+1)) :
    physicalCutMass a (sampleClockSteps q a as) (j.val+1)-
      physicalCutMass a (sampleClockSteps q a as) j.val ≤ ε := by
  induction as generalizing a with
  | nil =>
    have hj : j=0 := by apply Fin.ext; change j.val=0; have hh := j.isLt; simp [sampleClockSteps] at hh; omega
    subst j
    exact hm
  | cons b bs ih =>
    refine Fin.cases ?_ (fun l => ?_) j
    · simpa only [Fin.val_zero,zero_add,sampleClockSteps,physicalCutMass] using hm.1
    · exact ih hm.2 l

end SKFluctuations

 

 

namespace SKFluctuations
open Set
open scoped BigOperators

 def radiusGridCut {N : ℕ} (r : Fin (N+2) → ℝ) (s : ℝ) : ℕ :=
  min N ((Finset.univ.filter fun i => r i < s).card-1)

 theorem radiusGridCut_le {N : ℕ} (r : Fin (N+2) → ℝ) (s : ℝ) : radiusGridCut r s ≤ N :=
  min_le_left _ _

 theorem radiusGridCut_monotone {N : ℕ} (r : Fin (N+2) → ℝ) : Monotone (radiusGridCut r) := by
  intro s t hst
  apply min_le_min_left
  apply Nat.sub_le_sub_right
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hi ⊢
  exact hi.trans_le hst

 theorem radiusGridCut_cell {N : ℕ} (r : Fin (N+2) → ℝ) (hr : Monotone r)
    (j : Fin (N+1)) {s : ℝ} (hs : s ∈ Ioc (r j.castSucc) (r j.succ)) :
    radiusGridCut r s = j.val := by
  have he : (Finset.univ.filter fun i => r i < s) = Finset.Iic j.castSucc := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Iic]
    constructor
    · intro hi
      by_contra h
      have hij : j.succ ≤ i := by
        change j.val+1 ≤ i.val
        have hj : ¬i.val ≤ j.val := h
        omega
      exact (not_lt_of_ge (hs.2.trans (hr hij))) hi
    · intro hi
      exact (hr hi).trans_lt hs.1
  rw [radiusGridCut,he,Fin.card_Iic]
  simp only [Fin.val_castSucc,Nat.add_sub_cancel]
  exact min_eq_right (Nat.le_of_lt_succ j.isLt)

 theorem radiusGridCell_disjoint {N : ℕ} (r : Fin (N+2) → ℝ) (hr : Monotone r) :
    Pairwise (fun i j : Fin (N+1) => Disjoint (Ioc (r i.castSucc) (r i.succ))
      (Ioc (r j.castSucc) (r j.succ))) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro s hsi hsj
  exact hij (Fin.ext ((radiusGridCut_cell r hr i hsi).symm.trans (radiusGridCut_cell r hr j hsj)))

end SKFluctuations

 

 

namespace SKFluctuations
open Set
open scoped BigOperators

 theorem exists_radiusGridCell {N : ℕ} (r : Fin (N+2) → ℝ) {s : ℝ}
    (h₀ : r 0<s) (h₁ : s ≤ r (Fin.last (N+1))) :
    ∃ j : Fin (N+1), s ∈ Ioc (r j.castSucc) (r j.succ) := by
  classical
  let K := Finset.univ.filter (fun i => r i<s)
  have hK : K.Nonempty := ⟨0,by simp [K,h₀]⟩
  let m := K.max' hK
  have hm : m ∈ K := Finset.max'_mem K hK
  have hms : r m<s := (Finset.mem_filter.mp hm).2
  have hmne : m≠Fin.last (N+1) := by intro h; rw [h] at hms; linarith
  have hmlt : m.val<N+1 := by
    have hh := m.isLt
    have hh' : m.val≠N+1 := by intro h; exact hmne (Fin.ext h)
    omega
  let j : Fin (N+1) := ⟨m.val,hmlt⟩
  have hj : j.castSucc=m := Fin.ext rfl
  refine ⟨j,by simpa only [hj] using hms,?_⟩
  by_contra hn
  have hin : j.succ ∈ K := by simp only [K,Finset.mem_filter,Finset.mem_univ,true_and]; exact lt_of_not_ge hn
  have hh := Finset.le_max' K j.succ hin
  change j.val+1 ≤ m.val at hh
  dsimp [j] at hh
  omega

 def radiusGridPoint {N : ℕ} (r : Fin (N+2) → ℝ) (s : ℝ) : ℝ :=
    r ⟨radiusGridCut r s,lt_of_le_of_lt (radiusGridCut_le r s) (by omega)⟩

 theorem radiusGridPoint_bounds {N : ℕ} (r : Fin (N+2) → ℝ) (hr : Monotone r)
    {s δ : ℝ} (h₀ : r 0<s) (h₁ : s ≤ r (Fin.last (N+1)))
    (hmesh : ∀ j : Fin (N+1), r j.succ-r j.castSucc ≤ δ) :
    s-δ ≤ radiusGridPoint r s ∧ radiusGridPoint r s<s := by
  obtain ⟨j,hj⟩ := exists_radiusGridCell r h₀ h₁
  have he : radiusGridPoint r s=r j.castSucc := by
    unfold radiusGridPoint
    congr 1
    exact Fin.ext (radiusGridCut_cell r hr j hj)
  rw [he]
  exact ⟨by linarith [hmesh j,hj.2],hj.1⟩

 theorem radiusGridPoint_mem {N : ℕ} (r : Fin (N+2) → ℝ) (hr : Monotone r) (s : ℝ) :
    radiusGridPoint r s ∈ Icc (r 0) (r (Fin.last (N+1))) := by
  exact ⟨hr (Fin.zero_le _),hr (Fin.le_last _)⟩

 theorem radiusGridPoint_monotone {N : ℕ} (r : Fin (N+2) → ℝ) (hr : Monotone r) :
    Monotone (radiusGridPoint r) := by
  intro s t hst
  exact hr (radiusGridCut_monotone r hst)

 theorem radiusSampledClock_growth {N : ℕ} (r : Fin (N+2) → ℝ) (hr : Monotone r)
    {H : ℝ → ℝ} {c δ s t : ℝ} (hc : 0 ≤ c) (hst : s ≤ t)
    (hs : r 0<s) (ht : t ≤ r (Fin.last (N+1)))
    (hmesh : ∀ j : Fin (N+1), r j.succ-r j.castSucc ≤ δ)
    (hg : ∀ a ∈ Icc (r 0) (r (Fin.last (N+1))),
      ∀ b ∈ Icc (r 0) (r (Fin.last (N+1))), a ≤ b → c*(b-a) ≤ H b-H a) :
    c*(t-s-δ) ≤ H (radiusGridPoint r t)-H (radiusGridPoint r s) := by
  have hs' := radiusGridPoint_bounds r hr hs (hst.trans ht) hmesh
  have ht' := radiusGridPoint_bounds r hr (hs.trans_le hst) ht hmesh
  have hh := hg _ (radiusGridPoint_mem r hr s) _ (radiusGridPoint_mem r hr t)
    (radiusGridPoint_monotone r hr hst)
  have hdist : t-s-δ ≤ radiusGridPoint r t-radiusGridPoint r s := by linarith
  exact (mul_le_mul_of_nonneg_left hdist hc).trans hh

 theorem radiusSampledClock_growth_local {N : ℕ} (r : Fin (N+2) → ℝ) (hr : Monotone r)
    {H : ℝ → ℝ} {c δ s t : ℝ} (hc : 0 ≤ c) (hst : s ≤ t)
    (hs : r 0<s) (ht : t ≤ r (Fin.last (N+1)))
    (hmesh : ∀ j : Fin (N+1), r j.succ-r j.castSucc ≤ δ)
    (hg : ∀ a ∈ Icc (s-δ) t, ∀ b ∈ Icc (s-δ) t,
      a ≤ b → c*(b-a) ≤ H b-H a) :
    c*(t-s-δ) ≤ H (radiusGridPoint r t)-H (radiusGridPoint r s) := by
  have hs' := radiusGridPoint_bounds r hr hs (hst.trans ht) hmesh
  have ht' := radiusGridPoint_bounds r hr (hs.trans_le hst) ht hmesh
  have hh := hg _ ⟨hs'.1,hs'.2.le.trans hst⟩ _
    ⟨by linarith [ht'.1],ht'.2.le⟩ (radiusGridPoint_monotone r hr hst)
  have hdist : t-s-δ ≤ radiusGridPoint r t-radiusGridPoint r s := by linarith
  exact (mul_le_mul_of_nonneg_left hdist hc).trans hh

end SKFluctuations

end

end OAI
