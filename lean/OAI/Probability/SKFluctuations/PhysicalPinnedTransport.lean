import Mathlib
import OAI.Probability.SKFluctuations.PhysicalQuantileSampling

namespace OAI

/-! Physical Pinned Transport. -/

noncomputable section


namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal ENNReal BigOperators
variable {n d : ℕ}

 theorem physicalPinnedPair_realize (q₀ : FeatureIndex n → ℝ≥0)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (e : Fin d ≃ Fin (steps.length+1) × FeatureIndex n)
    (k : Fin (steps.length+1) → ℝ) (σ : Spin n) (z : Fin d → ℝ) :
    let p := realizeRootedPath q₀ steps ((flattenDrivers e).symm z) σ
    physicalPinnedPair (uniformWeight n) (finiteFeature n) (spinSource n) steps 0 k p.1 p.2 =
      actualPinnedPair q₀ steps ha e k σ z := by
  exact physicalPinnedPair_eq_frames (uniformWeight n) (uniformWeight_pos n)
    (finiteFeature n) (spinSource n) steps ha
    ((scaleDriver q₀).comp (flatLevelProjection e 0))
    (fun j => flatLevelProjection e j.succ) k z σ

 theorem physicalPinnedPair_map_eq (q₀ : FeatureIndex n → ℝ≥0)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (e : Fin d ≃ Fin (steps.length+1) × FeatureIndex n)
    (k : Fin (steps.length+1) → ℝ) :
    (rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps).map
      (Function.uncurry (physicalPinnedPair (uniformWeight n) (finiteFeature n)
        (spinSource n) steps 0 k)) = actualPlantedPairLaw q₀ steps ha e k := by
  have hm := physicalPinnedPair_measurable (uniformWeight_pos n)
    (finiteFeature n) (spinSource n) steps ha k
  rw [rootedHierarchyPathLaw_eq_flat (uniformWeight_pos n) (finiteFeature n) q₀ steps ha e]
  rw [Measure.map_finset_sum hm.aemeasurable]
  unfold actualPlantedPairLaw
  apply Finset.sum_congr rfl
  intro σ _
  have hr : Measurable (fun z => realizeRootedPath q₀ steps ((flattenDrivers e).symm z) σ) :=
    (measurable_realizeRootedPath q₀ steps σ).comp (flattenDrivers e).symm.continuous.measurable
  rw [Measure.map_map hm hr]
  congr 1
  funext z
  exact physicalPinnedPair_realize q₀ steps ha e k σ z

 

 theorem physical_planted_centered_moment_le (q₀ : FeatureIndex n → ℝ≥0)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (e : Fin d ≃ Fin (steps.length+1) × FeatureIndex n)
    (k : Fin (steps.length+1) → ℝ) {p : ℝ} (hp : 2 ≤ p) :
    let μ := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps
    let LW := Function.uncurry (physicalPinnedPair (uniformWeight n) (finiteFeature n)
      (spinSource n) steps 0 k)
    (momentNorm μ (fun x => (LW x).1 - ∫ y, (LW y).1 ∂μ) p)^2 ≤
      (1+p^2/3)*momentNorm μ (fun x => (LW x).2) (p/2) := by
  dsimp only
  have hm := physicalPinnedPair_measurable (uniformWeight_pos n)
    (finiteFeature n) (spinSource n) steps ha k
  have h := actual_planted_centered_moment_le q₀ steps ha e k hp
  dsimp only at h
  rw [← physicalPinnedPair_map_eq q₀ steps ha e k,
    integral_map hm.aemeasurable continuous_fst.aestronglyMeasurable] at h
  simp only [momentNorm] at h ⊢
  rw [eLpNorm_map_measure (g := fun x : ℝ × ℝ => x.1 -
      ∫ y, (Function.uncurry (physicalPinnedPair (uniformWeight n) (finiteFeature n)
        (spinSource n) steps 0 k) y).1
        ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps)
      (continuous_fst.sub continuous_const).aestronglyMeasurable hm.aemeasurable,
    eLpNorm_map_measure continuous_snd.aestronglyMeasurable hm.aemeasurable] at h
  exact h

 theorem physical_planted_variance_le (q₀ : FeatureIndex n → ℝ≥0)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (e : Fin d ≃ Fin (steps.length+1) × FeatureIndex n)
    (k : Fin (steps.length+1) → ℝ) :
    let μ := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps
    let LW := Function.uncurry (physicalPinnedPair (uniformWeight n) (finiteFeature n)
      (spinSource n) steps 0 k)
    variance (fun x => (LW x).1) μ ≤ ∫ x, (LW x).2 ∂μ := by
  dsimp only
  have hm := physicalPinnedPair_measurable (uniformWeight_pos n)
    (finiteFeature n) (spinSource n) steps ha k
  have h := actual_planted_variance_le q₀ steps ha e k
  rw [← physicalPinnedPair_map_eq q₀ steps ha e k,
    variance_map measurable_fst.aemeasurable hm.aemeasurable,
    integral_map hm.aemeasurable continuous_snd.aestronglyMeasurable] at h
  exact h

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal ENNReal BigOperators

 theorem driverMean_spin (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    (x : FeatureIndex n → ℝ) :
    driverMean (uniformWeight n) (finiteFeature n) steps (.id ℝ _) (spinSource n) x =
      actualSpinMean n steps x := by
  funext i
  simp only [driverMean, actualSpinMean, ContinuousLinearMap.id_apply,
    normalizedSpin, finiteFeature_source]

 theorem sum_spinSource (n : ℕ) (V : Fin n → ℝ) :
    (∑ i, V i • spinSource n i) = fieldProjectionDirection n V := by
  classical
  ext j
  cases j with
  | inl j => simp [spinSource, fieldProjectionDirection, Pi.single_apply, div_eq_mul_inv]
  | inr j => simp [spinSource, fieldProjectionDirection]

 theorem driverSource_spin (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    (x : FeatureIndex n → ℝ) (σ : Spin n) :
    driverSource (uniformWeight n) (finiteFeature n) steps (.id ℝ _) (spinSource n) σ x =
      fieldProjectionDirection n (normalizedSpin n σ-actualSpinMean n steps x) := by
  simp only [driverSource, driverMean_spin, finiteFeature_source]
  exact sum_spinSource n _

 
def physicalSpinL (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    (x : FeatureIndex n → ℝ) (σ : Spin n) : ℝ :=
  (∑ i, normalizedSpin n σ i * actualSpinMean n steps x i) -
    (1/2:ℝ) * ∑ i, (actualSpinMean n steps x i)^2

 theorem driverObservable_spin (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    (x : FeatureIndex n → ℝ) (σ : Spin n) :
    driverObservable (uniformWeight n) (finiteFeature n) steps (.id ℝ _)
      (spinSource n) σ x = physicalSpinL n steps x σ := by
  simp only [driverObservable, physicalSpinL, driverMean_spin, finiteFeature_source,
    normalizedSpin, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

 theorem driverEnergy_spin (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {a : ℝ} (ha : OrderedSteps a steps) (x : FeatureIndex n → ℝ)
    (p : ForwardPath (FeatureIndex n → ℝ) (Spin n) steps.length) :
    driverEnergy (uniformWeight n) (finiteFeature n) steps (.id ℝ _) (spinSource n)
      (ForwardPath.spin steps.length p) x = physicalSusceptibility n steps x p := by
  rw [driverEnergy_eq (uniformWeight_pos n) (finiteFeature n) steps ha, driverSource_spin]
  rfl

 theorem physicalNodePair_spin (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {a : ℝ} (ha : OrderedSteps a steps) (k : ℝ) (x : FeatureIndex n → ℝ)
    (p : ForwardPath (FeatureIndex n → ℝ) (Spin n) steps.length) :
    physicalNodePair (uniformWeight n) (finiteFeature n) (spinSource n) steps k x
      (ForwardPath.spin steps.length p) =
      (k*physicalSpinL n steps x (ForwardPath.spin steps.length p),
        k^2*physicalSusceptibility n steps x p) := by
  rw [physicalNodePair, driverObservable_spin, driverEnergy_spin n steps ha]

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 def physicalCutSusceptibility (n : ℕ) : (steps : List (GaussianStep (FeatureIndex n))) →
    {P : Type} → (P → FeatureIndex n → ℝ) → ℕ → PhysicalPathState P n steps → ℝ
  | steps, _, x, 0, p => physicalSusceptibility n steps (x p.1) p.2
  | [], _, _, _+1, _ => 0
  | _::steps, _, x, k+1, p => physicalCutSusceptibility n steps
      (fun q => x q.1+q.2) k ((p.1,p.2.1),p.2.2)

 theorem physicalCutSusceptibility_at_prefix (n : ℕ)
    (pre tail : List (GaussianStep (FeatureIndex n))) {P : Type}
    (x : P → FeatureIndex n → ℝ) (p : PhysicalPathState P n (pre++tail)) :
    physicalCutSusceptibility n (pre++tail) x pre.length p =
      physicalFutureSusceptibility n pre tail x p := by
  induction pre generalizing P with
  | nil => simp only [physicalCutSusceptibility,physicalFutureSusceptibility,
      continuationState,List.length_nil,List.nil_append]
  | cons st pre ih =>
    exact ih (fun q : P × (FeatureIndex n → ℝ) => x q.1+q.2) ((p.1,p.2.1),p.2.2)

 theorem physicalCutSusceptibility_nonneg (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {c : ℝ} (hc : OrderedSteps c steps) {P : Type} (x : P → FeatureIndex n → ℝ)
    (k : ℕ) (p : PhysicalPathState P n steps) :
    0 ≤ physicalCutSusceptibility n steps x k p := by
  induction steps generalizing c P k with
  | nil =>
    cases k with
    | zero => exact gaussianHierarchyHessian_nonneg (uniformWeight_pos n) (finiteFeature n) [] hc _ _
    | succ k => exact le_rfl
  | cons st steps ih =>
    cases k with
    | zero => exact gaussianHierarchyHessian_nonneg (uniformWeight_pos n) (finiteFeature n) (st::steps) hc _ _
    | succ k => exact ih hc.2.2.2 (fun q : P × (FeatureIndex n → ℝ) => x q.1+q.2) k ((p.1,p.2.1),p.2.2)

end SKFluctuations
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 theorem cutPredecessor_shift (cs : List (ℝ × ℕ)) (a d : ℕ) (i : Fin cs.length) :
    cutPredecessor (cs.map (fun c => (c.1,d+c.2))) (d+a)
      (Fin.cast (List.length_map (f := fun c : ℝ × ℕ => (c.1,d+c.2))).symm i) =
      d+cutPredecessor cs a i := by
  induction cs generalizing a with
  | nil => exact Fin.elim0 i
  | cons c cs ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact ih c.2 j

 def schedulePairSum (cs : List (ℝ × ℕ)) (a : ℕ)
    (F : ℕ → ℕ → ℕ → ℕ → ℝ) : ℝ :=
    ∑ i : Fin cs.length, ∑ j : Fin cs.length,
      (cs.get j).1*F (cutPredecessor cs a i) (cs.get i).2
        (cutPredecessor cs a j) (cs.get j).2

 theorem schedulePairSum_shift (cs : List (ℝ × ℕ)) (a d : ℕ)
    (F : ℕ → ℕ → ℕ → ℕ → ℝ) :
    schedulePairSum (cs.map (fun c => (c.1,d+c.2))) (d+a) F =
      schedulePairSum cs a (fun v w b e => F (d+v) (d+w) (d+b) (d+e)) := by
  let e : Fin cs.length ≃ Fin (cs.map (fun c => (c.1,d+c.2))).length :=
    finCongr (List.length_map (f := fun c : ℝ × ℕ => (c.1,d+c.2))).symm
  unfold schedulePairSum
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  simp only [e,finCongr_apply,cutPredecessor_shift,List.get_eq_getElem,List.getElem_map,
    Fin.val_cast]

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal ENNReal BigOperators

theorem physicalPinnedPair_snd_eq_sum (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps)
    (k : Fin (steps.length+1) → ℝ) {P : Type} (x : P → FeatureIndex n → ℝ)
    (p : PhysicalPathState P n steps) :
    (physicalPinnedPair (uniformWeight n) (finiteFeature n) (spinSource n)
      steps a k (x p.1) p.2).2 =
      ∑ j : Fin (steps.length+1), pathMassDifferences steps a j * (k j)^2 *
        physicalCutSusceptibility n steps x j.val p := by
  induction steps generalizing a P with
  | nil =>
    change (1-a)*(physicalNodePair (uniformWeight n) (finiteFeature n) (spinSource n)
      [] (k 0) (x p.1) p.2).2 = _
    have he := congrArg Prod.snd (physicalNodePair_spin n [] ha (k 0) (x p.1) p.2)
    change (physicalNodePair (uniformWeight n) (finiteFeature n) (spinSource n)
      [] (k 0) (x p.1) p.2).2 = (k 0)^2 * physicalSusceptibility n [] (x p.1) p.2 at he
    rw [he]
    conv_rhs => erw [Fin.sum_univ_one]
    simp only [pathMassDifferences,physicalCutSusceptibility]
    ring
  | cons st steps ih =>
    rcases st with ⟨m,q⟩
    change (m-a)*(physicalNodePair (uniformWeight n) (finiteFeature n) (spinSource n)
      ((m,q)::steps) (k 0) (x p.1) (ForwardPath.spin steps.length p.2.2)).2 +
      (physicalPinnedPair (uniformWeight n) (finiteFeature n) (spinSource n)
        steps m (Fin.tail k) (x p.1+p.2.1) p.2.2).2 = _
    have he := congrArg Prod.snd (physicalNodePair_spin n ((m,q)::steps) ha (k 0) (x p.1) p.2)
    change (physicalNodePair (uniformWeight n) (finiteFeature n) (spinSource n)
      ((m,q)::steps) (k 0) (x p.1) (ForwardPath.spin steps.length p.2.2)).2 =
      (k 0)^2 * physicalSusceptibility n ((m,q)::steps) (x p.1) p.2 at he
    rw [he,ih ha.2.2.2 (Fin.tail k) (fun z : P × (FeatureIndex n → ℝ) => x z.1+z.2)
      ((p.1,p.2.1),p.2.2)]
    conv_rhs => erw [Fin.sum_univ_succ]
    simp only [physicalCutSusceptibility,pathMassDifferences,Fin.cons_zero,Fin.cons_succ,
      Fin.val_zero,Fin.val_succ,Fin.tail]
    congr 1
    ring

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 theorem physicalCutSusceptibility_le_schedule (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {c : ℝ} (hc : OrderedSteps c steps)
    {a : ℕ} {cs : List (ℝ × ℕ)} (h : CutPartition steps a cs)
    (hm : ∀ B ∈ layersOfCuts steps a cs, ∀ st ∈ B.2, st.1 ≤ B.1)
    {P : Type} (x : P → FeatureIndex n → ℝ) (p : PhysicalPathState P n steps) :
    physicalCutSusceptibility n steps x a p ≤ (cs.length+1:ℕ) *
      schedulePairSum (cs++[(1,steps.length+1)]) a
        (fun v w b e => physicalCutPairSquare n steps x a v w b e p) := by
  have ht := h.take_append_layers
  have hs := h.shifted_schedule
  have hp : (steps.take a).length = a := List.length_take_of_le h.start_le
  have hb := length_layersOfCuts steps a cs
  have hc' := orderedSteps_drop_cutMass steps hc a
  rw [← h.all_steps] at hc'
  generalize hpre : steps.take a = pre at ht hp
  generalize hbs : layersOfCuts steps a cs = bs at ht hs hb hc' hm
  subst steps
  rw [← hp,physicalCutSusceptibility_at_prefix]
  have hh := physicalFutureSusceptibility_le_cut_sum n pre bs hc' hm x p
  rw [← hs,← hb]
  rw [← hp]
  have he := schedulePairSum_shift (layerCutSchedule bs) 0 pre.length
    (fun v w b e => physicalCutPairSquare n (pre++layerSteps bs) x pre.length v w b e p)
  simp only [Nat.add_zero] at he
  rw [he]
  simpa only [schedulePairSum] using hh

end SKFluctuations

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 theorem cutPredecessor_lookup (cs : List (ℝ × ℕ)) (a : ℕ) (i : Fin cs.length) :
    cutPredecessor cs a i = ((a::cs.map Prod.snd)[i.val]?).getD 0 := by
  induction cs generalizing a with
  | nil => exact Fin.elim0 i
  | cons c cs ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact ih c.2 j

 theorem cutPredecessor_ofFn {N : ℕ} (m : Fin N → ℝ) (t : Fin (N+1) → ℕ)
    (i : Fin N) :
    cutPredecessor (List.ofFn fun j => (m j,t j.succ)) (t 0)
      (Fin.cast (List.length_ofFn).symm i) = t i.castSucc := by
  rw [cutPredecessor_lookup]
  have he : t 0::(List.ofFn fun j => (m j,t j.succ)).map Prod.snd = List.ofFn t := by
    rw [List.map_ofFn]
    exact List.ofFn_succ.symm
  rw [he]
  simp only [Fin.val_cast,List.getElem?_ofFn,show i.val < N+1 by omega,↓reduceDIte,
    Option.getD_some]
  exact congrArg t (Fin.ext rfl)

 theorem schedulePairSum_ofFn {N : ℕ} (m : Fin N → ℝ) (t : Fin (N+1) → ℕ)
    (F : ℕ → ℕ → ℕ → ℕ → ℝ) :
    schedulePairSum (List.ofFn fun j => (m j,t j.succ)) (t 0) F =
      ∑ i : Fin N, ∑ j : Fin N, m j*F (t i.castSucc) (t i.succ) (t j.castSucc) (t j.succ) := by
  let e : Fin N ≃ Fin (List.ofFn fun j => (m j,t j.succ)).length := finCongr List.length_ofFn.symm
  unfold schedulePairSum
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  simp only [e,finCongr_apply,cutPredecessor_ofFn,List.get_ofFn,Fin.cast_cast,Fin.cast_eq_self]

end SKFluctuations.Hierarchy
namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 theorem physicalCutSusceptibility_le_array (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {c : ℝ} (hc : OrderedSteps c steps)
    {K : ℕ} (m : Fin (K+1) → ℝ) (t : Fin (K+2) → ℕ)
    (hterm : t (Fin.last (K+1)) = steps.length+1) (hmterm : m (Fin.last K)=1)
    (h : CutPartition steps (t 0)
      (List.ofFn fun i : Fin K => (m i.castSucc,t i.succ.castSucc)))
    (hm : ∀ B ∈ layersOfCuts steps (t 0)
      (List.ofFn fun i : Fin K => (m i.castSucc,t i.succ.castSucc)), ∀ st ∈ B.2, st.1 ≤ B.1)
    {P : Type} (x : P → FeatureIndex n → ℝ) (p : PhysicalPathState P n steps) :
    physicalCutSusceptibility n steps x (t 0) p ≤ (K+1:ℕ)*
      ∑ i : Fin (K+1), ∑ j : Fin (K+1), m j*
        physicalCutPairSquare n steps x (t 0) (t i.castSucc) (t i.succ) (t j.castSucc) (t j.succ) p := by
  have hh := physicalCutSusceptibility_le_schedule n steps hc h hm x p
  have he : (List.ofFn fun i : Fin K => (m i.castSucc,t i.succ.castSucc))++[(1,steps.length+1)] =
      List.ofFn (fun i : Fin (K+1) => (m i,t i.succ)) := by
    rw [List.ofFn_succ']
    simp only [List.concat_eq_append,Fin.castSucc_succ,Fin.succ_last,hterm,hmterm]
  simpa only [List.length_ofFn,he,schedulePairSum_ofFn] using hh

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 theorem projection_weight_scale_bound {N a D D₀ C z Q m S H : ℝ}
    (hN : 0 < N) (ha : 0 < a) (hD₀ : 0 < D₀) (hD : D₀ ≤ D)
    (hm : 0 ≤ m) (hS : 0 ≤ S) (hH : 0 ≤ H) (hscale : m*S ≤ H*a^2) :
    m*((C*z^2/(a*Real.sqrt (N*D)))^2*(2*Q)^2*S) ≤
      4*C^2*z^4*Q^2*H/(N*D₀) := by
  have hDp : 0 < D := hD₀.trans_le hD
  let A := 4*C^2*z^4*Q^2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have he : m*((C*z^2/(a*Real.sqrt (N*D)))^2*(2*Q)^2*S) =
      (A/(N*D))*(m*S/a^2) := by
    simp only [div_pow,mul_pow,Real.sq_sqrt (mul_nonneg hN.le hDp.le)]
    dsimp [A]
    field_simp
    ring
  rw [he]
  calc
    _ ≤ (A/(N*D))*H := mul_le_mul le_rfl
      ((div_le_iff₀ (sq_pos_of_pos ha)).2 hscale)
      (div_nonneg (mul_nonneg hm hS) (sq_nonneg a))
      (div_nonneg hA (mul_nonneg hN.le hDp.le))
    _ ≤ (A/(N*D₀))*H := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left hA (mul_pos hN hD₀) (mul_le_mul_of_nonneg_left hD hN.le)) hH
    _ = _ := by dsimp [A]; ring

 theorem integral_weighted_power_root {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) (hf : ∀ p, 0 ≤ f p) {l : ℕ} (hl : 0 < l) {m : ℝ} (hm : 0 ≤ m) :
    (∫ p, (m*f p)^l ∂μ)^((l:ℝ)⁻¹) = m*(∫ p, (f p)^l ∂μ)^((l:ℝ)⁻¹) := by
  simp only [mul_pow,integral_const_mul]
  rw [Real.mul_rpow (pow_nonneg hm _) (integral_nonneg fun p => pow_nonneg (hf p) _),
    Real.pow_rpow_inv_natCast hm hl.ne']

 theorem eventually_weighted_far_pair_moment (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Type) [MeasurableSpace P]
      (steps : List (GaussianStep (FeatureIndex n))) (a c D D₀ xs m H : ℝ),
      0 < a → 0 < D₀ → D₀ ≤ D → D ≤ B → 0 < xs → 0 ≤ m → 0 ≤ H →
      OrderedSteps c steps →
    ∀ (μ : Measure P) [IsProbabilityMeasure μ]
      (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (fork v w d e : ℕ),
      v ≤ w → w ≤ steps.length+1 → d ≤ e → e ≤ steps.length+1 →
      ((PhysicalProjectionClock n steps fork d e a D ∧
          m*(xs+physicalCutMass c steps w) ≤ H*a^2) ∨
       (PhysicalProjectionClock n steps fork v w a D ∧
          m*(xs+physicalCutMass c steps e) ≤ H*a^2)) →
    (∫ p, (m*physicalCutPairSquare n steps x fork v w d e p)^(k+1)
      ∂physicalPathLaw μ n steps x hx)^(((k+1:ℕ):ℝ)⁻¹) ≤
      4*(projectionLpConstant k)^2*(Real.log (n:ℝ))^4*
        (physicalRawRatio n (k+1) steps c xs μ x hx)^2*H/((n:ℝ)*D₀) := by
  filter_upwards [eventually_physical_clock_pair_moment k B,
    eventually_physical_clock_pair_observed_moment k B,eventually_ge_atTop 1] with n hn ho hnpos
  intro P _ steps a c D D₀ xs m H ha hD₀ hD hDB hxs hm hH hs μ _ x hx fork v w d e hvw hw hde he hc
  rw [integral_weighted_power_root _ _ (physicalCutPairSquare_nonneg n steps x fork v w d e)
    (Nat.succ_pos k) hm]
  have hnp : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hDp : 0 < D := hD₀.trans_le hD
  rcases hc with ⟨hc,hscale⟩ | ⟨hc,hscale⟩
  · exact (mul_le_mul_of_nonneg_left
      (hn P steps a c D xs ha hDp hDB hxs hs μ x hx fork v w d e hvw hw hc) hm).trans
      (projection_weight_scale_bound hnp ha hD₀ hD hm
        (add_nonneg hxs.le (physicalCutMass_mem steps hs w).1) hH hscale)
  · exact (mul_le_mul_of_nonneg_left
      (ho P steps a c D xs ha hDp hDB hxs hs μ x hx fork d e v w hde he hc) hm).trans
      (projection_weight_scale_bound hnp ha hD₀ hD hm
        (add_nonneg hxs.le (physicalCutMass_mem steps hs e).1) hH hscale)

end SKFluctuations

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 theorem integral_power_root_le_mass {A Ω : Type*} [MeasurableSpace A] [MeasurableSpace Ω]
    (ν : Measure A) (μ : Measure Ω) [IsFiniteMeasure ν] [IsFiniteMeasure μ]
    (f : A × Ω → ℝ) (hf : Measurable f) (h0 : ∀ z, 0 ≤ f z)
    {R : ℝ} (hR : ∀ z, f z ≤ R) {l : ℕ} (hl : 0 < l)
    {L : ℝ} (hL : 0 ≤ L)
    (hm : ∀ᵐ s ∂ν, (∫ p, f (s,p)^l ∂μ)^((l:ℝ)⁻¹) ≤ L) :
    (∫ p, (∫ s, f (s,p) ∂ν)^l ∂μ)^((l:ℝ)⁻¹) ≤ ν.real univ*L := by
  let m := ν.real univ
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  have hIp : Integrable (fun z => (f z)^l) (ν.prod μ) :=
    Integrable.of_bound (hf.pow_const l).aestronglyMeasurable (R^l)
      (Eventually.of_forall fun z => by
        rw [Real.norm_of_nonneg (pow_nonneg (h0 z) l)]
        exact pow_le_pow_left₀ (h0 z) (hR z) l)
  have hInt p : Integrable (fun s => f (s,p)) ν :=
    Integrable.of_bound (hf.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable R
      (Eventually.of_forall fun s => by rw [Real.norm_of_nonneg (h0 _)]; exact hR _)
  have hIntp p : Integrable (fun s => f (s,p)^l) ν :=
    Integrable.of_bound ((hf.comp (measurable_id.prodMk measurable_const)).pow_const l).aestronglyMeasurable
      (R^l) (Eventually.of_forall fun s => by
        rw [Real.norm_of_nonneg (pow_nonneg (h0 _) l)]
        exact pow_le_pow_left₀ (h0 _) (hR _) l)
  have hJ0 : 0 ≤ ∫ p, (∫ s, f (s,p) ∂ν)^l ∂μ :=
    integral_nonneg fun p => pow_nonneg (integral_nonneg fun s => h0 _) l
  have hsection : ∀ᵐ s ∂ν, (∫ p, f (s,p)^l ∂μ) ≤ L^l := by
    filter_upwards [hm] with s hs
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg (integral_nonneg fun p => pow_nonneg (h0 _) l) _) hs l
    rwa [Real.rpow_inv_natCast_pow (integral_nonneg fun p => pow_nonneg (h0 _) l) hl.ne'] at hh
  have hbound : (∫ p, (∫ s, f (s,p) ∂ν)^l ∂μ) ≤ (m*L)^l := by
    calc
      _ ≤ ∫ p, m^(l-1)*(∫ s, f (s,p)^l ∂ν) ∂μ := by
        apply integral_mono_of_nonneg
          (Eventually.of_forall fun p => pow_nonneg (integral_nonneg fun s => h0 _) l)
          (hIp.integral_prod_right.const_mul (m^(l-1)))
        exact Eventually.of_forall fun p => integral_pow_le_mass ν
          (Eventually.of_forall fun s => h0 _) (hInt p) hl (hIntp p)
      _ = m^(l-1)*(∫ s, ∫ p, f (s,p)^l ∂μ ∂ν) := by
        rw [integral_const_mul,← integral_integral_swap hIp]
      _ ≤ m^(l-1)*(m*L^l) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hm0 _)
        simpa only [integral_const,smul_eq_mul] using
          integral_mono_ae hIp.integral_prod_left (integrable_const (L^l)) hsection
      _ = (m*L)^l := by
        rw [mul_pow,← mul_assoc,← pow_succ,show l-1+1=l by omega]
  have hh := Real.rpow_le_rpow hJ0 hbound (inv_nonneg.2 (Nat.cast_nonneg l))
  simpa only [Real.pow_rpow_inv_natCast (mul_nonneg hm0 hL) hl.ne'] using hh

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 theorem physicalCutPairSquare_joint (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {c : ℝ} (hc : OrderedSteps c steps) {P A : Type} [MeasurableSpace P] [MeasurableSpace A]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
    {fork v w d e : A → ℕ} (hf : Measurable fork) (hv : Measurable v) (hw : Measurable w)
    (hd : Measurable d) (he : Measurable e) :
    Measurable (fun q : A × PhysicalPathState P n steps =>
      physicalCutPairSquare n steps x (fork q.1) (v q.1) (w q.1) (d q.1) (e q.1) q.2) := by
  have hm : Measurable (fun q : (ℕ × ℕ × ℕ × ℕ × ℕ) × PhysicalPathState P n steps =>
      physicalCutPairSquare n steps x q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2.1 q.1.2.2.2.2 q.2) :=
    measurable_from_prod_countable_right fun k =>
      physicalCutPairSquare_measurable n steps hc x hx k.1 k.2.1 k.2.2.1 k.2.2.2.1 k.2.2.2.2
  exact hm.comp (((hf.prodMk (hv.prodMk (hw.prodMk (hd.prodMk he)))).comp measurable_fst).prodMk measurable_snd)

 def HasFarPairClock (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    (c xs D₀ B H m : ℝ) (fork v w d e : ℕ) : Prop :=
  v ≤ w ∧ w ≤ steps.length+1 ∧ d ≤ e ∧ e ≤ steps.length+1 ∧
    ∃ a D : ℝ, 0 < a ∧ D₀ ≤ D ∧ D ≤ B ∧
      ((PhysicalProjectionClock n steps fork d e a D ∧ m*(xs+physicalCutMass c steps w) ≤ H*a^2) ∨
       (PhysicalProjectionClock n steps fork v w a D ∧ m*(xs+physicalCutMass c steps e) ≤ H*a^2))

 def physicalCutPairRadiusIntegral (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {P : Type} (x : P → FeatureIndex n → ℝ) (m : ℝ → ℝ)
    (fork v w d e : ℝ → ℕ) (r₀ r₁ : ℝ) (p : PhysicalPathState P n steps) : ℝ :=
  ∫ s in r₀..r₁, m s*physicalCutPairSquare n steps x (fork s) (v s) (w s) (d s) (e s) p

 theorem eventually_physical_far_radius_integral (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Type) [MeasurableSpace P]
      (steps : List (GaussianStep (FeatureIndex n))) (c D₀ xs H r₀ r₁ : ℝ),
      0 < D₀ → 0 < xs → 0 ≤ H → r₀ ≤ r₁ → OrderedSteps c steps →
    ∀ (μ : Measure P) [IsProbabilityMeasure μ]
      (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
      (m : ℝ → ℝ) (fork v w d e : ℝ → ℕ),
      Measurable m → Measurable fork → Measurable v → Measurable w → Measurable d → Measurable e →
      (∀ s, m s ∈ Icc (0:ℝ) 1) →
      (∀ s ∈ Ioc r₀ r₁, HasFarPairClock n steps c xs D₀ B H (m s) (fork s) (v s) (w s) (d s) (e s)) →
    (∫ p, (physicalCutPairRadiusIntegral n steps x m fork v w d e r₀ r₁ p)^(k+1)
      ∂physicalPathLaw μ n steps x hx)^(((k+1:ℕ):ℝ)⁻¹) ≤
      (r₁-r₀)*(4*(projectionLpConstant k)^2*(Real.log (n:ℝ))^4*
        (physicalRawRatio n (k+1) steps c xs μ x hx)^2*H/((n:ℝ)*D₀)) := by
  filter_upwards [eventually_weighted_far_pair_moment k B] with n hn
  intro P _ steps c D₀ xs H r₀ r₁ hD₀ hxs hH hr hs μ _ x hx m fork v w d e hm hf hv hw hd he hm01 hclock
  let ν := physicalPathLaw μ n steps x hx
  have := physicalPathLaw_finite μ n steps hs x hx
  let F : ℝ × PhysicalPathState P n steps → ℝ := fun z =>
    m z.1*physicalCutPairSquare n steps x (fork z.1) (v z.1) (w z.1) (d z.1) (e z.1) z.2
  have hF : Measurable F := (hm.comp measurable_fst).mul
    (physicalCutPairSquare_joint n steps hs x hx hf hv hw hd he)
  have hF0 : ∀ z, 0 ≤ F z := fun z => mul_nonneg (hm01 z.1).1
    (physicalCutPairSquare_nonneg n steps x _ _ _ _ _ z.2)
  have hFB : ∀ z, F z ≤ 16 := fun z => by
    apply (mul_le_mul_of_nonneg_right (hm01 z.1).2
      (physicalCutPairSquare_nonneg n steps x _ _ _ _ _ z.2)).trans
    simpa only [one_mul] using physicalCutPairSquare_le n steps hs x hx
      (fork z.1) (v z.1) (w z.1) (d z.1) (e z.1) z.2
  let L := 4*(projectionLpConstant k)^2*(Real.log (n:ℝ))^4*
    (physicalRawRatio n (k+1) steps c xs μ x hx)^2*H/((n:ℝ)*D₀)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hsection : ∀ᵐ s ∂volume.restrict (Ioc r₀ r₁),
      (∫ p, F (s,p)^(k+1) ∂ν)^(((k+1:ℕ):ℝ)⁻¹) ≤ L := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hsr
    rcases hclock s hsr with ⟨hvw,hw',hde,he',a,D,ha,hD,hDB,hp⟩
    exact hn P steps a c D D₀ xs (m s) H ha hD₀ hD hDB hxs (hm01 s).1 hH hs μ x hx
      (fork s) (v s) (w s) (d s) (e s) hvw hw' hde he' hp
  have hh := integral_power_root_le_mass (volume.restrict (Ioc r₀ r₁)) ν F hF hF0 hFB
    (Nat.succ_pos k) hL hsection
  have hmass : (volume.restrict (Ioc r₀ r₁)).real univ = r₁-r₀ := by
    simp only [Measure.real,Measure.restrict_apply_univ,Real.volume_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hr)]
  rw [hmass] at hh
  simpa only [physicalCutPairRadiusIntegral,intervalIntegral.integral_of_le hr] using hh

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 theorem eventually_physical_far_mass_integral (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (P A : Type) [MeasurableSpace P] [MeasurableSpace A]
      (steps : List (GaussianStep (FeatureIndex n))) (c D₀ xs H : ℝ),
      0 < D₀ → 0 < xs → 0 ≤ H → OrderedSteps c steps →
    ∀ (μ : Measure P) [IsProbabilityMeasure μ] (ζ : Measure A) [IsFiniteMeasure ζ]
      (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
      (m : A → ℝ) (fork v w d e : A → ℕ),
      Measurable m → Measurable fork → Measurable v → Measurable w → Measurable d → Measurable e →
      (∀ s, m s ∈ Icc (0:ℝ) 1) →
      (∀ᵐ s ∂ζ, HasFarPairClock n steps c xs D₀ B H (m s) (fork s) (v s) (w s) (d s) (e s)) →
    (∫ p, (∫ s, m s*physicalCutPairSquare n steps x (fork s) (v s) (w s) (d s) (e s) p ∂ζ)^(k+1)
      ∂physicalPathLaw μ n steps x hx)^(((k+1:ℕ):ℝ)⁻¹) ≤
      ζ.real univ*(4*(projectionLpConstant k)^2*(Real.log (n:ℝ))^4*
        (physicalRawRatio n (k+1) steps c xs μ x hx)^2*H/((n:ℝ)*D₀)) := by
  filter_upwards [eventually_weighted_far_pair_moment k B] with n hn
  intro P A _ _ steps c D₀ xs H hD₀ hxs hH hs μ _ ζ _ x hx m fork v w d e hm hf hv hw hd he hm01 hclock
  let ν := physicalPathLaw μ n steps x hx
  have := physicalPathLaw_finite μ n steps hs x hx
  let F : A × PhysicalPathState P n steps → ℝ := fun z =>
    m z.1*physicalCutPairSquare n steps x (fork z.1) (v z.1) (w z.1) (d z.1) (e z.1) z.2
  have hF : Measurable F := (hm.comp measurable_fst).mul
    (physicalCutPairSquare_joint n steps hs x hx hf hv hw hd he)
  have hF0 : ∀ z, 0 ≤ F z := fun z => mul_nonneg (hm01 z.1).1
    (physicalCutPairSquare_nonneg n steps x _ _ _ _ _ z.2)
  have hFB : ∀ z, F z ≤ 16 := fun z => by
    apply (mul_le_mul_of_nonneg_right (hm01 z.1).2
      (physicalCutPairSquare_nonneg n steps x _ _ _ _ _ z.2)).trans
    simpa only [one_mul] using physicalCutPairSquare_le n steps hs x hx
      (fork z.1) (v z.1) (w z.1) (d z.1) (e z.1) z.2
  let L := 4*(projectionLpConstant k)^2*(Real.log (n:ℝ))^4*
    (physicalRawRatio n (k+1) steps c xs μ x hx)^2*H/((n:ℝ)*D₀)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hsection : ∀ᵐ s ∂ζ,
      (∫ p, F (s,p)^(k+1) ∂ν)^(((k+1:ℕ):ℝ)⁻¹) ≤ L := by
    filter_upwards [hclock] with s hsc
    rcases hsc with ⟨hvw,hw',hde,he',a,D,ha,hD,hDB,hp⟩
    exact hn P steps a c D D₀ xs (m s) H ha hD₀ hD hDB hxs (hm01 s).1 hH hs μ x hx
      (fork s) (v s) (w s) (d s) (e s) hvw hw' hde he' hp
  exact integral_power_root_le_mass ζ ν F hF hF0 hFB
    (Nat.succ_pos k) hL hsection

end SKFluctuations

end

end OAI
