import Mathlib
import OAI.Probability.SKFluctuations.HasDerivAtDynamicVarianceContinuation

namespace OAI

/-! Rooted Variance Pressure. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

 

noncomputable def rootedVariancePressure (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (front tail : List (GaussianStep ι)) (m : ℝ) (q₀ : ι → ℝ≥0) (q x : ι → ℝ) : ℝ :=
  zeroContinuation (Measure.pi fun i => gaussianReal 0 (q₀ i))
    (gaussianHierarchy w φ (front ++ (m,fun i => Real.toNNReal (q i))::tail)) x

theorem rootedVariancePressure_continuous {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (front tail : List (GaussianStep ι)) {m : ℝ} (hm : 0 < m)
    (ha : OrderedSteps m tail) (hf : ∀ st ∈ front, 0 < st.1) (q₀ : ι → ℝ≥0)
    {q : ℝ → (ι → ℝ)} (hq : Continuous q) (x : ι → ℝ) :
    Continuous (fun s => rootedVariancePressure w φ front tail m q₀ (q s) x) := by
  obtain ⟨C,hF⟩ := (gaussianHierarchy_regular hw φ tail ha 0).1
  obtain ⟨K,hK⟩ := parametric_continuous_variance hF (BddSmooth.const 0 (0:ℝ)) hm hq
  have hc := (((hK.prefix front hf).root q₀).potential x)
  have he (s : ℝ) : prefixContinuation front (varianceContinuation m (gaussianHierarchy w φ tail) (q s)) =
      gaussianHierarchy w φ (front ++ (m,fun i => Real.toNNReal (q s i))::tail) :=
    prefixContinuation_hierarchy w φ front ((m,fun i => Real.toNNReal (q s i))::tail)
  simp_rw [he] at hc
  exact continuousOn_univ.mp hc

variable {n : ℕ}

 

theorem rootedVariancePressure_chord_pos {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (q d : Fin (n+1) → ℝ) {Q B : ℝ}
    (hQ : ∀ σ, ∑ i, d i*(φ σ (Pi.single i 1))^2 = Q)
    (hB : ∀ σ τ, -B ≤ ∑ i, d i*φ σ (Pi.single i 1)*φ τ (Pi.single i 1))
    (front tail : List (GaussianStep (Fin (n+1)))) {m : ℝ} (hm : 0 < m)
    (ha : OrderedSteps m tail) (hf : ∀ st ∈ front, 0 < st.1)
    (q₀ : Fin (n+1) → ℝ≥0) (hq : ∀ t ∈ Ioo (0:ℝ) 1, ∀ i, 0 < q i+t*d i) (x : Fin (n+1) → ℝ) :
    rootedVariancePressure w φ front tail m q₀ (q+d) x ≤
      rootedVariancePressure w φ front tail m q₀ q x+Q/2+(1-m)*B/2 := by
  have hc := (rootedVariancePressure_continuous hw φ front tail hm ha hf q₀
    (q := fun t i => q i+t*d i) (by fun_prop) x).sub
      ((continuous_id.const_mul Q).div_const 2)
  have hd (t) (ht : t ∈ Ioo (0:ℝ) 1) :=
    rootedHierarchy_corrected_signed_variance hw φ q d hQ front tail hm ha hf q₀ hq ht x
  have hh := (convex_Icc (0:ℝ) 1).image_sub_le_mul_sub_of_deriv_le hc.continuousOn
    (fun t ht => (hd t (by simpa only [interior_Icc] using ht)).differentiableAt.differentiableWithinAt)
    (fun t ht => rootedHierarchy_signed_derivative_bound hw φ q d hQ hB front tail hm ha hf q₀
      hq (by simpa only [interior_Icc] using ht) x)
    0 (by simp) 1 (by simp) (by norm_num)
  change (_-Q*1/2)-(_-Q*0/2) ≤ _ at hh
  simp only [mul_one,mul_zero,zero_div,sub_zero,one_mul,zero_mul,add_zero] at hh
  change rootedVariancePressure w φ front tail m q₀ (q+d) x-Q/2-
    rootedVariancePressure w φ front tail m q₀ q x ≤ (1-m)*B/2 at hh
  linarith

 

theorem rootedVariancePressure_chord {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (q r : Fin (n+1) → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hr : ∀ i, 0 ≤ r i) {Q B : ℝ}
    (hQ : ∀ σ, ∑ i, (r i-q i)*(φ σ (Pi.single i 1))^2 = Q)
    (hB : ∀ σ τ, -B ≤ ∑ i, (r i-q i)*φ σ (Pi.single i 1)*φ τ (Pi.single i 1))
    (front tail : List (GaussianStep (Fin (n+1)))) {m : ℝ} (hm : 0 < m)
    (ha : OrderedSteps m tail) (hf : ∀ st ∈ front, 0 < st.1)
    (q₀ : Fin (n+1) → ℝ≥0) (x : Fin (n+1) → ℝ) :
    rootedVariancePressure w φ front tail m q₀ r x ≤
      rootedVariancePressure w φ front tail m q₀ q x+Q/2+(1-m)*B/2 := by
  have hp (e : ℝ) (he : 0 < e) :
      rootedVariancePressure w φ front tail m q₀ (fun i => r i+e) x ≤
        rootedVariancePressure w φ front tail m q₀ (fun i => q i+e) x+Q/2+(1-m)*B/2 := by
    have hh := rootedVariancePressure_chord_pos hw φ (fun i => q i+e) (fun i => r i-q i)
      hQ hB front tail hm ha hf q₀ (fun t ht i => by
        have h1 := mul_nonneg (sub_nonneg.mpr ht.2.le) (hq i)
        have h2 := mul_nonneg ht.1.le (hr i)
        nlinarith) x
    have heq : (fun i => q i+e)+(fun i => r i-q i) = (fun i => r i+e) := by ext i; dsimp; ring
    rw [heq] at hh
    exact hh
  have hcq := rootedVariancePressure_continuous hw φ front tail hm ha hf q₀
    (q := fun e i => q i+e) (by fun_prop) x
  have hcr := rootedVariancePressure_continuous hw φ front tail hm ha hf q₀
    (q := fun e i => r i+e) (by fun_prop) x
  have hh := le_of_tendsto_of_tendsto
    (hcr.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)) (a := 0)))
    (((hcq.add_const (Q/2)).add_const ((1-m)*B/2)).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (0:ℝ)) (a := 0)))
    (show ∀ᶠ e in 𝓝[>] (0:ℝ), rootedVariancePressure w φ front tail m q₀ (fun i => r i+e) x ≤
      rootedVariancePressure w φ front tail m q₀ (fun i => q i+e) x+Q/2+(1-m)*B/2 from
      Filter.Eventually.mono self_mem_nhdsWithin (fun e he => hp e he))
  simpa only [add_zero] using hh

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι κ S : Type*} [Fintype ι] [Fintype κ] [Fintype S]

def reindexSteps (e : κ ≃ ι) (steps : List (GaussianStep ι)) : List (GaussianStep κ) :=
  steps.map fun st => (st.1,fun i => st.2 (e i))

omit [Fintype ι] [Fintype κ] in
theorem reindexSteps_ordered (e : κ ≃ ι) {steps : List (GaussianStep ι)} {m : ℝ}
    (hm : OrderedSteps m steps) : OrderedSteps m (reindexSteps e steps) := by
  induction steps generalizing m with
  | nil => exact hm
  | cons st steps ih => exact ⟨hm.1,hm.2.1,hm.2.2.1,ih hm.2.2.2⟩

omit [Fintype ι] [Fintype κ] in
theorem reindexSteps_positive (e : κ ≃ ι) {steps : List (GaussianStep ι)}
    (hm : ∀ st ∈ steps, 0 < st.1) : ∀ st ∈ reindexSteps e steps, 0 < st.1 := by
  intro st hs
  change st ∈ steps.map (fun s => (s.1,fun i => s.2 (e i))) at hs
  simp only [List.mem_map] at hs
  obtain ⟨s,hs,hst⟩ := hs
  subst st
  exact hm s hs

theorem gaussianHierarchy_reindex_steps (e : κ ≃ ι) (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι)) :
    gaussianHierarchy w (reindexFeature e φ) (reindexSteps e steps) =
      fun x => gaussianHierarchy w φ steps (coordinateEquiv e x) := by
  induction steps with
  | nil => rfl
  | cons st steps ih =>
    funext x
    change shiftedContinuation _ _ (gaussianHierarchy w (reindexFeature e φ) (reindexSteps e steps)) x = _
    rw [ih]
    exact shiftedContinuation_reindex e st.2 st.1 _ x

theorem zeroContinuation_reindex (e : κ ≃ ι) (q : ι → ℝ≥0) (F : (ι → ℝ) → ℝ) (x : κ → ℝ) :
    zeroContinuation (Measure.pi fun i => gaussianReal 0 (q (e i))) (fun y => F (coordinateEquiv e y)) x =
      zeroContinuation (Measure.pi fun i => gaussianReal 0 (q i)) F (coordinateEquiv e x) := by
  have h := (coordinateEquiv_measPres e q).integral_comp
    (coordinateEquiv e).toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (fun z => F (coordinateEquiv e x+z))
  simpa only [zeroContinuation,← map_add] using h

theorem rootedVariancePressure_reindex (e : κ ≃ ι) (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (front tail : List (GaussianStep ι)) (m : ℝ)
    (q₀ : ι → ℝ≥0) (q : ι → ℝ) (x : κ → ℝ) :
    rootedVariancePressure w (reindexFeature e φ) (reindexSteps e front) (reindexSteps e tail) m
      (fun i => q₀ (e i)) (fun i => q (e i)) x =
    rootedVariancePressure w φ front tail m q₀ q (coordinateEquiv e x) := by
  unfold rootedVariancePressure
  have he : reindexSteps e front ++ (m,fun i => Real.toNNReal (q (e i)))::reindexSteps e tail =
      reindexSteps e (front ++ (m,fun i => Real.toNNReal (q i))::tail) := by
    simp only [reindexSteps,List.map_append,List.map_cons]
  rw [he,gaussianHierarchy_reindex_steps]
  exact zeroContinuation_reindex e q₀ _ x

variable [Nonempty S] [Nonempty ι] [DecidableEq ι]

 
theorem rootedVariancePressure_chord_finite {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (q r : ι → ℝ) (hq : ∀ i, 0 ≤ q i) (hr : ∀ i, 0 ≤ r i)
    {Q B : ℝ} (hQ : ∀ σ, ∑ i, (r i-q i)*(φ σ (Pi.single i 1))^2 = Q)
    (hB : ∀ σ τ, -B ≤ ∑ i, (r i-q i)*φ σ (Pi.single i 1)*φ τ (Pi.single i 1))
    (front tail : List (GaussianStep ι)) {m : ℝ} (hm : 0 < m) (ha : OrderedSteps m tail)
    (hf : ∀ st ∈ front, 0 < st.1) (q₀ : ι → ℝ≥0) (x : ι → ℝ) :
    rootedVariancePressure w φ front tail m q₀ r x ≤
      rootedVariancePressure w φ front tail m q₀ q x+Q/2+(1-m)*B/2 := by
  classical
  let d := Fintype.card ι-1
  have hd : d+1 = Fintype.card ι := Nat.sub_add_cancel (Fintype.card_pos_iff.mpr ‹Nonempty ι›)
  let e : Fin (d+1) ≃ ι := (finCongr hd).trans (Fintype.equivFin ι).symm
  have hp (σ : S) (i : Fin (d+1)) : reindexFeature e φ σ (Pi.single i 1) = φ σ (Pi.single (e i) 1) := by
    change φ σ (coordinateEquiv e (Pi.single i 1)) = _
    rw [coordinateEquiv_single]
  have hQ' (σ) : ∑ i, (r (e i)-q (e i))*(reindexFeature e φ σ (Pi.single i 1))^2 = Q := by
    simp_rw [hp]
    rw [e.sum_comp (fun i => (r i-q i)*(φ σ (Pi.single i 1))^2)]
    exact hQ σ
  have hB' (σ τ) : -B ≤ ∑ i, (r (e i)-q (e i))*reindexFeature e φ σ (Pi.single i 1)*
      reindexFeature e φ τ (Pi.single i 1) := by
    simp_rw [hp]
    rw [e.sum_comp (fun i => (r i-q i)*φ σ (Pi.single i 1)*φ τ (Pi.single i 1))]
    exact hB σ τ
  have hh := rootedVariancePressure_chord hw (reindexFeature e φ) (fun i => q (e i)) (fun i => r (e i))
    (fun i => hq (e i)) (fun i => hr (e i)) hQ' hB' (reindexSteps e front) (reindexSteps e tail)
    hm (reindexSteps_ordered e ha) (reindexSteps_positive e hf) (fun i => q₀ (e i)) ((coordinateEquiv e).symm x)
  rw [rootedVariancePressure_reindex,rootedVariancePressure_reindex,ContinuousLinearEquiv.apply_symm_apply] at hh
  exact hh

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι κ S : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [Fintype S] [Nonempty S]

def reindexSignedSteps (e : κ ≃ ι) (ss : List (SignedStep ι)) : List (SignedStep κ) :=
  ss.map fun st => (st.1,(fun i => st.2.1 (e i)),(fun i => st.2.2 (e i)))

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
@[simp] theorem reindexSignedSteps_nil (e : κ ≃ ι) :
    reindexSignedSteps e ([] : List (SignedStep ι)) = [] := rfl

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
@[simp] theorem reindexSignedSteps_cons (e : κ ≃ ι) (st : SignedStep ι) (ss : List (SignedStep ι)) :
    reindexSignedSteps e (st::ss) =
      (st.1,(fun i => st.2.1 (e i)),(fun i => st.2.2 (e i)))::reindexSignedSteps e ss := rfl

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
@[simp] theorem reindexSignedSteps_inverse (e : κ ≃ ι) (ss : List (SignedStep ι)) :
    reindexSignedSteps e.symm (reindexSignedSteps e ss) = ss := by
  simp [reindexSignedSteps,List.map_map,Function.comp_def]

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem affineSteps_reindex (e : κ ≃ ι) (ss : List (SignedStep ι)) (t : ℝ) :
    affineSteps (reindexSignedSteps e ss) t = reindexSteps e (affineSteps ss t) := by
  simp only [affineSteps,affineCovariances,covarianceSteps,reindexSignedSteps,reindexSteps,
    List.map_map,Function.comp_def]

omit [Fintype S] [Nonempty S] in
theorem featureKernel_reindex (e : κ ≃ ι) (φ : S → (ι → ℝ) →L[ℝ] ℝ) (d : ι → ℝ) :
    featureKernel (reindexFeature e φ) (fun i => d (e i)) = featureKernel φ d := by
  funext σ τ
  unfold featureKernel
  have hp (σ : S) (i : κ) : reindexFeature e φ σ (Pi.single i 1) =
      φ σ (Pi.single (e i) 1) := by
    change φ σ (coordinateEquiv e (Pi.single i 1)) = _
    rw [coordinateEquiv_single]
  simp_rw [hp]
  exact e.sum_comp (fun i => d i*φ σ (Pi.single i 1)*φ τ (Pi.single i 1))

omit [Fintype S] [Nonempty S] in
theorem PathKernelBound.reindex {e : κ ≃ ι} {φ : S → (ι → ℝ) →L[ℝ] ℝ}
    {B : List (SignedStep ι) → ℝ} {K : S → S → ℝ} {ss : List (SignedStep ι)}
    (hB : PathKernelBound φ B K ss) :
    PathKernelBound (reindexFeature e φ) (fun tail => B (reindexSignedSteps e.symm tail))
      K (reindexSignedSteps e ss) := by
  induction ss generalizing K with
  | nil => exact hB
  | cons st ss ih =>
    constructor
    · change ∀ σ τ, -B (reindexSignedSteps e.symm (reindexSignedSteps e (st::ss))) ≤ K σ τ
      simpa only [reindexSignedSteps_inverse] using hB.1
    · change PathKernelBound (reindexFeature e φ) (fun tail => B (reindexSignedSteps e.symm tail))
        (fun σ τ => K σ τ+featureKernel (reindexFeature e φ) (fun i => st.2.2 (e i)) σ τ)
        (reindexSignedSteps e ss)
      rw [featureKernel_reindex]
      exact ih hB.2

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem pathKernelCost_reindex (e : κ ≃ ι) (B : List (SignedStep ι) → ℝ)
    (ss : List (SignedStep ι)) (a : ℝ) :
    pathKernelCost (fun tail => B (reindexSignedSteps e.symm tail)) a (reindexSignedSteps e ss) =
      pathKernelCost B a ss := by
  induction ss generalizing a with
  | nil => rfl
  | cons st ss ih =>
    change (st.1-a)*B (reindexSignedSteps e.symm (reindexSignedSteps e (st::ss)))+
      pathKernelCost (fun tail => B (reindexSignedSteps e.symm tail)) st.1 (reindexSignedSteps e ss) = _
    rw [reindexSignedSteps_inverse,ih]
    rfl

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype S] [Nonempty S]

 

theorem rootedHierarchy_affine_chord_finite {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (T : (ι → ℝ) → ℝ)
    (ss : List (SignedStep ι)) (q d : ι → ℝ)
    (hQ : ∀ st ∈ ss, ∀ σ, ∑ i, st.2.2 i*(φ σ (Pi.single i 1))^2 = T st.2.2)
    (hD : ∀ σ, ∑ i, d i*(φ σ (Pi.single i 1))^2 = T d)
    (B : List (SignedStep ι) → ℝ)
    (ha : OrderedSteps 0 (affineSteps ss 0)) (hB : PathKernelBound φ B (featureKernel φ d) ss)
    (hq : ∀ st ∈ ss, ∀ i, 0 ≤ st.2.1 i)
    (hr : ∀ st ∈ ss, ∀ i, 0 ≤ st.2.1 i+st.2.2 i)
    (hq₀ : ∀ i, 0 ≤ q i) (hr₀ : ∀ i, 0 ≤ q i+d i) (x : ι → ℝ) :
    zeroContinuation (Measure.pi fun i => gaussianReal 0 (Real.toNNReal (q i+d i)))
        (gaussianHierarchy w φ (affineSteps ss 1)) x-
      zeroContinuation (Measure.pi fun i => gaussianReal 0 (Real.toNNReal (q i)))
        (gaussianHierarchy w φ (affineSteps ss 0)) x-
      (T d+(ss.map fun st => T st.2.2).sum)/2 ≤ pathKernelCost B 0 ss/2 := by
  classical
  let k := Fintype.card ι-1
  have hk : k+1 = Fintype.card ι := Nat.sub_add_cancel (Fintype.card_pos_iff.mpr ‹Nonempty ι›)
  let e : Fin (k+1) ≃ ι := (finCongr hk).trans (Fintype.equivFin ι).symm
  let T' : (Fin (k+1) → ℝ) → ℝ := fun v => T (fun i => v (e.symm i))
  have hp (σ : S) (i : Fin (k+1)) : reindexFeature e φ σ (Pi.single i 1) =
      φ σ (Pi.single (e i) 1) := by
    change φ σ (coordinateEquiv e (Pi.single i 1)) = _
    rw [coordinateEquiv_single]
  have hQ' : ∀ st ∈ reindexSignedSteps e ss, ∀ σ,
      ∑ i, st.2.2 i*(reindexFeature e φ σ (Pi.single i 1))^2 = T' st.2.2 := by
    intro st hs σ
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hs
    dsimp only
    simp_rw [hp]
    rw [e.sum_comp (fun i => z.2.2 i*(φ σ (Pi.single i 1))^2)]
    simpa only [T',e.apply_symm_apply] using hQ z hz σ
  have hD' (σ : S) : ∑ i, d (e i)*(reindexFeature e φ σ (Pi.single i 1))^2 =
      T' (fun i => d (e i)) := by
    simp_rw [hp]
    rw [e.sum_comp (fun i => d i*(φ σ (Pi.single i 1))^2)]
    simpa only [T',e.apply_symm_apply] using hD σ
  have ha' : OrderedSteps 0 (affineSteps (reindexSignedSteps e ss) 0) := by
    rw [affineSteps_reindex]
    exact reindexSteps_ordered e ha
  have hB' : PathKernelBound (reindexFeature e φ)
      (fun tail => B (reindexSignedSteps e.symm tail))
      (featureKernel (reindexFeature e φ) (fun i => d (e i))) (reindexSignedSteps e ss) := by
    rw [featureKernel_reindex]
    exact hB.reindex
  have hq' : ∀ st ∈ reindexSignedSteps e ss, ∀ i, 0 ≤ st.2.1 i := by
    intro st hs i
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hs
    exact hq z hz (e i)
  have hr' : ∀ st ∈ reindexSignedSteps e ss, ∀ i, 0 ≤ st.2.1 i+st.2.2 i := by
    intro st hs i
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hs
    exact hr z hz (e i)
  have hh := rootedHierarchy_affine_chord hw (reindexFeature e φ) T' (reindexSignedSteps e ss)
    (fun i => q (e i)) (fun i => d (e i)) hQ' hD' (fun tail => B (reindexSignedSteps e.symm tail))
    ha' hB' hq' hr' (fun i => hq₀ (e i)) (fun i => hr₀ (e i)) ((coordinateEquiv e).symm x)
  have hsum : ((reindexSignedSteps e ss).map fun st => T' st.2.2).sum =
      (ss.map fun st => T st.2.2).sum := by
    simp only [reindexSignedSteps,List.map_map,Function.comp_def,T',e.apply_symm_apply]
  rw [hsum,pathKernelCost_reindex] at hh
  simp only [affineSteps_reindex,gaussianHierarchy_reindex_steps] at hh
  rw [zeroContinuation_reindex e (fun i => Real.toNNReal (q i+d i))
      (gaussianHierarchy w φ (affineSteps ss 1)) ((coordinateEquiv e).symm x),
    zeroContinuation_reindex e (fun i => Real.toNNReal (q i))
      (gaussianHierarchy w φ (affineSteps ss 0)) ((coordinateEquiv e).symm x),
    ContinuousLinearEquiv.apply_symm_apply] at hh
  simpa only [T',e.apply_symm_apply] using hh

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι : Type*}

 

def signedClockSteps : List PositiveMass → (ℕ → ι → ℝ) → (ℕ → ι → ℝ) → List (SignedStep ι)
  | [],_,_ => []
  | a::as,q,r => (a.val,q 1-q 0,(r 1-q 1)-(r 0-q 0))::
      signedClockSteps as (fun j => q (j+1)) (fun j => r (j+1))

@[simp] theorem signedClockSteps_length (as : List PositiveMass) (q r : ℕ → ι → ℝ) :
    (signedClockSteps as q r).length = as.length := by
  induction as generalizing q r with
  | nil => rfl
  | cons a as ih => simpa only [signedClockSteps,List.length_cons] using congrArg Nat.succ (ih _ _)

@[simp] theorem signedClockSteps_zero (as : List PositiveMass) (q r : ℕ → ι → ℝ) :
    affineSteps (signedClockSteps as q r) 0 =
      diagonalBoundarySteps as (q 0) (fun j => q (j+1)) := by
  induction as generalizing q r with
  | nil => rfl
  | cons a as ih =>
    simp only [signedClockSteps,affineSteps_cons,Pi.sub_apply,zero_mul,add_zero,ih,
      diagonalBoundarySteps]

@[simp] theorem signedClockSteps_one (as : List PositiveMass) (q r : ℕ → ι → ℝ) :
    affineSteps (signedClockSteps as q r) 1 =
      diagonalBoundarySteps as (r 0) (fun j => r (j+1)) := by
  induction as generalizing q r with
  | nil => rfl
  | cons a as ih =>
    simp only [signedClockSteps,affineSteps_cons,Pi.sub_apply,one_mul,ih,diagonalBoundarySteps]
    congr 2
    funext i
    congr 1
    ring

theorem signedClockSteps_admissible (as : List PositiveMass) (q r : ℕ → ι → ℝ)
    (hq : ∀ i, Monotone (fun j => q j i)) (hr : ∀ i, Monotone (fun j => r j i)) :
    ∀ st ∈ signedClockSteps as q r, ∀ i, 0 ≤ st.2.1 i ∧ 0 ≤ st.2.1 i+st.2.2 i := by
  induction as generalizing q r with
  | nil => simp only [signedClockSteps,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | cons a as ih =>
    intro st hs i
    rcases List.mem_cons.mp hs with rfl|hs
    · have hqi := hq i (by norm_num : (0:ℕ) ≤ 1)
      have hri := hr i (by norm_num : (0:ℕ) ≤ 1)
      dsimp only [Pi.sub_apply]
      constructor <;> linarith
    · exact ih _ _ (fun i _ _ hj => hq i (Nat.add_le_add_right hj 1))
        (fun i _ _ hj => hr i (Nat.add_le_add_right hj 1)) st hs i

 

theorem signedClockSteps_trace (T : (ι → ℝ) →ₗ[ℝ] ℝ) (as : List PositiveMass) (q r : ℕ → ι → ℝ) :
    T (r 0-q 0)+((signedClockSteps as q r).map fun st => T st.2.2).sum =
      T (r as.length-q as.length) := by
  induction as generalizing q r with
  | nil => simp only [signedClockSteps,List.map_nil,List.sum_nil,add_zero,List.length_nil]
  | cons a as ih =>
    have hh := ih (fun j => q (j+1)) (fun j => r (j+1))
    simp only [zero_add] at hh
    simp only [signedClockSteps,List.map_cons,List.sum_cons,List.length_cons,map_sub]
    simp only [map_sub] at hh
    linarith

 

def massStepSum : List PositiveMass → ℝ → (ℕ → ℝ) → ℝ
  | [],a,C => (1-a)*C 0
  | b::bs,a,C => (b.val-a)*C 0+massStepSum bs b.val (fun j => C (j+1))

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [DecidableEq ι]

 
theorem featureKernel_add_difference (φ : S → (ι → ℝ) →L[ℝ] ℝ) (v u : ι → ℝ) :
    (fun σ τ => featureKernel φ v σ τ+featureKernel φ (u-v) σ τ) = featureKernel φ u := by
  funext σ τ
  simp only [featureKernel,Pi.sub_apply,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem signedClockSteps_kernelBound (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (as : List PositiveMass) (q r : ℕ → ι → ℝ) (C : ℕ → ℝ)
    (hC : ∀ j, j ≤ as.length → ∀ σ τ, -C j ≤ featureKernel φ (r j-q j) σ τ) :
    PathKernelBound φ (fun tail => C (as.length-tail.length))
      (featureKernel φ (r 0-q 0)) (signedClockSteps as q r) := by
  induction as generalizing q r C with
  | nil => exact hC 0 le_rfl
  | cons a as ih =>
    constructor
    · simpa only [signedClockSteps_length,List.length_cons,Nat.sub_self] using hC 0 (Nat.zero_le _)
    · rw [featureKernel_add_difference]
      have hh := ih (fun j => q (j+1)) (fun j => r (j+1)) (fun j => C (j+1))
        (fun j hj => hC (j+1) (by simpa only [List.length_cons] using Nat.succ_le_succ hj))
      simp only [zero_add] at hh
      apply hh.congr_bounds
      intro tail ht
      rw [signedClockSteps_length] at ht
      congr 1
      simp only [List.length_cons]
      omega

omit [Fintype ι] [DecidableEq ι] in
theorem signedClockSteps_cost (as : List PositiveMass) (q r : ℕ → ι → ℝ) (C : ℕ → ℝ) (a : ℝ) :
    pathKernelCost (fun tail => C (as.length-tail.length)) a (signedClockSteps as q r) =
      massStepSum as a C := by
  induction as generalizing q r C a with
  | nil => rfl
  | cons b bs ih =>
    change (b.val-a)*C ((b::bs).length-(signedClockSteps (b::bs) q r).length)+
      pathKernelCost (fun tail => C ((b::bs).length-tail.length)) b.val
        (signedClockSteps bs (fun j => q (j+1)) (fun j => r (j+1))) = _
    rw [signedClockSteps_length,Nat.sub_self]
    change _ = (b.val-a)*C 0+massStepSum bs b.val (fun j => C (j+1))
    congr 1
    calc
      _ = pathKernelCost (fun tail => C (bs.length-tail.length+1)) b.val
          (signedClockSteps bs (fun j => q (j+1)) (fun j => r (j+1))) := by
        apply pathKernelCost_congr
        intro tail ht
        rw [signedClockSteps_length] at ht
        congr 1
        simp only [List.length_cons]
        omega
      _ = _ := ih _ _ (fun j => C (j+1)) b.val

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype S] [Nonempty S]

 

theorem disorderPressure_chord {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (C : ι → ℝ)
    (hself : ∀ σ i, (φ σ (Pi.single i 1))^2 = C i)
    (as : List PositiveMass) (ho : as.Pairwise (fun a b => a.val ≤ b.val))
    (hu : ∀ a ∈ as, a.val ≤ 1) (l : ι → ℝ) (q r : ℕ → ι → ℝ)
    (hq : ∀ i, Monotone (fun j => q j i)) (hr : ∀ i, Monotone (fun j => r j i))
    (hql : ∀ i, l i ≤ q 0 i) (hrl : ∀ i, l i ≤ r 0 i)
    (B : ℕ → ℝ) (hB : ∀ j, j ≤ as.length → ∀ σ τ, -B j ≤ featureKernel φ (r j-q j) σ τ)
    (x : ι → ℝ) :
    disorderPressure w φ C as l r x-disorderPressure w φ C as l q x ≤ massStepSum as 0 B/2 := by
  let T : (ι → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun v => ∑ i, v i*C i
      map_add' := by intro v z; simp only [Pi.add_apply,add_mul,Finset.sum_add_distrib]
      map_smul' := by intro a v; simp only [Pi.smul_apply,smul_eq_mul,mul_assoc,Finset.mul_sum,RingHom.id_apply] }
  have hT (v : ι → ℝ) (σ : S) : ∑ i, v i*(φ σ (Pi.single i 1))^2 = T v := by
    simp only [hself,T,LinearMap.coe_mk,AddHom.coe_mk]
  have ha : OrderedSteps 0 (affineSteps (signedClockSteps as q r) 0) := by
    rw [signedClockSteps_zero]
    exact diagonalBoundarySteps_ordered as le_rfl zero_le_one ho hu (fun a _ => a.property.le) _ _
  have hs := signedClockSteps_admissible as q r hq hr
  have hh := rootedHierarchy_affine_chord_finite hw φ T (signedClockSteps as q r)
    (q 0-l) (r 0-q 0) (fun st _ => hT st.2.2) (hT (r 0-q 0))
    (fun tail => B (as.length-tail.length)) ha (signedClockSteps_kernelBound φ as q r B hB)
    (fun st hst i => (hs st hst i).1) (fun st hst i => (hs st hst i).2)
    (fun i => sub_nonneg.mpr (hql i))
    (fun i => by have hi := hrl i; dsimp only [Pi.sub_apply]; linarith) x
  rw [signedClockSteps_zero,signedClockSteps_one,signedClockSteps_trace,signedClockSteps_cost] at hh
  have he (i : ι) : (q 0-l) i+(r 0-q 0) i = r 0 i-l i := by dsimp only [Pi.sub_apply]; ring
  simp_rw [he,Pi.sub_apply] at hh
  have ht : T (r as.length-q as.length) =
      (∑ i, (r as.length i-l i)*C i)-(∑ i, (q as.length i-l i)*C i) := by
    change (∑ i, (r as.length i-q as.length i)*C i) = _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [ht] at hh
  unfold disorderPressure
  linarith

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
variable {ι κ S : Type*} [Fintype ι] [Fintype κ] [Fintype S]

 
def featureVector (φ : S → (ι → ℝ) →L[ℝ] ℝ) : (ι → ℝ) →L[ℝ] (S → ℝ) :=
  ContinuousLinearMap.pi φ

omit [Fintype ι] [Fintype S] in
@[simp] theorem featureVector_apply (φ : S → (ι → ℝ) →L[ℝ] ℝ) (x : ι → ℝ) (σ : S) :
    featureVector φ x σ = φ σ x := rfl

 

theorem charFunDual_featureVector [DecidableEq ι]
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (q : ι → ℝ≥0) (L : (S → ℝ) →L[ℝ] ℝ) :
    charFunDual ((Measure.pi fun i => gaussianReal 0 (q i)).map (featureVector φ)) L =
      Complex.exp (-((∑ i, (q i:ℝ)*(L (fun σ => φ σ (Pi.single i 1)))^2 : ℝ):ℂ)/2) := by
  rw [charFunDual_map,charFunDual_pi]
  simp_rw [IsGaussian.charFunDual_eq,integral_complex_ofReal,
    integral_continuousLinearMap_gaussianReal,variance_continuousLinearMap_gaussianReal]
  simp only [ContinuousLinearMap.comp_apply,map_zero,Complex.ofReal_zero,zero_mul,zero_sub,
    ContinuousLinearMap.single_apply,
    Real.coe_toNNReal _ (sq_nonneg _)]
  rw [← Complex.exp_sum]
  congr 1
  simp [featureVector,div_eq_mul_inv,Finset.mul_sum,mul_comm]

variable [DecidableEq S]

 

theorem finiteDual_expansion (L : (S → ℝ) →L[ℝ] ℝ) (x : S → ℝ) :
    L x = ∑ σ, L (Pi.single σ 1)*x σ := by
  rw [← L.sum_comp_single]
  apply Finset.sum_congr rfl
  intro σ _
  change L (Pi.single σ (x σ)) = _
  have hh : Pi.single σ (x σ) = x σ • Pi.single σ (1:ℝ) := by
    simpa only [smul_eq_mul,mul_one] using (Pi.single_smul (f := fun _ : S => ℝ) σ (x σ) (1:ℝ))
  rw [hh,map_smul]
  simp only [smul_eq_mul,mul_comm]

omit [DecidableEq S] in
 

theorem kernel_quadratic_identity (c : S → ι → ℝ) (q : ι → ℝ) (a : S → ℝ) :
    ∑ i, q i*(∑ σ, a σ*c σ i)^2 =
      ∑ σ, ∑ τ, a σ*a τ*(∑ i, q i*c σ i*c τ i) := by
  simp only [pow_two,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro τ _
  apply Finset.sum_congr rfl
  intro i _
  ring

 

theorem featureVector_law_eq [DecidableEq ι] [DecidableEq κ]
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (ψ : S → (κ → ℝ) →L[ℝ] ℝ)
    (q : ι → ℝ≥0) (r : κ → ℝ≥0)
    (hk : ∀ σ τ, (∑ i, (q i:ℝ)*φ σ (Pi.single i 1)*φ τ (Pi.single i 1)) =
      ∑ k, (r k:ℝ)*ψ σ (Pi.single k 1)*ψ τ (Pi.single k 1)) :
    (Measure.pi fun i => gaussianReal 0 (q i)).map (featureVector φ) =
      (Measure.pi fun k => gaussianReal 0 (r k)).map (featureVector ψ) := by
  apply Measure.ext_of_charFunDual
  ext L
  rw [charFunDual_featureVector,charFunDual_featureVector]
  have hφ : (∑ i, (q i:ℝ)*(L (fun σ => φ σ (Pi.single i 1)))^2) =
      ∑ σ, ∑ τ, L (Pi.single σ 1)*L (Pi.single τ 1)*
        (∑ i, (q i:ℝ)*φ σ (Pi.single i 1)*φ τ (Pi.single i 1)) := by
    rw [← kernel_quadratic_identity]
    apply Finset.sum_congr rfl
    intro i _
    rw [finiteDual_expansion L]
  have hψ : (∑ k, (r k:ℝ)*(L (fun σ => ψ σ (Pi.single k 1)))^2) =
      ∑ σ, ∑ τ, L (Pi.single σ 1)*L (Pi.single τ 1)*
        (∑ k, (r k:ℝ)*ψ σ (Pi.single k 1)*ψ τ (Pi.single k 1)) := by
    rw [← kernel_quadratic_identity]
    apply Finset.sum_congr rfl
    intro k _
    rw [finiteDual_expansion L]
  rw [hφ,hψ]
  simp_rw [hk]

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open scoped BigOperators

theorem massStepSum_const_mul (as : List PositiveMass) (C : ℕ → ℝ) (a k : ℝ) :
    massStepSum as a (fun j => k*C j) = k*massStepSum as a C := by
  induction as generalizing a C with
  | nil => change (1-a)*(k*C 0) = k*((1-a)*C 0); ring
  | cons b bs ih =>
    change (b.val-a)*(k*C 0)+massStepSum bs b.val (fun j => k*C (j+1)) = _
    rw [ih]
    change _ = k*((b.val-a)*C 0+massStepSum bs b.val (fun j => C (j+1)))
    ring

end SKFluctuations.Hierarchy

end

end OAI
