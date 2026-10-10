import Mathlib
import OAI.Probability.SKFluctuations.HasDerivWithinAtVectorHeatContinuation

namespace OAI

/-! Hierarchy Penalty. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

 
def hierarchyPenalty (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ) (v : ι → ℝ) :
    ℝ → List (GaussianStep ι) → (ι → ℝ) → ℝ
  | a, [] => fun x => (1-a)*(gaussianHierarchyMean w φ (fun σ => φ σ v) [] x)^2
  | a, (m,q)::tail => fun x =>
      (m-a)*(gaussianHierarchyMean w φ (fun σ => φ σ v) ((m,q)::tail) x)^2 +
      shiftedMean (Measure.pi fun i => gaussianReal 0 (q i)) m (gaussianHierarchy w φ tail)
        (hierarchyPenalty w φ v m tail) x

theorem hierarchyPenalty_smooth {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (v : ι → ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (r : ℕ) : BddSmooth r (hierarchyPenalty w φ v a steps) := by
  induction steps generalizing a with
  | nil =>
    simpa only [hierarchyPenalty,pow_two] using
      ((gaussianHierarchyMean_smooth hw φ _ [] ha r).mul
        (gaussianHierarchyMean_smooth hw φ _ [] ha r)).const_mul (1-a)
  | cons st tail ih =>
    rcases st with ⟨m,q⟩
    have hm := gaussianHierarchyMean_smooth hw φ (fun σ => φ σ v) ((m,q)::tail) ha r
    have hp := (ih ha.2.2.2).shiftedMean (gaussianHierarchy_regular hw φ tail ha.2.2.2 r)
      (gaussianHierarchy_integrable hw φ tail ha.2.2.2 m q)
    simpa only [hierarchyPenalty,pow_two] using ((hm.mul hm).const_mul (m-a)).add hp

 

theorem gaussianHierarchyResponse_mass_telescope {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (v : ι → ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (x : ι → ℝ) :
    gaussianHierarchyResponse w φ (fun σ => φ σ v) v steps x +
      a*(gaussianHierarchyMean w φ (fun σ => φ σ v) steps x)^2 =
    gaussianHierarchyMean w φ (fun σ => (φ σ v)^2) steps x - hierarchyPenalty w φ v a steps x := by
  induction steps generalizing a x with
  | nil =>
    have he : (∑ σ, spinWeight w φ x σ * φ σ v * φ σ v) =
        ∑ σ, spinWeight w φ x σ * (φ σ v)^2 := by
      apply Finset.sum_congr rfl
      intro σ _
      ring
    simp only [gaussianHierarchyResponse,hierarchyPenalty,he]
    change _ + a*_ = (∑ σ, spinWeight w φ x σ*(φ σ v)^2) - (1-a)*_
    ring
  | cons st tail ih =>
    rcases st with ⟨m,q⟩
    let ν := Measure.pi fun i => gaussianReal 0 (q i)
    have hi := gaussianHierarchy_integrable hw φ tail ha.2.2.2 m q x
    have hM := gaussianHierarchyMean_smooth hw φ (fun σ => φ σ v) tail ha.2.2.2 0
    have hMsq : BddSmooth 0 (fun y => (gaussianHierarchyMean w φ (fun σ => φ σ v) tail y)^2) := by
      simpa only [pow_two] using hM.mul hM
    have he : (fun y => gaussianHierarchyResponse w φ (fun σ => φ σ v) v tail y +
        m*(gaussianHierarchyMean w φ (fun σ => φ σ v) tail y)^2) =
        fun y => gaussianHierarchyMean w φ (fun σ => (φ σ v)^2) tail y - hierarchyPenalty w φ v m tail y :=
      funext fun y => ih ha.2.2.2 y
    have hh := congrArg (fun A => shiftedMean ν m (gaussianHierarchy w φ tail) A x) he
    rw [shiftedMean_add (gaussianHierarchyResponse_smooth hw φ _ _ tail ha.2.2.2 0)
      (hMsq.const_mul m) hi, shiftedMean_const_mul,
      shiftedMean_sub (gaussianHierarchyMean_smooth hw φ _ tail ha.2.2.2 0)
        (hierarchyPenalty_smooth hw φ v tail ha.2.2.2 0) hi] at hh
    simp only [gaussianHierarchyResponse,hierarchyPenalty]
    change _ + a*_ = shiftedMean ν m (gaussianHierarchy w φ tail)
      (gaussianHierarchyMean w φ (fun σ => (φ σ v)^2) tail) x - _
    simp only [pow_two] at hh ⊢
    linarith [hh]

theorem hierarchyPenalty_nonneg {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (v : ι → ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (x : ι → ℝ) :
    0 ≤ hierarchyPenalty w φ v a steps x := by
  induction steps generalizing a x with
  | nil => exact mul_nonneg (sub_nonneg.mpr ha.2) (sq_nonneg _)
  | cons st tail ih =>
    rcases st with ⟨m,q⟩
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr ha.2.1) (sq_nonneg _))
      (shiftedMean_nonneg (fun y => ih ha.2.2.2 y) (gaussianHierarchy_integrable hw φ tail ha.2.2.2 m q x))

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

theorem gaussianHierarchyMean_const {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (c : ℝ) (x : ι → ℝ) :
    gaussianHierarchyMean w φ (fun _ => c) steps x = c := by
  induction steps generalizing a x with
  | nil => simp only [gaussianHierarchyMean, ← Finset.sum_mul, sum_spinWeight hw, one_mul]
  | cons st tail ih =>
    rcases st with ⟨m,q⟩
    have hi := gaussianHierarchy_integrable hw φ tail ha.2.2.2 m q x
    simp only [gaussianHierarchyMean, shiftedMean, tiltedMean, ih ha.2.2.2, integral_const_mul]
    exact mul_div_cancel_right₀ c (partition_pos m hi).ne'

 

def featurePenalty [DecidableEq ι] (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (a : ℝ) (steps : List (GaussianStep ι)) (x : ι → ℝ) : ℝ :=
  ∑ i, hierarchyPenalty w φ (Pi.single i 1) a steps x

theorem featurePenalty_smooth [DecidableEq ι] {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {a : ℝ} (steps : List (GaussianStep ι))
    (ha : OrderedSteps a steps) (r : ℕ) : BddSmooth r (featurePenalty w φ a steps) := by
  exact BddSmooth.sum Finset.univ (fun i _ => hierarchyPenalty_smooth hw φ _ steps ha r)

theorem featurePenalty_nonneg [DecidableEq ι] {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {a : ℝ} (steps : List (GaussianStep ι))
    (ha : OrderedSteps a steps) (x : ι → ℝ) : 0 ≤ featurePenalty w φ a steps x :=
  Finset.sum_nonneg fun i _ => hierarchyPenalty_nonneg hw φ (Pi.single i 1) steps ha x

 

theorem feature_trace_telescope [DecidableEq ι] {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {q a : ℝ} (hq : ∀ σ, ∑ i, (φ σ (Pi.single i 1))^2 = q)
    (steps : List (GaussianStep ι)) (ha : OrderedSteps a steps) (x : ι → ℝ) :
    (∑ i, gaussianHierarchyResponse w φ (fun σ => φ σ (Pi.single i 1)) (Pi.single i 1) steps x) +
      a*(∑ i, (gaussianHierarchyMean w φ (fun σ => φ σ (Pi.single i 1)) steps x)^2) =
      q - featurePenalty w φ a steps x := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  simp_rw [gaussianHierarchyResponse_mass_telescope hw φ _ steps ha]
  rw [Finset.sum_sub_distrib]
  have he := congrFun (gaussianHierarchyMean_sum hw φ steps ha Finset.univ
    (fun i σ => (φ σ (Pi.single i 1))^2)) x
  simp_rw [hq] at he
  rw [gaussianHierarchyMean_const hw φ steps ha q x] at he
  rw [← he]
  rfl

theorem shiftedMean_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {ν : Measure E} [IsProbabilityMeasure ν]
    {F : E → ℝ} {A : ι → E → ℝ} {m : ℝ} (hA : ∀ i, BddSmooth 0 (A i))
    {x : E} (hi : Integrable (fun z => Real.exp (m*F (x+z))) ν) :
    shiftedMean ν m F (fun y => ∑ i, A i y) x = ∑ i, shiftedMean ν m F (A i) x := by
  simp only [shiftedMean,tiltedMean,Finset.sum_mul]
  rw [integral_finsetSum _ (fun i _ => (hA i).integrable_shifted_weighted hi),Finset.sum_div]

 

theorem clockDerivative_feature_trace {n : ℕ} {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {q m : ℝ}
    (hq : ∀ σ, ∑ i, (φ σ (Pi.single i 1))^2 = q) (tail : List (GaussianStep (Fin (n+1))))
    (ha : OrderedSteps m tail) (t : ℝ) (x : Fin (n+1) → ℝ) :
    clockDerivative m (gaussianHierarchy w φ tail)
      (fun i => gaussianHierarchyMean w φ (fun σ => φ σ (Pi.single i 1)) tail)
      (fun i => gaussianHierarchyResponse w φ (fun σ => φ σ (Pi.single i 1)) (Pi.single i 1) tail) t x =
      (1/2:ℝ)*(q-clockTest m (gaussianHierarchy w φ tail) (featurePenalty w φ m tail) t x) := by
  let ν := Measure.pi fun _ : Fin (n+1) => gaussianReal 0 (Real.toNNReal t)
  have hi := gaussianHierarchy_integrable hw φ tail ha m (fun _ => Real.toNNReal t) x
  have hH (i) := gaussianHierarchyResponse_smooth hw φ (fun σ => φ σ (Pi.single i 1))
    (Pi.single i 1) tail ha 0
  have hG (i) : BddSmooth 0 (fun y => (gaussianHierarchyMean w φ (fun σ => φ σ (Pi.single i 1)) tail y)^2) := by
    simpa only [pow_two] using (gaussianHierarchyMean_smooth hw φ (fun σ => φ σ (Pi.single i 1)) tail ha 0).mul
      (gaussianHierarchyMean_smooth hw φ (fun σ => φ σ (Pi.single i 1)) tail ha 0)
  have he := funext fun y => feature_trace_telescope hw φ hq tail ha y
  have hn := congrArg (fun A => shiftedMean ν m (gaussianHierarchy w φ tail) A x) he
  rw [shiftedMean_add (BddSmooth.sum Finset.univ (fun i _ => hH i))
      ((BddSmooth.sum Finset.univ (fun i _ => hG i)).const_mul m) hi,
    shiftedMean_const_mul, shiftedMean_sum hH hi, shiftedMean_sum hG hi] at hn
  have hc : shiftedMean ν m (gaussianHierarchy w φ tail) (fun _ => q) x = q := by
    simp only [shiftedMean,tiltedMean,integral_const_mul]
    exact mul_div_cancel_right₀ q (partition_pos m hi).ne'
  rw [shiftedMean_sub (BddSmooth.const 0 q) (featurePenalty_smooth hw φ tail ha 0) hi,hc] at hn
  exact congrArg (fun z : ℝ => (1/2)*z) hn

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι : Type*} [Fintype ι]

theorem prefixContinuation_lipschitz {F : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (front : List (GaussianStep ι))
    (hm : ∀ st ∈ front, 0 < st.1) : LipschitzWith C (prefixContinuation front F) := by
  induction front with
  | nil => exact hF
  | cons st tail ih =>
    rcases st with ⟨m,q⟩
    exact lipschitzWith_shiftedContinuation (ih (fun st hs => hm st (List.mem_cons_of_mem _ hs)))
      (hm (m,q) List.mem_cons_self)
      ((exponentialIncrement_gaussian q).integrable_shift
        (ih (fun st hs => hm st (List.mem_cons_of_mem _ hs))) m)

theorem prefixTest_smooth0 {F A : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hA : BddSmooth 0 A) (front : List (GaussianStep ι))
    (hm : ∀ st ∈ front, 0 < st.1) : BddSmooth 0 (prefixTest front F A) := by
  induction front with
  | nil => exact hA
  | cons st tail ih =>
    rcases st with ⟨m,q⟩
    have htail := fun st hs => hm st (List.mem_cons_of_mem _ hs)
    have hf := prefixContinuation_lipschitz hF tail htail
    have hi := (exponentialIncrement_gaussian q).integrable_shift hf m
    obtain ⟨B,hB,hb⟩ := (ih htail).bound
    exact ⟨continuous_shiftedMean hf (ih htail).continuous hB hb hi,B,hB,
      fun x => abs_tiltedMean_le ((ih htail).continuous.comp (continuous_const.add continuous_id)).measurable
        (hi x) (fun z => hb _)⟩

theorem prefixTest_affine {F A : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hA : BddSmooth 0 A) (front : List (GaussianStep ι))
    (hm : ∀ st ∈ front, 0 < st.1) (a b : ℝ) (x : ι → ℝ) :
    prefixTest front F (fun y => a+b*A y) x = a+b*prefixTest front F A x := by
  induction front generalizing x with
  | nil => rfl
  | cons st tail ih =>
    rcases st with ⟨m,q⟩
    have htail := fun st hs => hm st (List.mem_cons_of_mem _ hs)
    have hi := (exponentialIncrement_gaussian q).integrable_shift
      (prefixContinuation_lipschitz hF tail htail) m x
    simp only [prefixTest]
    rw [funext (ih htail)]
    rw [shiftedMean_add (BddSmooth.const 0 a) ((prefixTest_smooth0 hF hA tail htail).const_mul b) hi,
      shiftedMean_const_mul]
    congr 1
    simp only [shiftedMean,tiltedMean,integral_const_mul]
    exact mul_div_cancel_right₀ a (partition_pos m hi).ne'

theorem prefixTest_nonneg {F A : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hA : ∀ x, 0 ≤ A x) (front : List (GaussianStep ι))
    (hm : ∀ st ∈ front, 0 < st.1) (x : ι → ℝ) : 0 ≤ prefixTest front F A x := by
  induction front generalizing x with
  | nil => exact hA x
  | cons st tail ih =>
    rcases st with ⟨m,q⟩
    have htail := fun st hs => hm st (List.mem_cons_of_mem _ hs)
    exact shiftedMean_nonneg (ih htail) ((exponentialIncrement_gaussian q).integrable_shift
      (prefixContinuation_lipschitz hF tail htail) m x)

theorem zeroContinuation_affine {F : (ι → ℝ) → ℝ} (hF : BddSmooth 0 F)
    (q : ι → ℝ≥0) (a b : ℝ) (x : ι → ℝ) :
    zeroContinuation (Measure.pi fun i => gaussianReal 0 (q i)) (fun y => a+b*F y) x =
      a+b*zeroContinuation (Measure.pi fun i => gaussianReal 0 (q i)) F x := by
  let ν := Measure.pi fun i => gaussianReal 0 (q i)
  obtain ⟨B,hB,hb⟩ := hF.bound
  have hi : Integrable (fun z => F (x+z)) ν := by
    apply (integrable_const B).mono' (hF.continuous.comp (continuous_const.add continuous_id)).aestronglyMeasurable
    exact Eventually.of_forall fun z => by
      change |F (x+z)| ≤ B
      exact hb _
  simp only [zeroContinuation]
  rw [integral_add (integrable_const _) (hi.const_mul b),integral_const_mul]
  simp [ν]

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S]

 

theorem rootedHierarchy_corrected_clock {n : ℕ} {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {Q : ℝ}
    (hQ : ∀ σ, ∑ i, (φ σ (Pi.single i 1))^2 = Q)
    (front tail : List (GaussianStep (Fin (n+1)))) {m : ℝ} (hm : 0 < m)
    (ha : OrderedSteps m tail) (hfront : ∀ st ∈ front, 0 < st.1)
    (q₀ : Fin (n+1) → ℝ≥0) {t : ℝ} (ht : 0 < t) (x : Fin (n+1) → ℝ) :
    HasDerivAt
      (fun s => zeroContinuation (Measure.pi fun i => gaussianReal 0 (q₀ i))
        (gaussianHierarchy w φ (front ++ (m,fun _ => Real.toNNReal s)::tail)) x-Q*s/2)
      (-(1/2:ℝ)*zeroContinuation (Measure.pi fun i => gaussianReal 0 (q₀ i))
        (prefixTest front (clockContinuation m (gaussianHierarchy w φ tail) t)
          (clockTest m (gaussianHierarchy w φ tail) (featurePenalty w φ m tail) t)) x) t := by
  have hh := (rootedHierarchy_inserted_clock hw φ front tail hm ha hfront q₀ ht x).sub
    (((hasDerivAt_id t).const_mul Q).div_const 2)
  obtain ⟨C,hF⟩ := (gaussianHierarchy_regular hw φ tail ha 0).1
  have hi := gaussianHierarchy_integrable hw φ tail ha m (fun _ => Real.toNNReal t)
  have hP : BddSmooth 0 (clockTest m (gaussianHierarchy w φ tail) (featurePenalty w φ m tail) t) :=
    (featurePenalty_smooth hw φ tail ha 0).shiftedMean (gaussianHierarchy_regular hw φ tail ha 0) hi
  have hC : LipschitzWith C (clockContinuation m (gaussianHierarchy w φ tail) t) :=
    lipschitzWith_shiftedContinuation hF hm hi
  have hPT := prefixTest_smooth0 hC hP front hfront
  have he : clockDerivative m (gaussianHierarchy w φ tail)
      (fun i => gaussianHierarchyMean w φ (fun σ => φ σ (Pi.single i 1)) tail)
      (fun i => gaussianHierarchyResponse w φ (fun σ => φ σ (Pi.single i 1)) (Pi.single i 1) tail) t =
      fun y => Q/2+(-(1/2:ℝ))*clockTest m (gaussianHierarchy w φ tail) (featurePenalty w φ m tail) t y := by
    funext y
    rw [clockDerivative_feature_trace hw φ hQ tail ha t y]
    ring
  rw [he] at hh
  have he' := funext (prefixTest_affine hC hP front hfront (Q/2) (-(1/2:ℝ)))
  rw [he',zeroContinuation_affine hPT q₀ (Q/2) (-(1/2:ℝ)) x] at hh
  exact hh.congr_deriv (by ring)

 

theorem corrected_clock_derivative_nonpos {n : ℕ} {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ)
    (front tail : List (GaussianStep (Fin (n+1)))) {m : ℝ} (hm : 0 < m)
    (ha : OrderedSteps m tail) (hfront : ∀ st ∈ front, 0 < st.1)
    (q₀ : Fin (n+1) → ℝ≥0) (t : ℝ) (x : Fin (n+1) → ℝ) :
    -(1/2:ℝ)*zeroContinuation (Measure.pi fun i => gaussianReal 0 (q₀ i))
      (prefixTest front (clockContinuation m (gaussianHierarchy w φ tail) t)
        (clockTest m (gaussianHierarchy w φ tail) (featurePenalty w φ m tail) t)) x ≤ 0 := by
  obtain ⟨C,hF⟩ := (gaussianHierarchy_regular hw φ tail ha 0).1
  have hi := gaussianHierarchy_integrable hw φ tail ha m (fun _ => Real.toNNReal t)
  have hC : LipschitzWith C (clockContinuation m (gaussianHierarchy w φ tail) t) :=
    lipschitzWith_shiftedContinuation hF hm hi
  have hP (y) : 0 ≤ clockTest m (gaussianHierarchy w φ tail) (featurePenalty w φ m tail) t y :=
    shiftedMean_nonneg (featurePenalty_nonneg hw φ tail ha) (hi y)
  exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (integral_nonneg
    (fun z => prefixTest_nonneg hC hP front hfront (x+z)))

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S]

 

theorem rootedHierarchy_corrected_root {n : ℕ} {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {Q : ℝ}
    (hQ : ∀ σ, ∑ i, (φ σ (Pi.single i 1))^2 = Q)
    (tail : List (GaussianStep (Fin (n+1)))) (ha : OrderedSteps 0 tail)
    {t : ℝ} (ht : 0 ≤ t) (x : Fin (n+1) → ℝ) :
    HasDerivWithinAt (fun s => clockRoot (gaussianHierarchy w φ tail) s x-Q*s/2)
      (-(1/2:ℝ)*clockRoot (featurePenalty w φ 0 tail) t x) (Ici 0) t := by
  obtain ⟨C,hF⟩ := (gaussianHierarchy_regular hw φ tail ha 0).1
  have hG (i) := gaussianHierarchyMean_smooth hw φ (fun σ => φ σ (Pi.single i 1)) tail ha 0
  have hH (i) := gaussianHierarchyResponse_smooth hw φ (fun σ => φ σ (Pi.single i 1)) (Pi.single i 1) tail ha 0
  have hh := (hasDerivWithinAt_clockRoot hF hG hH
    (fun y v s => by
      rw [← gaussianHierarchyMean_feature_components hw φ tail ha v (y+s • v)]
      exact gaussianHierarchy_hasDerivAt hw φ tail ha y v s)
    (fun i y s => gaussianHierarchyMean_hasDerivAt hw φ _ tail ha y _ s) ht x).sub
    ((((hasDerivAt_id t).const_mul Q).div_const 2).hasDerivWithinAt)
  have he : (fun y => ∑ i, gaussianHierarchyResponse w φ
      (fun σ => φ σ (Pi.single i 1)) (Pi.single i 1) tail y) =
      fun y => Q+(-1)*featurePenalty w φ 0 tail y := by
    funext y
    have he := feature_trace_telescope hw φ hQ tail ha y
    simpa only [zero_mul,add_zero,neg_one_mul,← sub_eq_add_neg] using he
  rw [he] at hh
  change HasDerivWithinAt _ ((1/2)*zeroContinuation _ (fun y => Q+(-1)*featurePenalty w φ 0 tail y) x-Q*1/2) _ _ at hh
  rw [zeroContinuation_affine (featurePenalty_smooth hw φ tail ha 0) (fun _ => Real.toNNReal t) Q (-1) x] at hh
  exact hh.congr_deriv (by unfold clockRoot; ring)

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal
variable {ι : Type*} [Fintype ι]

theorem clockContinuation_continuousOn {F : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (m : ℝ) (x : ι → ℝ) :
    ContinuousOn (fun t => clockContinuation m F t x) (Ici 0) := by
  let ν := Measure.pi fun _ : ι => gaussianReal 0 1
  have hν : ExponentialIncrement ν := exponentialIncrement_gaussian (fun _ => 1)
  have he := ExpNormBounded.exp_lipschitz hF m
  have hc := he.continuous_gaussian_variance hν x
  have hn (t : ℝ) : (∫ z, Real.exp (m*F (x+Real.sqrt t • z)) ∂ν) ≠ 0 :=
    (partition_pos m (he.affine_integrable hν x (Real.sqrt t))).ne'
  have hp : Continuous (fun t => Real.log (∫ z, Real.exp (m*F (x+Real.sqrt t • z)) ∂ν)/m) :=
    (hc.log hn).div_const m
  exact hp.continuousOn.congr (fun t ht => clockContinuation_eq hF.continuous m ht x)

theorem clockTest_continuousOn {F A : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hA : BddSmooth 0 A) (m : ℝ) (x : ι → ℝ) :
    ContinuousOn (fun t => clockTest m F A t x) (Ici 0) := by
  let ν := Measure.pi fun _ : ι => gaussianReal 0 1
  have hν : ExponentialIncrement ν := exponentialIncrement_gaussian (fun _ => 1)
  have he := ExpNormBounded.exp_lipschitz hF m
  have hn := (he.bdd_mul hA).continuous_gaussian_variance hν x
  have hd := he.continuous_gaussian_variance hν x
  have hp (t : ℝ) : (∫ z, Real.exp (m*F (x+Real.sqrt t • z)) ∂ν) ≠ 0 :=
    (partition_pos m (he.affine_integrable hν x (Real.sqrt t))).ne'
  have hc : Continuous (fun t => tiltedMean ν m (fun z => F (x+Real.sqrt t • z))
      (fun z => A (x+Real.sqrt t • z))) := hn.div hd hp
  exact hc.continuousOn.congr (fun t ht => clockTest_eq hF.continuous hA.continuous m ht x)

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  {ν : Measure E} [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure ν] in
 

theorem continuousWithinAt_testedPartition {U : Set ℝ} {t m K : ℝ} {C : ℝ≥0}
    {F A : ℝ → E → ℝ} (hν : ExponentialIncrement ν)
    (hF : ∀ s ∈ U, LipschitzWith C (F s))
    (hA : ∀ s ∈ U, Continuous (A s))
    (hb : ∀ s ∈ U, ∀ y, |A s y| ≤ K)
    (hFt : ∀ y, ContinuousWithinAt (fun s => F s y) U t)
    (hAt : ∀ y, ContinuousWithinAt (fun s => A s y) U t) (x : E) :
    ContinuousWithinAt (fun s => ∫ z, A s (x+z)*Real.exp (m*F s (x+z)) ∂ν) U t := by
  have hbase : ∀ᶠ s in 𝓝[U] t, |F s x| < |F t x|+1 :=
    (hFt x).abs.eventually (eventually_lt_nhds (by linarith : |F t x| < |F t x|+1))
  let B := |F t x|+1
  apply continuousWithinAt_of_dominated
    (bound := fun z => K*Real.exp (|m| *B)*Real.exp (|m| *C*‖z‖))
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact (((hA s hs).comp (continuous_const.add continuous_id)).mul
      (((hF s hs).continuous.comp (continuous_const.add continuous_id)).const_mul m).rexp).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin,hbase] with s hs hbase
    apply Eventually.of_forall
    intro z
    have hK : 0 ≤ K := (abs_nonneg (A s x)).trans (hb s hs x)
    have hdiff : |F s (x+z)-F s x| ≤ (C:ℝ)*‖z‖ := by
      simpa only [dist_eq_norm,add_sub_cancel_left,Real.norm_eq_abs] using (hF s hs).dist_le_mul (x+z) x
    have hale : |F s (x+z)| ≤ B+(C:ℝ)*‖z‖ := by
      have hh := abs_add_le (F s (x+z)-F s x) (F s x)
      rw [sub_add_cancel] at hh
      dsimp [B]; linarith
    have hexp : Real.exp (m*F s (x+z)) ≤ Real.exp (|m| *B)*Real.exp (|m| *C*‖z‖) := by
      rw [← Real.exp_add,Real.exp_le_exp]
      have h1 := (le_abs_self (m*F s (x+z))).trans_eq (abs_mul m (F s (x+z)))
      have h2 := mul_le_mul_of_nonneg_left hale (abs_nonneg m)
      nlinarith
    change |A s (x+z)*Real.exp (m*F s (x+z))| ≤ _
    rw [abs_mul,abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul (hb s hs _) hexp (Real.exp_nonneg _) hK).trans_eq (by ring)
  · exact (hν (|m| *C)).const_mul _
  · exact Eventually.of_forall fun z => (hAt (x+z)).mul (((hFt (x+z)).const_mul m).rexp)

 
theorem continuousWithinAt_shiftedContinuation {U : Set ℝ} {t m : ℝ} {C : ℝ≥0}
    {F : ℝ → E → ℝ} (hν : ExponentialIncrement ν) (ht : t ∈ U)
    (hF : ∀ s ∈ U, LipschitzWith C (F s))
    (hFt : ∀ y, ContinuousWithinAt (fun s => F s y) U t) (x : E) :
    ContinuousWithinAt (fun s => shiftedContinuation ν m (F s) x) U t := by
  have hh := continuousWithinAt_testedPartition (A := fun _ _ => 1) (K := 1) (m := m)
    hν hF (fun _ _ => continuous_const) (fun _ _ _ => by norm_num) hFt
    (fun _ => continuousWithinAt_const) x
  simp only [one_mul] at hh
  exact (hh.log (partition_pos m (hν.integrable_shift (hF t ht) m x)).ne').div_const m

 theorem continuousWithinAt_shiftedMean {U : Set ℝ} {t m K : ℝ} {C : ℝ≥0}
    {F A : ℝ → E → ℝ} (hν : ExponentialIncrement ν) (ht : t ∈ U)
    (hF : ∀ s ∈ U, LipschitzWith C (F s))
    (hA : ∀ s ∈ U, Continuous (A s))
    (hb : ∀ s ∈ U, ∀ y, |A s y| ≤ K)
    (hFt : ∀ y, ContinuousWithinAt (fun s => F s y) U t)
    (hAt : ∀ y, ContinuousWithinAt (fun s => A s y) U t) (x : E) :
    ContinuousWithinAt (fun s => shiftedMean ν m (F s) (A s) x) U t := by
  have hn := continuousWithinAt_testedPartition hν hF hA hb hFt hAt x (m := m)
  have hd := continuousWithinAt_testedPartition (A := fun _ _ => 1) (K := 1) (m := m)
    hν hF (fun _ _ => continuous_const) (fun _ _ _ => by norm_num) hFt
    (fun _ => continuousWithinAt_const) x
  simp only [one_mul] at hd
  exact hn.div hd (partition_pos m (hν.integrable_shift (hF t ht) m x)).ne'

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  {ν : Measure E} [IsProbabilityMeasure ν]

theorem continuousWithinAt_zeroContinuation {U : Set ℝ} {t : ℝ} {C : ℝ≥0}
    {F : ℝ → E → ℝ} (hν : ExponentialIncrement ν)
    (hF : ∀ s ∈ U, LipschitzWith C (F s))
    (hFt : ∀ y, ContinuousWithinAt (fun s => F s y) U t) (x : E) :
    ContinuousWithinAt (fun s => zeroContinuation ν (F s) x) U t := by
  have hbase : ∀ᶠ s in 𝓝[U] t, |F s x| < |F t x|+1 :=
    (hFt x).abs.eventually (eventually_lt_nhds (by linarith : |F t x| < |F t x|+1))
  apply continuousWithinAt_of_dominated (bound := fun z => (|F t x|+1)+(C:ℝ)*‖z‖)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact ((hF s hs).continuous.comp (continuous_const.add continuous_id)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin,hbase] with s hs hbase
    apply Eventually.of_forall
    intro z
    have hdiff : |F s (x+z)-F s x| ≤ (C:ℝ)*‖z‖ := by
      simpa only [dist_eq_norm,add_sub_cancel_left,Real.norm_eq_abs] using (hF s hs).dist_le_mul (x+z) x
    have hh := abs_add_le (F s (x+z)-F s x) (F s x)
    rw [sub_add_cancel] at hh
    change |F s (x+z)| ≤ _
    linarith
  · exact (integrable_const _).add (hν.integrable_norm.const_mul _)
  · exact Eventually.of_forall fun z => hFt (x+z)

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal
variable {ι : Type*} [Fintype ι]

 

structure ParametricContinuous (U : Set ℝ) (C : ℝ≥0) (K : ℝ)
    (F A : ℝ → (ι → ℝ) → ℝ) : Prop where
  nonneg : 0 ≤ K
  spatial : ∀ t ∈ U, LipschitzWith C (F t)
  test_spatial : ∀ t ∈ U, Continuous (A t)
  bounded : ∀ t ∈ U, ∀ x, |A t x| ≤ K
  potential : ∀ x, ContinuousOn (fun t => F t x) U
  tested : ∀ x, ContinuousOn (fun t => A t x) U

theorem ParametricContinuous.step {U : Set ℝ} {C : ℝ≥0} {K : ℝ}
    {F A : ℝ → (ι → ℝ) → ℝ} (h : ParametricContinuous U C K F A)
    {m : ℝ} (hm : 0 < m) (q : ι → ℝ≥0) :
    ParametricContinuous U C K
      (fun t => shiftedContinuation (Measure.pi fun i => gaussianReal 0 (q i)) m (F t))
      (fun t => shiftedMean (Measure.pi fun i => gaussianReal 0 (q i)) m (F t) (A t)) := by
  have hi (t) (ht : t ∈ U) (x) := (exponentialIncrement_gaussian q).integrable_shift (h.spatial t ht) m x
  refine ⟨h.nonneg, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun t ht => lipschitzWith_shiftedContinuation (h.spatial t ht) hm (hi t ht)
  · exact fun t ht => continuous_shiftedMean (h.spatial t ht) (h.test_spatial t ht)
      h.nonneg (h.bounded t ht) (hi t ht)
  · exact fun t ht x => abs_tiltedMean_le
      ((h.test_spatial t ht).comp (continuous_const.add continuous_id)).measurable
      (hi t ht x) (fun z => h.bounded t ht (x+z))
  · exact fun x t ht => continuousWithinAt_shiftedContinuation
      (exponentialIncrement_gaussian q) ht h.spatial (fun y => h.potential y t ht) x
  · exact fun x t ht => continuousWithinAt_shiftedMean
      (exponentialIncrement_gaussian q) ht h.spatial h.test_spatial h.bounded
      (fun y => h.potential y t ht) (fun y => h.tested y t ht) x

theorem ParametricContinuous.prefix {U : Set ℝ} {C : ℝ≥0} {K : ℝ}
    {F A : ℝ → (ι → ℝ) → ℝ} (h : ParametricContinuous U C K F A)
    (steps : List (GaussianStep ι)) (hm : ∀ st ∈ steps, 0 < st.1) :
    ParametricContinuous U C K (fun t => prefixContinuation steps (F t))
      (fun t => prefixTest steps (F t) (A t)) := by
  induction steps with
  | nil => exact h
  | cons st tail ih =>
    rcases st with ⟨m,q⟩
    exact (ih (fun s hs => hm s (List.mem_cons_of_mem _ hs))).step (hm _ List.mem_cons_self) q

theorem ParametricContinuous.root {U : Set ℝ} {C : ℝ≥0} {K : ℝ}
    {F A : ℝ → (ι → ℝ) → ℝ} (h : ParametricContinuous U C K F A)
    (q : ι → ℝ≥0) :
    ParametricContinuous U C K
      (fun t => zeroContinuation (Measure.pi fun i => gaussianReal 0 (q i)) (F t))
      (fun t => zeroContinuation (Measure.pi fun i => gaussianReal 0 (q i)) (A t)) := by
  let ν := Measure.pi fun i => gaussianReal 0 (q i)
  have hi (t) (ht : t ∈ U) (x) := (exponentialIncrement_gaussian q).integrable_lipschitz (h.spatial t ht) x
  refine ⟨h.nonneg, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun t ht => zeroContinuation_lipschitz (h.spatial t ht) (hi t ht)
  · intro t ht
    have hh := continuous_shiftedMean (ν := ν) (m := 0) (LipschitzWith.const (0:ℝ))
      (h.test_spatial t ht) h.nonneg (h.bounded t ht) (fun x => by simp)
    have he : shiftedMean ν 0 (fun _ : ι → ℝ => (0:ℝ)) (A t) = zeroContinuation ν (A t) :=
      funext fun x => shiftedMean_zero _ _ x
    rw [he] at hh
    exact hh
  · intro t ht x
    calc
      |zeroContinuation ν (A t) x| ≤ ∫ z, |A t (x+z)| ∂ν := abs_integral_le_integral_abs
      _ ≤ ∫ _ : ι → ℝ, K ∂ν := integral_mono_of_nonneg
        (Eventually.of_forall fun _ => abs_nonneg _) (integrable_const _)
        (Eventually.of_forall fun z => h.bounded t ht (x+z))
      _ = K := by simp
  · exact fun x t ht => continuousWithinAt_zeroContinuation (exponentialIncrement_gaussian q)
      h.spatial (fun y => h.potential y t ht) x
  · intro x t ht
    apply continuousWithinAt_of_dominated (bound := fun _ : ι → ℝ => K)
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact ((h.test_spatial s hs).comp (continuous_const.add continuous_id)).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using h.bounded s hs (x+z)
    · exact integrable_const _
    · exact Eventually.of_forall fun z => h.tested (x+z) t ht

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι : Type*} [Fintype ι]

theorem parametric_continuous_clock {F A : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hA : BddSmooth 0 A) {m : ℝ} (hm : 0 < m) :
    ∃ K, ParametricContinuous (Ici 0) C K (clockContinuation m F) (clockTest m F A) := by
  obtain ⟨K,hK,hb⟩ := hA.bound
  have hi (t : ℝ) (x : ι → ℝ) :=
    (exponentialIncrement_gaussian (fun _ : ι => Real.toNNReal t)).integrable_shift hF m x
  exact ⟨K,hK,fun t _ => lipschitzWith_shiftedContinuation hF hm (hi t),
    fun t _ => continuous_shiftedMean hF hA.continuous hK hb (hi t),
    fun t _ x => abs_tiltedMean_le (hA.continuous.comp (continuous_const.add continuous_id)).measurable
      (hi t x) (fun z => hb (x+z)),
    fun x => clockContinuation_continuousOn hF m x,
    fun x => clockTest_continuousOn hF hA m x⟩

 

theorem rootedHierarchy_corrected_clock_zero {n : ℕ} {S : Type*} [Fintype S] [Nonempty S]
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ) (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {Q : ℝ}
    (hQ : ∀ σ, ∑ i, (φ σ (Pi.single i 1))^2 = Q)
    (front tail : List (GaussianStep (Fin (n+1)))) {m : ℝ} (hm : 0 < m)
    (ha : OrderedSteps m tail) (hfront : ∀ st ∈ front, 0 < st.1)
    (q₀ : Fin (n+1) → ℝ≥0) (x : Fin (n+1) → ℝ) :
    HasDerivWithinAt
      (fun s => zeroContinuation (Measure.pi fun i => gaussianReal 0 (q₀ i))
        (gaussianHierarchy w φ (front ++ (m,fun _ => Real.toNNReal s)::tail)) x-Q*s/2)
      (-(1/2:ℝ)*zeroContinuation (Measure.pi fun i => gaussianReal 0 (q₀ i))
        (prefixTest front (clockContinuation m (gaussianHierarchy w φ tail) 0)
          (clockTest m (gaussianHierarchy w φ tail) (featurePenalty w φ m tail) 0)) x) (Ici 0) 0 := by
  obtain ⟨C,hC⟩ := (gaussianHierarchy_regular hw φ tail ha 0).1
  obtain ⟨K,hK⟩ := parametric_continuous_clock hC (featurePenalty_smooth hw φ tail ha 0) hm
  have hc := (hK.prefix front hfront).root q₀
  have he (s : ℝ) : prefixContinuation front (clockContinuation m (gaussianHierarchy w φ tail) s) =
      gaussianHierarchy w φ (front ++ (m,fun _ => Real.toNNReal s)::tail) :=
    prefixContinuation_hierarchy w φ front ((m,fun _ => Real.toNNReal s)::tail)
  have hp := (hc.potential x).sub ((continuous_id.const_mul Q).div_const 2).continuousOn
  simp_rw [he] at hp
  have hd := (hc.tested x).const_mul (-(1/2:ℝ))
  apply hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioi 0)
  · intro s hs
    exact (rootedHierarchy_corrected_clock hw φ hQ front tail hm ha hfront q₀ hs x).differentiableAt.differentiableWithinAt
  · exact (hp 0 (by simp)).mono Ioi_subset_Ici_self
  · exact self_mem_nhdsWithin
  · have hlim := (hd 0 (by simp)).tendsto.mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self)
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (rootedHierarchy_corrected_clock hw φ hQ front tail hm ha hfront q₀ hs x).deriv.symm

theorem rootedHierarchy_corrected_clock_nonneg {n : ℕ} {S : Type*} [Fintype S] [Nonempty S]
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ) (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {Q : ℝ}
    (hQ : ∀ σ, ∑ i, (φ σ (Pi.single i 1))^2 = Q)
    (front tail : List (GaussianStep (Fin (n+1)))) {m : ℝ} (hm : 0 < m)
    (ha : OrderedSteps m tail) (hfront : ∀ st ∈ front, 0 < st.1)
    (q₀ : Fin (n+1) → ℝ≥0) {t : ℝ} (ht : 0 ≤ t) (x : Fin (n+1) → ℝ) :
    HasDerivWithinAt
      (fun s => zeroContinuation (Measure.pi fun i => gaussianReal 0 (q₀ i))
        (gaussianHierarchy w φ (front ++ (m,fun _ => Real.toNNReal s)::tail)) x-Q*s/2)
      (-(1/2:ℝ)*zeroContinuation (Measure.pi fun i => gaussianReal 0 (q₀ i))
        (prefixTest front (clockContinuation m (gaussianHierarchy w φ tail) t)
          (clockTest m (gaussianHierarchy w φ tail) (featurePenalty w φ m tail) t)) x) (Ici 0) t := by
  rcases eq_or_lt_of_le ht with ht | ht
  · subst t
    exact rootedHierarchy_corrected_clock_zero hw φ hQ front tail hm ha hfront q₀ x
  · exact (rootedHierarchy_corrected_clock hw φ hQ front tail hm ha hfront q₀ ht x).hasDerivWithinAt

end SKFluctuations.Hierarchy

end

end OAI
