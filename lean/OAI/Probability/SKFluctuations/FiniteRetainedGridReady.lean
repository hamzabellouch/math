import Mathlib
import OAI.Probability.SKFluctuations.PhysicalPinnedWindow

namespace OAI

/-! Finite Retained Grid Ready. -/

noncomputable section


namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal

 theorem finiteRetainedGridReady (n : ℕ) (hn : 0<n)
    (b h : ℝ → ℝ≥0) (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (us : List PositiveMass) (hus : ∀ u ∈ us, u.val ≤ 1)
    (C : PositiveMass → ℝ) (hC : ∀ u ∈ us, orderedPathS n b h u.val < C u)
    {r₀ u₀ c : ℝ} {k M : ℝ → ℝ}
    (hr : r₀ ≤ 1) (hu : u₀ ≤ 1) (hc : 0<c)
    (hk : ContinuousOn k (Icc r₀ 1)) (hkc : ∀ t ∈ Icc r₀ 1, c ≤ k t)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)
    (α : inverseIntegralConstraints r₀ u₀ k M) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ j : ℕ in atTop,
      let as := finiteCutMasses us j
      let has := finiteCutMasses_ordered us hus j
      let steps := sampleClockSteps (completedPathClock n b h) 0 as
      let hs := sampleClockSteps_ordered (completedPathClock n b h) as has
      let r := physicalQuantileGrid hr hu hc hk hkc hm hM α steps hs
      (∀ i : Fin (steps.length+1), r i.succ-r i.castSucc ≤ ε) ∧
      (∀ u ∈ us, ∀ i ≤ (physicalRetainedIndex steps u.val).val,
        physicalPathSecondMoment n steps ((completedPathClock n b h) 0) i ≤ C u) := by
  have hmom := finiteRetainedMeans_eventually n hn b h hb hh us hus C hC
  have hmesh : ∀ᶠ j : ℕ in atTop, (((j+1:ℕ):ℝ)⁻¹)/c ≤ ε := by
    exact ((uniformMasses_mesh_tendsto.div_const c).eventually (gt_mem_nhds (by simpa using hε))).mono
      (fun j hj => by simpa using hj.le)
  filter_upwards [hmom,hmesh] with j hj hmj
  dsimp only at hj ⊢
  constructor
  · intro i
    exact (physicalQuantileGrid_mesh hr hu hc hk hkc hm hM α _ _
      (sampled_physicalMass_mesh _ _ (finiteCutMasses_mesh us hus j)) i).trans hmj
  · exact hj

 theorem retainedWindow_future_means (n : ℕ) (q₀ : ℝ → FeatureIndex n → ℝ≥0)
    (as : List PositiveMass) (has : MassOrdered 0 as)
    (p q : PositiveMass) (hpm : p ∈ as) (i : ℕ)
    (hi : physicalCutMass 0 (sampleClockSteps q₀ 0 as) i < p.val)
    {C : ℝ}
    (hmean : ∀ j ≤ (physicalRetainedIndex (sampleClockSteps q₀ 0 as) q.val).val,
      physicalPathSecondMoment n (sampleClockSteps q₀ 0 as) (q₀ 0) j ≤ C) :
    let steps := sampleClockSteps q₀ 0 as
    let selected := physicalIntervalCells steps (physicalRetainedIndex steps p.val).val
      (physicalRetainedIndex steps q.val).val
    (∀ j ∈ selected, i ≤ j.val) ∧
    (∀ j ∈ selected, (∫ z, ‖actualSpinPath n steps id j.val z‖^2
      ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) (q₀ 0) steps) ≤ C) := by
  dsimp only
  have hip := physicalRetainedIndex_after q₀ as has p hpm i hi
  constructor
  · intro j hj
    have hh := (mem_physicalIntervalCells _ _ _ j).mp hj
    exact hip.trans hh.1
  · intro j hj
    have hh := (mem_physicalIntervalCells _ _ _ j).mp hj
    exact hmean j.val (Nat.le_of_lt hh.2)

end SKFluctuations

 

 

namespace SKFluctuations.Hierarchy.ClockTree
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal BigOperators
variable {S : Type*}

 
def pairPower (as : List PositiveMass) : ℕ → ClockTree S as
  | 0 => single as
  | l+1 => (pairClock as 0).fork (pairPower as l)

def pairPowerTest (as : List PositiveMass) (P : S → S → ℝ) :
    (l : ℕ) → (pairPower (S:=S) as l).Assignment → ℝ
  | 0, _ => 1
  | l+1, σ => P (pairSpin as 0 σ.1).1 (pairSpin as 0 σ.1).2 * pairPowerTest as P l σ.2

 
def powerClock : (pre post : List PositiveMass) → ℕ → ClockTree S (pre++post)
  | [], post, l => pairPower post l
  | a::pre, post, l => (powerClock pre post l).step a

def powerTest : (pre post : List PositiveMass) → (l : ℕ) → (S → S → ℝ) →
    (powerClock (S:=S) pre post l).Assignment → ℝ
  | [], post, l, P, σ => pairPowerTest post P l σ
  | _::pre, post, l, P, σ => powerTest pre post l P σ

variable {ι : Type*} [Fintype S] [Nonempty S] [Fintype ι]

omit [Nonempty S] in
 theorem expect_mul_constant [Nonempty S] (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (q : ℕ → ι → ℝ≥0)
    (P : T.Assignment → ℝ) (c : ℝ) (x : ι → ℝ) :
    T.expect w φ q (fun σ => P σ*c) x = T.expect w φ q P x*c := by
  simp only [expect,Finset.sum_mul,mul_assoc]

 theorem pairPower_expect {w : S → ℝ} (hw : ∀ σ,0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (as : List PositiveMass) {a : ℝ}
    (ho : MassOrdered a as) (q : ℕ → ι → ℝ≥0) (P : S → S → ℝ) (l : ℕ) (x : ι → ℝ) :
    (pairPower as l).expect w φ q (pairPowerTest as P l) x = (pairMean w φ as q 0 P x)^l := by
  induction l with
  | zero => simpa only [pairPower,pairPowerTest,pow_zero] using (single as).expect_const hw φ ho q 1 x
  | succ l ih =>
    simp only [pairPower,pairPowerTest,expect_fork]
    simp_rw [mul_comm (P _ _),expect_mul_constant,ih]
    simp_rw [mul_comm ((pairMean w φ as q 0 P x)^l)]
    rw [expect_mul_constant,pairClock_expect hw φ as ho]
    rw [pow_succ]
    ring

omit [Fintype S] [Nonempty S] in
 theorem pairPower_bound [Fintype S] [Nonempty S] (as : List PositiveMass) (P : S → S → ℝ) (l : ℕ)
    {C : ℝ} (hC : 0≤C) (hP : ∀ σ τ, |P σ τ|≤C)
    (σ : (pairPower (S:=S) as l).Assignment) : |pairPowerTest as P l σ|≤C^l := by
  induction l with
  | zero => simp [pairPowerTest]
  | succ l ih =>
    change |P _ _*pairPowerTest as P l σ.2|≤_
    rw [abs_mul,pow_succ]
    exact (mul_le_mul (hP _ _) (ih σ.2) (abs_nonneg _) hC).trans_eq (mul_comm _ _)

 theorem powerTest_bound (pre post : List PositiveMass) (l : ℕ) (P : S → S → ℝ)
    {C : ℝ} (hC : 0≤C) (hP : ∀ σ τ, |P σ τ|≤C)
    (σ : (powerClock (S:=S) pre post l).Assignment) : |powerTest pre post l P σ|≤C^l := by
  induction pre with
  | nil => exact pairPower_bound post P l hC hP σ
  | cons a pre ih => exact ih σ

omit [Fintype S] [Nonempty S] in
 theorem pairPower_leaves [Fintype S] [Nonempty S] (as : List PositiveMass) (l : ℕ) :
    (pairPower (S:=S) as l).leaves=2*l+1 := by
  induction l with
  | zero => exact single_leaves_exact as
  | succ l ih => simp only [pairPower,leaves,pairClock_leaves,ih]; omega

 theorem powerClock_leaves (pre post : List PositiveMass) (l : ℕ) :
    (powerClock (S:=S) pre post l).leaves=2*l+1 := by
  induction pre with
  | nil => exact pairPower_leaves post l
  | cons a pre ih => exact ih

omit [Fintype S] [Nonempty S] in
 theorem pairPower_forkCost [Fintype S] [Nonempty S] (as : List PositiveMass) (l : ℕ) (f : ℕ → ℝ) :
    (pairPower (S:=S) as l).forkCost f=(2*l:ℕ)*f 0 := by
  induction l with
  | zero => simpa only [pairPower,Nat.mul_zero,Nat.cast_zero,zero_mul] using single_forkCost as f
  | succ l ih =>
    simp only [pairPower,forkCost,pairClock_forkCost,Nat.zero_min,ih]
    push_cast
    ring

 theorem powerClock_forkCost (pre post : List PositiveMass) (l : ℕ) (f : ℕ → ℝ) :
    (powerClock (S:=S) pre post l).forkCost f=(2*l:ℕ)*f pre.length := by
  induction pre generalizing f with
  | nil => exact pairPower_forkCost post l f
  | cons a pre ih =>
    change (powerClock pre post l).forkCost (fun j => f (1+j))=_
    rw [ih]
    simp only [List.length_cons,Nat.add_comm]

 theorem powerClock_expect {w : S → ℝ} (hw : ∀ σ,0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (pre post : List PositiveMass) {a : ℝ}
    (ho : MassOrdered a (pre++post)) (q : ℕ → ι → ℝ≥0) (P : S → S → ℝ) (l : ℕ) :
    (powerClock pre post l).expect w φ q (powerTest pre post l P) =
      prefixTest (clockSteps pre q) (gaussianHierarchy w φ (clockSteps post (fun j => q (pre.length+j))))
        (fun x => (pairMean w φ post (fun j => q (pre.length+j)) 0 P x)^l) := by
  induction pre generalizing a q with
  | nil => funext x; simpa only [powerClock,powerTest,List.length_nil,Nat.zero_add,clockSteps,prefixTest]
      using pairPower_expect hw φ post ho q P l x
  | cons b pre ih =>
    funext x
    change ((powerClock pre post l).step b).expect w φ q (powerTest pre post l P) x=_
    rw [expect_step hw φ b _ ho.2.2]
    simp only [clockSteps,prefixTest,List.length_cons]
    have hi : (fun j => q (pre.length+1+j))=(fun j => q (pre.length+j+1)) := by
      funext j; congr 1; omega
    rw [hi]
    congr 1
    · rw [prefixContinuation_hierarchy]
      congr 1
      exact clockSteps_append pre post (fun j => q (j+1))
    · exact ih ho.2.2 (fun j => q (j+1))

end SKFluctuations.Hierarchy.ClockTree

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι]

 theorem MassOrdered.suffix_end {a : ℝ} {pre post : List PositiveMass}
    (ho : MassOrdered a (pre++post)) : MassOrdered (partitionEnd a pre) post := by
  induction pre generalizing a with
  | nil => exact ho
  | cons b pre ih => exact ih ho.2.2

 def stepPowerMean (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (pre post : List (GaussianStep ι)) (P : S → S → ℝ) (l : ℕ) : (ι → ℝ) → ℝ :=
  prefixTest pre (gaussianHierarchy w φ post)
    (fun x => (gaussianHierarchyMean w φ
      (fun σ => gaussianHierarchyMean w φ (P σ) post x) post x)^l)

 def stepPowerDisorder (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (v : ι → ℝ≥0) (pre post : List (GaussianStep ι)) (P : S → S → ℝ) (l : ℕ) :
    (ι → ℝ) → ℝ :=
  zeroContinuation (Measure.pi fun i => gaussianReal 0 (v i)) (stepPowerMean w φ pre post P l)

omit [Nonempty S] in
 theorem ZeroClockRefinement.powerMean [Nonempty S] {L M A B : List (GaussianStep ι)}
    (h₁ : ZeroClockRefinement L M) (h₂ : ZeroClockRefinement A B)
    (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ) (P : S → S → ℝ) (l : ℕ) :
    stepPowerMean w φ L A P l = stepPowerMean w φ M B P l := by
  unfold stepPowerMean
  rw [(h₁.continuation_test _ _).2,(h₂.hierarchy w φ (fun _ => 0)).1]
  congr 1
  funext x
  simp_rw [(h₂.hierarchy w φ _).2]

 theorem ZeroClockRefinement.powerDisorder {L M A B : List (GaussianStep ι)}
    (h₁ : ZeroClockRefinement L M) (h₂ : ZeroClockRefinement A B)
    (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ) (v : ι → ℝ≥0) (P : S → S → ℝ) (l : ℕ) :
    stepPowerDisorder w φ v L A P l = stepPowerDisorder w φ v M B P l := by
  unfold stepPowerDisorder
  rw [h₁.powerMean h₂]

 theorem ClockTree.powerClock_expect_stepPowerMean {w : S → ℝ} (hw : ∀ σ,0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (pre post : List PositiveMass) {a : ℝ}
    (ho : MassOrdered a (pre++post)) (q : ℕ → ι → ℝ≥0) (P : S → S → ℝ) (l : ℕ) :
    (powerClock pre post l).expect w φ q (powerTest pre post l P) =
      stepPowerMean w φ (clockSteps pre q) (clockSteps post (fun j => q (pre.length+j))) P l := by
  rw [powerClock_expect hw φ pre post ho]
  unfold stepPowerMean
  congr 1
  funext x
  congr 1
  have hpost : MassOrdered (partitionEnd a pre) post := ho.suffix_end
  have hpair := congrFun (pairMean_prefix hw φ [] post hpost (fun j => q (pre.length+j)) P) x
  simpa only [List.nil_append,List.length_nil,Nat.zero_add,clockSteps,stepPairMean,prefixTest] using hpair

 theorem ClockTree.powerDisorder_coordinates {w : S → ℝ} (hw : ∀ σ,0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (pre post : List (GaussianStep ι))
    (hpre : ∀ s ∈ pre, 0<s.1) (hpost : ∀ s ∈ post, 0<s.1)
    (ho : OrderedSteps 0 (pre++post)) (v : ι → ℝ≥0) (P : S → S → ℝ) (l : ℕ) :
    let as := positiveStepMasses pre hpre
    let bs := positiveStepMasses post hpost
    let q := stepClockValues (fun i => (v i:ℝ)) (pre++post)
    (fun x => (powerClock as bs l).disorderExpect w φ (fun _ => 0) q
      (powerTest as bs l P) x) = stepPowerDisorder w φ v pre post P l := by
  dsimp only
  let as := positiveStepMasses pre hpre
  let bs := positiveStepMasses post hpost
  let q := stepClockValues (fun i => (v i:ℝ)) (pre++post)
  have hpos : ∀ s ∈ pre++post, 0<s.1 :=
    fun s hs => (List.mem_append.mp hs).elim (hpre s) (hpost s)
  have heq : positiveStepMasses (pre++post) hpos=as++bs := positiveStepMasses_append _ _ _ _
  have hordered : MassOrdered 0 (as++bs) := heq ▸ positiveStepMasses_ordered ho hpos
  have hc : clockSteps as (cumulativeIncrements (q 0) (fun j => q (j+1))) = pre ∧
      clockSteps bs (fun j => cumulativeIncrements (q 0) (fun j => q (j+1)) (as.length+j)) = post := by
    have hc := clockSteps_stepClockValues (fun i => (v i:ℝ)) (pre++post) hpos
    rw [heq,clockSteps_append] at hc
    have hq : q 0=(fun i => (v i:ℝ)) := stepClockValues_zero _ _
    rw [hq]
    apply List.append_inj hc
    rw [length_clockSteps,positiveStepMasses_length]
  funext x
  rw [disorderExpect_integral hw φ _ hordered,powerClock_expect_stepPowerMean hw φ as bs hordered,hc.1,hc.2]
  change zeroContinuation _ _ x=zeroContinuation _ _ x
  congr 2
  funext i
  simp only [stepClockValues_zero,sub_zero,Real.toNNReal_coe]

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 theorem physicalPowerMoment_eq_stepPowerDisorder (n l : ℕ)
    (pre tail : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 (pre++tail))
    (q₀ : FeatureIndex n → ℝ≥0) :
    (∫ p, ‖actualSpinPath n (pre++tail) id pre.length p‖^(2*l)
      ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ (pre++tail))=
      stepPowerDisorder (uniformWeight n) (finiteFeature n) q₀ pre tail (orderedOverlap n) l 0 := by
  have htail := ha.suffix pre tail
  have hI := physicalCutNormPower_integrable n (pre++tail) ha
    (Measure.pi fun i => gaussianReal 0 (q₀ i)) id measurable_id pre.length (2*l)
  rw [←rootedHierarchyPathLaw_eq_physical] at hI
  have := hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) (pre++tail) ha
  rw [rootedHierarchyPathLaw,Measure.integral_compProd hI]
  simp_rw [pow_mul,actualSpinPath_norm_sq_at_cut n pre tail ha]
  simp_rw [integral_actualCutField_test (uniformWeight_pos n) (finiteFeature n) pre tail ha
    ((hierarchyPairMean_smooth (uniformWeight_pos n) (finiteFeature n) (orderedOverlap n) tail htail 0).pow l)]
  unfold stepPowerDisorder zeroContinuation stepPowerMean
  simp only [zero_add]
  congr 1
  funext x
  congr 1
  funext y
  rw [hierarchyPairMean_eq_nested (uniformWeight_pos n) (finiteFeature n) (orderedOverlap n) tail htail]

end SKFluctuations

 

 

namespace SKFluctuations.Hierarchy.ClockTree
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]

 theorem powerDisorder_l1_comparison {w : S → ℝ}
    (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {pre post : List PositiveMass} (ho : MassOrdered 0 (pre++post)) (l : ℕ) (P : S → S → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hP : ∀ σ τ, |P σ τ| ≤ C)
    (v : ι → ℝ) (q K : ℕ → ι → ℝ) {a b : ℝ}
    (hp : ∀ u ∈ Ioo a b, ∀ i, Monotone (fun j => q j i+u*K j i))
    (hr : ∀ u ∈ Ioo a b, ∀ i, v i ≤ q 0 i+u*K 0 i)
    {f : ℕ → ℝ} (hf : ∀ j, 0 ≤ f j)
    (hE : ∀ j σ τ, |ReplicaTree.coordinateProfile φ K j σ τ| ≤ f j)
    (x : ι → ℝ) {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    |(powerClock pre post l).disorderExpect w φ v (fun j i => q j i+s*K j i)
        (powerTest pre post l P) x -
      (powerClock pre post l).disorderExpect w φ v (fun j i => q j i+t*K j i)
        (powerTest pre post l P) x| ≤
      errorJetVariation (2*l+1) 0 0*C^l*
        ((2*l:ℕ)*f pre.length+edgeBudget 0 (pre++post) f+f (pre++post).length)*|s-t| := by
  have h := disorderProfileJets_l1_comparison hw φ ho []
    (powerClock pre post l) (le_of_eq (powerClock_leaves pre post l))
    (powerTest pre post l P) (pow_nonneg hC l) (show 0 ≤ (1:ℝ) by norm_num)
    (powerTest_bound pre post l P hC hP) (by simp) v q K hp hr hf hE x hs ht
  simpa only [disorderProfileJets,List.length_nil,pow_zero,mul_one,powerClock_forkCost] using h

 theorem powerDisorder_cumulative_comparison {w : S → ℝ}
    (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {pre post : List PositiveMass} (ho : MassOrdered 0 (pre++post)) (l : ℕ) (P : S → S → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hP : ∀ σ τ, |P σ τ| ≤ C)
    (v : ι → ℝ) (q r : ℕ → ι → ℝ)
    (hq : ∀ i, Monotone (fun j => q j i)) (hr : ∀ i, Monotone (fun j => r j i))
    (hq₀ : ∀ i, v i ≤ q 0 i) (hr₀ : ∀ i, v i ≤ r 0 i)
    {f : ℕ → ℝ} (hf : ∀ j, 0 ≤ f j)
    (hE : ∀ j σ τ, |ReplicaTree.coordinateProfile φ (fun j i => r j i-q j i) j σ τ| ≤ f j)
    (x : ι → ℝ) :
    |(powerClock pre post l).disorderExpect w φ v q (powerTest pre post l P) x -
      (powerClock pre post l).disorderExpect w φ v r (powerTest pre post l P) x| ≤
      errorJetVariation (2*l+1) 0 0*C^l*
        ((2*l:ℕ)*f pre.length+(∫ u in (0:ℝ)..1, massStepFunction (pre++post) f u)+f (pre++post).length) := by
  have hp : ∀ u ∈ Ioo (0:ℝ) 1, ∀ i, Monotone (fun j => q j i+u*(r j i-q j i)) := by
    intro u hu i j k hjk
    have h₁ := mul_nonneg (sub_nonneg.mpr hu.2.le) (sub_nonneg.mpr (hq i hjk))
    have h₂ := mul_nonneg hu.1.le (sub_nonneg.mpr (hr i hjk))
    nlinarith
  have hv : ∀ u ∈ Ioo (0:ℝ) 1, ∀ i, v i ≤ q 0 i+u*(r 0 i-q 0 i) := by
    intro u hu i
    have h₁ := mul_nonneg (sub_nonneg.mpr hu.2.le) (sub_nonneg.mpr (hq₀ i))
    have h₂ := mul_nonneg hu.1.le (sub_nonneg.mpr (hr₀ i))
    nlinarith
  have hb := powerDisorder_l1_comparison hw φ ho l P hC hP v q
    (fun j i => r j i-q j i) hp hv hf hE x
    (show (0:ℝ) ∈ Icc 0 1 by norm_num) (show (1:ℝ) ∈ Icc 0 1 by norm_num)
  simpa only [zero_mul,one_mul,add_zero,add_sub_cancel,sub_self,zero_sub,abs_neg,abs_one,
    mul_one,edgeBudget_eq_massStepSum,massStepFunction_integral (pre++post) 0 f ho] using hb

end SKFluctuations.Hierarchy.ClockTree

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]
attribute [local instance] Classical.propDecidable

 theorem stepPowerDisorder_sameMasses {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (D : ι → ℝ) (hD : ∀ i, 0≤D i)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (q₀ r₀ : ι → ℝ≥0) (A B C E : List (GaussianStep ι))
    (hA : OrderedSteps 0 (A++B)) (hC : OrderedSteps 0 (C++E))
    (hm₁ : A.map Prod.fst=C.map Prod.fst) (hm₂ : B.map Prod.fst=E.map Prod.fst)
    (l : ℕ) (P : S → S → ℝ) {K : ℝ} (hK : 0≤K) (hP : ∀ σ τ, |P σ τ|≤K) (x : ι → ℝ) :
    |stepPowerDisorder w φ q₀ A B P l x-stepPowerDisorder w φ r₀ C E P l x| ≤
      ClockTree.errorJetVariation (2*l+1) 0 0*K^l*
        ((2*l:ℕ)*clockCoordinateDistance D (stepClockValues (fun i => (q₀ i:ℝ)) A A.length)
          (stepClockValues (fun i => (r₀ i:ℝ)) C C.length)+
         (∫ u in (0:ℝ)..1, clockCoordinateDistance D
           (stepClockFunction (fun i => (q₀ i:ℝ)) (A++B) u)
           (stepClockFunction (fun i => (r₀ i:ℝ)) (C++E) u))+
         clockCoordinateDistance D (stepClockValues (fun i => (q₀ i:ℝ)) (A++B) (A++B).length)
           (stepClockValues (fun i => (r₀ i:ℝ)) (C++E) (C++E).length)) := by
  have hpa : ∀ s ∈ A, 0<s.1 := fun s hs => hA.mem_pos s (List.mem_append_left _ hs)
  have hpb : ∀ s ∈ B, 0<s.1 := fun s hs => hA.mem_pos s (List.mem_append_right _ hs)
  have hpc : ∀ s ∈ C, 0<s.1 := fun s hs => hC.mem_pos s (List.mem_append_left _ hs)
  have hpe : ∀ s ∈ E, 0<s.1 := fun s hs => hC.mem_pos s (List.mem_append_right _ hs)
  have he₁ := positiveStepMasses_eq hpa hpc hm₁
  have he₂ := positiveStepMasses_eq hpb hpe hm₂
  have he : positiveStepMasses (A++B) hA.mem_pos=
      positiveStepMasses A hpa++positiveStepMasses B hpb := positiveStepMasses_append _ _ _ _
  have he' : positiveStepMasses (C++E) hC.mem_pos=
      positiveStepMasses A hpa++positiveStepMasses B hpb := by
    rw [positiveStepMasses_append C E hpc hpe,←he₁,←he₂]
  have hl₁ : A.length=C.length := by simpa only [List.length_map] using congrArg List.length hm₁
  have hl₂ : (A++B).length=(C++E).length := by
    simpa only [List.length_append,List.length_map] using
      congrArg List.length (show (A++B).map Prod.fst=(C++E).map Prod.fst by
        simp only [List.map_append,hm₁,hm₂])
  let as := positiveStepMasses A hpa++positiveStepMasses B hpb
  let q := stepClockValues (fun i => (q₀ i:ℝ)) (A++B)
  let r := stepClockValues (fun i => (r₀ i:ℝ)) (C++E)
  have ho : MassOrdered 0 as := by
    change MassOrdered 0 (positiveStepMasses A hpa++positiveStepMasses B hpb)
    rw [←he]
    exact positiveStepMasses_ordered hA hA.mem_pos
  have hf : ∀ j, 0≤clockCoordinateDistance D (q j) (r j) :=
    fun j => clockCoordinateDistance_nonneg _ _ _
  have henv : ∀ j σ τ, |ReplicaTree.coordinateProfile φ (fun j i => r j i-q j i) j σ τ|≤
      clockCoordinateDistance D (q j) (r j) := by
    intro j σ τ
    simpa only [clockCoordinateDistance,abs_sub_comm] using
      ReplicaTree.coordinateProfile_abs_le_sum φ (fun j i => r j i-q j i) D hD hφ j σ τ
  have hh := ClockTree.powerDisorder_cumulative_comparison hw φ ho
    l P hK hP (fun _ => 0) q r
    (stepClockValues_mono _ _) (stepClockValues_mono _ _)
    (fun i => by simp only [q,stepClockValues_zero]; exact (q₀ i).coe_nonneg)
    (fun i => by simp only [r,stepClockValues_zero]; exact (r₀ i).coe_nonneg) hf henv x
  have hmfun (u : ℝ) : massStepFunction as
      (fun j => clockCoordinateDistance D (q j) (r j)) u =
      clockCoordinateDistance D (stepClockFunction (fun i => (q₀ i:ℝ)) (A++B) u)
        (stepClockFunction (fun i => (r₀ i:ℝ)) (C++E) u) := by
    rw [massStepFunction_coordinateDistance]
    congr 1
    · funext i; change massStepFunction (positiveStepMasses A hpa++positiveStepMasses B hpb) _ u = _
      rw [←he,←stepClockFunction_eq _ hA]
    · funext i; change massStepFunction (positiveStepMasses A hpa++positiveStepMasses B hpb) _ u = _
      rw [←he',←stepClockFunction_eq _ hC]
  have hj : (positiveStepMasses A hpa).length=A.length := positiveStepMasses_length _ _
  have hlen : as.length=(A++B).length := by
    change (positiveStepMasses A hpa++positiveStepMasses B hpb).length=_
    rw [←he,positiveStepMasses_length]
  rw [congrFun (ClockTree.powerDisorder_coordinates hw φ A B hpa hpb hA q₀ P l) x] at hh
  have hrw := congrFun (ClockTree.powerDisorder_coordinates hw φ C E hpc hpe hC r₀ P l) x
  rw [←he₁,←he₂] at hrw
  rw [hrw,hj] at hh
  dsimp only [as] at hmfun hlen
  simp_rw [hmfun] at hh
  rw [hlen] at hh
  dsimp only [q,r] at hh
  rw [stepClockValues_append_cut,hl₁,stepClockValues_append_cut,hl₂] at hh
  simpa only [hl₁,hl₂] using hh

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]
attribute [local instance] Classical.propDecidable

 theorem stepPowerDisorder_l1_comparison {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (D : ι → ℝ) (hD : ∀ i, 0≤D i)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (q₀ r₀ : ι → ℝ≥0) (A B C E : List (GaussianStep ι)) {u : ℝ}
    (hu : 0≤u) (hA : OrderedSteps 0 A) (hB : OrderedSteps u B)
    (hC : OrderedSteps 0 C) (hE : OrderedSteps u E)
    (hAu : ∀ s ∈ A, s.1≤u) (hCu : ∀ s ∈ C, s.1≤u)
    (l : ℕ) (P : S → S → ℝ) {K : ℝ} (hK : 0≤K) (hP : ∀ σ τ, |P σ τ|≤K) (x : ι → ℝ) :
    |stepPowerDisorder w φ q₀ A B P l x-stepPowerDisorder w φ r₀ C E P l x| ≤
      ClockTree.errorJetVariation (2*l+1) 0 0*K^l*
        ((2*l:ℕ)*clockCoordinateDistance D (stepClockValues (fun i => (q₀ i:ℝ)) A A.length)
          (stepClockValues (fun i => (r₀ i:ℝ)) C C.length)+
         (∫ u in (0:ℝ)..1, clockCoordinateDistance D
           (stepClockFunction (fun i => (q₀ i:ℝ)) (A++B) u)
           (stepClockFunction (fun i => (r₀ i:ℝ)) (C++E) u))+
         clockCoordinateDistance D (stepClockValues (fun i => (q₀ i:ℝ)) (A++B) (A++B).length)
           (stepClockValues (fun i => (r₀ i:ℝ)) (C++E) (C++E).length)) := by
  have ho := commonClockSteps_prepost_ordered A B C E hu hA hB hC hE hAu hCu
  have hr₁ := commonClockSteps_refines A C hA.mem_pos hC.mem_pos
  have hr₂ := commonClockSteps_refines B E hB.mem_pos hE.mem_pos
  have hh := stepPowerDisorder_sameMasses hw φ D hD hφ q₀ r₀
    (leftClockSteps (commonClockSteps A C)) (leftClockSteps (commonClockSteps B E))
    (rightClockSteps (commonClockSteps A C)) (rightClockSteps (commonClockSteps B E))
    ho.1 ho.2 (commonClockSteps_same_masses A C) (commonClockSteps_same_masses B E)
    l P hK hP x
  rw [←hr₁.1.powerDisorder hr₂.1,←hr₁.2.powerDisorder hr₂.2,
    ←hr₁.1.terminal,←hr₁.2.terminal,
    ←(hr₁.1.append hr₂.1).terminal,←(hr₁.2.append hr₂.2).terminal,
    ←(hr₁.1.append hr₂.1).clockFunction,←(hr₁.2.append hr₂.2).clockFunction] at hh
  exact hh

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]
attribute [local instance] Classical.propDecidable

 def sampledPowerDisorder (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (q : ℝ → ι → ℝ≥0) (u : ℝ) (as bs : List PositiveMass) (P : S → S → ℝ) (l : ℕ) (x : ι → ℝ) : ℝ :=
    stepPowerDisorder w φ (q 0) (sampleClockSteps q 0 as) (sampleClockSteps q u bs) P l x

 theorem sampledPowerDisorder_mesh_comparison {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (D : ι → ℝ) (hD : ∀ i, 0≤D i)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (q : ℝ → ι → ℝ≥0) (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    {u : ℝ} (hu : 0≤u) (as bs cs es : List PositiveMass)
    (ha : MassOrdered 0 as) (hb : MassOrdered u bs) (hc : MassOrdered 0 cs) (he : MassOrdered u es)
    (hau : ∀ a ∈ as, a.val≤u) (hcu : ∀ c ∈ cs, c.val≤u)
    (heA : partitionEnd 0 as=u) (heC : partitionEnd 0 cs=u)
    (hetB : partitionEnd u bs=1) (hetE : partitionEnd u es=1)
    {h k : ℝ} (hmesh : PartitionMesh h 0 (as++bs)) (kmesh : PartitionMesh k 0 (cs++es))
    (l : ℕ) (P : S → S → ℝ) {K : ℝ} (hK : 0≤K) (hP : ∀ σ τ, |P σ τ|≤K) (x : ι → ℝ) :
    |sampledPowerDisorder w φ q u as bs P l x-sampledPowerDisorder w φ q u cs es P l x| ≤
      ClockTree.errorJetVariation (2*l+1) 0 0*K^l*(2*(h+k)*clockVariationBound D q) := by
  have hoa : MassOrdered 0 (as++bs) := ha.append_end (heA.symm ▸ hb)
  have hoc : MassOrdered 0 (cs++es) := hc.append_end (heC.symm ▸ he)
  have ht := stepPowerDisorder_l1_comparison hw φ D hD hφ (q 0) (q 0)
    (sampleClockSteps q 0 as) (sampleClockSteps q u bs)
    (sampleClockSteps q 0 cs) (sampleClockSteps q u es) hu
    (sampleClockSteps_ordered q as ha) (sampleClockSteps_ordered q bs hb)
    (sampleClockSteps_ordered q cs hc) (sampleClockSteps_ordered q es he)
    (sampleClockSteps_mass_le q 0 as hau) (sampleClockSteps_mass_le q 0 cs hcu) l P hK hP x
  rw [sampleClockSteps_terminal q hq 0 as ha,sampleClockSteps_terminal q hq 0 cs hc,heA,heC] at ht
  have hAB : sampleClockSteps q 0 as++sampleClockSteps q u bs=sampleClockSteps q 0 (as++bs) := by
    rw [sampleClockSteps_append,heA]
  have hCE : sampleClockSteps q 0 cs++sampleClockSteps q u es=sampleClockSteps q 0 (cs++es) := by
    rw [sampleClockSteps_append,heC]
  rw [hAB,hCE,sampleClockSteps_terminal q hq 0 (as++bs) hoa,
    sampleClockSteps_terminal q hq 0 (cs++es) hoc,
    partitionEnd_append,partitionEnd_append,heA,heC,hetB,hetE] at ht
  simp only [clockCoordinateDistance,sub_self,abs_zero,zero_mul,mul_zero,Finset.sum_const_zero,zero_add,add_zero] at ht
  simp_rw [sampleClockSteps_function q hq _ hoa,sampleClockSteps_function q hq _ hoc] at ht
  exact ht.trans (mul_le_mul_of_nonneg_left
    (sampleClock_distance_integral D q hq (as++bs) (cs++es) hoa hoc hmesh kmesh)
    (mul_nonneg (ClockTree.errorJetVariation_nonneg (2*l+1) 0 0) (pow_nonneg hK l)))

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]
attribute [local instance] Classical.propDecidable

 def retainedPowerSample (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (q : ℝ → ι → ℝ≥0) (u : PositiveMass) (as : List PositiveMass)
    (P : S → S → ℝ) (l : ℕ) (x : ι → ℝ) : ℝ :=
  sampledPowerDisorder w φ q u.val (retainedBefore u as) (retainedAfter u as) P l x

 theorem retainedPowerSample_comparison {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (D : ι → ℝ) (hD : ∀ i, 0≤D i)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (q : ℝ → ι → ℝ≥0) (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (u : PositiveMass) (hu : u.val≤1) (as bs : List PositiveMass)
    (ha : MassOrdered 0 as) (hb : MassOrdered 0 bs)
    {h k : ℝ} (hh : 0≤h) (hk : 0≤k) (hmesh : PartitionMesh h 0 as) (kmesh : PartitionMesh k 0 bs)
    (l : ℕ) (P : S → S → ℝ) {K : ℝ} (hK : 0≤K) (hP : ∀ σ τ, |P σ τ|≤K) (x : ι → ℝ) :
    |retainedPowerSample w φ q u as P l x-retainedPowerSample w φ q u bs P l x| ≤
      ClockTree.errorJetVariation (2*l+1) 0 0*K^l*(2*(h+k)*clockVariationBound D q) := by
  have h₁ := retainedMasses_ordered u hu as ha
  have h₂ := retainedMasses_ordered u hu bs hb
  exact sampledPowerDisorder_mesh_comparison hw φ D hD hφ q hq u.property.le
    _ _ _ _ h₁.1 h₁.2 h₂.1 h₂.2 (retainedBefore_bounds u as) (retainedBefore_bounds u bs)
    (retainedBefore_end u as) (retainedBefore_end u bs)
    (retainedAfter_end u as) (retainedAfter_end u bs)
    (retainedMasses_mesh u hu as ha hh hmesh) (retainedMasses_mesh u hu bs hb hk kmesh) l P hK hP x

 theorem retainedPowerSample_cauchy {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (D : ι → ℝ) (hD : ∀ i, 0≤D i)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (q : ℝ → ι → ℝ≥0) (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (u : PositiveMass) (hu : u.val≤1) (l : ℕ) (P : S → S → ℝ)
    {K : ℝ} (hK : 0≤K) (hP : ∀ σ τ, |P σ τ|≤K) (x : ι → ℝ) :
    CauchySeq (fun k => retainedPowerSample w φ q u (uniformMasses k) P l x) := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  let C := ClockTree.errorJetVariation (2*l+1) 0 0*K^l*(2*clockVariationBound D q)
  have ht : Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)⁻¹*C) atTop (𝓝 0) := by
    simpa using uniformMasses_mesh_tendsto.mul_const C
  obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds (half_pos hε)))
  refine ⟨N,fun n hn m hm => ?_⟩
  rw [Real.dist_eq]
  have hb := retainedPowerSample_comparison hw φ D hD hφ q hq u hu
    (uniformMasses n) (uniformMasses m) (uniformMasses_ordered n) (uniformMasses_ordered m)
    (by positivity) (by positivity) (uniformMasses_mesh n) (uniformMasses_mesh m) l P hK hP x
  apply hb.trans_lt
  have he : ClockTree.errorJetVariation (2*l+1) 0 0*K^l*
      (2*(((n+1:ℕ):ℝ)⁻¹+((m+1:ℕ):ℝ)⁻¹)*clockVariationBound D q)=
      ((n+1:ℕ):ℝ)⁻¹*C+((m+1:ℕ):ℝ)⁻¹*C := by dsimp [C]; ring
  rw [he]
  linarith [hN n hn,hN m hm]

 def pathPowerDisorder (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (q : ℝ → ι → ℝ≥0) (u : PositiveMass) (P : S → S → ℝ) (l : ℕ) (x : ι → ℝ) : ℝ :=
  limUnder atTop (fun k => retainedPowerSample w φ q u (uniformMasses k) P l x)

 theorem retainedPowerSample_tendsto {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (D : ι → ℝ) (hD : ∀ i, 0≤D i)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (q : ℝ → ι → ℝ≥0) (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (u : PositiveMass) (hu : u.val≤1) (l : ℕ) (P : S → S → ℝ)
    {K : ℝ} (hK : 0≤K) (hP : ∀ σ τ, |P σ τ|≤K) (x : ι → ℝ) :
    Tendsto (fun k => retainedPowerSample w φ q u (uniformMasses k) P l x) atTop
      (𝓝 (pathPowerDisorder w φ q u P l x)) :=
  (retainedPowerSample_cauchy hw φ D hD hφ q hq u hu l P hK hP x).tendsto_limUnder

end SKFluctuations.Hierarchy

end

end OAI
