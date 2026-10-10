import Mathlib
import OAI.Probability.SKFluctuations.ClockRetainTwo

namespace OAI

/-! Comparison Minimum Mass Center. -/

noncomputable section


namespace SKFluctuations
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

 theorem comparison_minimum_mass_center {N δ U L E d r₀ u₀ : ℝ}
    (hN : 0<N) (hU : 0<U) (hL : 0<L) (hLU : L≤U) (hE : 0<E) (hd : 0≤d)
    (hq : 2≤N^δ) (hr₀ : r₀ ∈ Icc (0:ℝ) (1/4)) (hu₀ : u₀ ∈ Icc (0:ℝ) (1/4))
    (n : ℕ) (hn : 0<n) (g : ℝ → ℝ) :
    let k := comparisonFloor N δ U
    let M := comparisonCap N δ U L E d
    let _M' := comparisonCapSlope N δ U L E d
    let c := k 1
    let hr : r₀ ≤ 1 := le_trans hr₀.2 (by norm_num)
    let hu : u₀ ∈ Icc (0:ℝ) 1 := ⟨hu₀.1,le_trans hu₀.2 (by norm_num)⟩
    let hc : 0<c := comparisonFloor_pos hN hU (by norm_num)
    let hk := comparisonFloor_continuousOn (δ:=δ) hN hU hr₀.1
    let hkc := fun r (hri : r ∈ Icc r₀ 1) => comparisonFloor_lower_on (δ:=δ) hN hU hr₀.1 hri
    let hm := comparisonCap_monotoneOn (δ:=δ) hN hU.le hL hE hd
    let hM := comparisonCap_nonneg (δ:=δ) hN hU.le hL hE hd (show (0:ℝ)≤1 by norm_num)
    ∀ (α : inverseIntegralConstraints r₀ u₀ k M)
    (hg : ContDiff ℝ 1 g)
    (_hgpos : ∀ r ∈ Icc r₀ 1, 0<g r)
    (_hp : ∀ r ∈ Ioc r₀ 1, comparisonLogSlope g r ∈ Icc (0:ℝ) 1)
    (b h : ℝ → ℝ)
    (_hb : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      MonotoneOn (fun u => b u-omittedExtension hu.2
        (constrainedCoefficient hr hc hk hkc hm hM g hg.continuous β) u) (Icc (0:ℝ) 1))
    (_hh : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      MonotoneOn (fun u => h u+omittedExtension hu.2
        (constrainedCoefficient hr hc hk hkc hm hM (fun r => g r*r)
          (hg.continuous.mul continuous_id) β) u) (Icc (0:ℝ) 1))
    (_hbn : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      0 ≤ b 0-omittedExtension hu.2 (constrainedCoefficient hr hc hk hkc hm hM g hg.continuous β) 0)
    (_hhn : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      0 ≤ h 0+omittedExtension hu.2 (constrainedCoefficient hr hc hk hkc hm hM (fun r => g r*r)
        (hg.continuous.mul continuous_id) β) 0)
    (_hmin : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      inverseCompensatedPressure hr hu.2 hc hk hkc hm hM g hg.continuous n b h 0 α ≤
      inverseCompensatedPressure hr hu.2 hc hk hkc hm hM g hg.continuous n b h 0 β),
    let b' := fun u => (b u-omittedExtension hu.2
      (constrainedCoefficient hr hc hk hkc hm hM g hg.continuous α) u).toNNReal
    let h' := fun u => (h u+omittedExtension hu.2
      (constrainedCoefficient hr hc hk hkc hm hM (fun r => g r*r)
        (hg.continuous.mul continuous_id) α) u).toNNReal
    ∀ (q t : Icc u₀ 1), u₀<q.val → N^(-δ)*U<t.val-q.val →
      orderedPathS n b' h' q.val ≤
        (constrainedQuantile hr hc hk hkc hm hM α t).val+
          (L/N^δ)*Real.log ((1+U)/U) := by
  dsimp only
  intro α hg hgpos hp b h hb hh hbn hhn hmin
  let k := comparisonFloor N δ U
  let M := comparisonCap N δ U L E d
  let c := k 1
  let hr : r₀≤1 := le_trans hr₀.2 (by norm_num)
  let hu : u₀≤1 := le_trans hu₀.2 (by norm_num)
  let hc : 0<c := comparisonFloor_pos hN hU (by norm_num)
  let hk := comparisonFloor_continuousOn (δ:=δ) hN hU hr₀.1
  let hkc := fun r (hri : r ∈ Icc r₀ 1) => comparisonFloor_lower_on (δ:=δ) hN hU hr₀.1 hri
  let hm := comparisonCap_monotoneOn (δ:=δ) hN hU.le hL hE hd
  let hM := comparisonCap_nonneg (δ:=δ) hN hU.le hL hE hd (show (0:ℝ)≤1 by norm_num)
  let b' := fun u => (b u-omittedExtension hu
    (constrainedCoefficient hr hc hk hkc hm hM g hg.continuous α) u).toNNReal
  let h' := fun u => (h u+omittedExtension hu
    (constrainedCoefficient hr hc hk hkc hm hM (fun r => g r*r)
      (hg.continuous.mul continuous_id) α) u).toNNReal
  have hbound := comparison_minimum_future_center hN hU hL hLU hE hd hq hr₀ hu₀
    n hn g α hg hgpos hp b h hb hh hbn hhn hmin
  dsimp only at hbound
  intro q t hqlo hmass
  let Q := constrainedQuantile hr hc hk hkc hm hM α
  have hqs : α.val.val (Q q)=q.val := constrainedQuantile_spec hr hc hk hkc hm hM α q
  have hts : α.val.val (Q t)=t.val := constrainedQuantile_spec hr hc hk hkc hm hM α t
  have hqr : r₀<(Q q).val := by
    by_contra hnq
    have heq : (Q q).val=r₀ := le_antisymm (le_of_not_gt hnq) (Q q).property.1
    rw [heq,α.property.1] at hqs
    linarith
  have hqt : q≤t := by
    change q.val≤t.val
    have hfloor : 0<N^(-δ)*U := mul_pos (Real.rpow_pos_of_pos hN _) hU
    linarith
  have hqrtr : (Q q).val≤(Q t).val :=
    (inverseConstraintOrderIso hr hc hk hkc hm hM α).symm.monotone hqt
  have hh := hbound (Q q) ⟨hqr,(Q q).property.2⟩ (Q t)
    ⟨hqrtr,(Q t).property.2⟩ (by rwa [hqs,hts])
  rwa [hqs] at hh

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

variable {r₀ u₀ c : ℝ} {k M : ℝ → ℝ}
variable (hr : r₀≤1) (hu : u₀≤1) (hc : 0<c) (hk : ContinuousOn k (Icc r₀ 1))
  (hkc : ∀ t ∈ Icc r₀ 1, c≤k t) (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)
  (α : inverseIntegralConstraints r₀ u₀ k M)

include hr hc hk hkc in
 theorem inverseConstraint_mass_mem {r : ℝ} (hri : r ∈ Icc r₀ 1) :
    α.val.val r ∈ Icc u₀ 1 := by
  have hmono := (inverseConstraint_strictMonoOn hc hk hkc α.property).monotoneOn
  refine ⟨?_,(α.val.property.1 r).2⟩
  have hh := hmono ⟨le_rfl,hr⟩ hri hri.1
  rwa [α.property.1] at hh

 theorem constrainedCoefficient_inverse (g : ℝ → ℝ) (hg : Continuous g)
    {r : ℝ} (hri : r ∈ Icc r₀ 1) :
    omittedExtension hu (constrainedCoefficient hr hc hk hkc hm hM g hg α) (α.val.val r)=g r := by
  let u : Icc u₀ 1 := ⟨α.val.val r,inverseConstraint_mass_mem hr hc hk hkc α hri⟩
  have heq : (constrainedQuantile hr hc hk hkc hm hM α u).val=r := by
    apply (inverseConstraint_strictMonoOn hc hk hkc α.property).injOn
      (constrainedQuantile hr hc hk hkc hm hM α u).property hri
    exact constrainedQuantile_spec hr hc hk hkc hm hM α u
  change omittedExtension hu (constrainedCoefficient hr hc hk hkc hm hM g hg α) u.val=g r
  rw [omittedExtension_on]
  change g (constrainedQuantile hr hc hk hkc hm hM α u).val=g r
  rw [heq]

 theorem changedField_radius_growth (e h₀ : ℝ → ℝ) (hec : Continuous e)
    {a b κ : ℝ} (ha : a ∈ Icc r₀ 1) (hb : b ∈ Icc r₀ 1) (hab : a≤b)
    (hh₀ : MonotoneOn h₀ (Icc u₀ 1))
    (he : ∀ t ∈ Icc a b, DifferentiableAt ℝ e t)
    (hepos : ∀ t ∈ Icc a b, 0<e t) (hem : AntitoneOn e (Icc a b))
    (hκ : 0≤κ) (hp : ∀ t ∈ Icc a b, κ≤1-comparisonLogSlope e t) :
    let h := fun u => h₀ u+omittedExtension hu
      (constrainedCoefficient hr hc hk hkc hm hM (fun r => e r*r) (hec.mul continuous_id) α) u
    κ*e b*(b-a) ≤ h (α.val.val b)-h (α.val.val a) := by
  dsimp only
  rw [constrainedCoefficient_inverse hr hu hc hk hkc hm hM α (fun r => e r*r) (hec.mul continuous_id) hb,
    constrainedCoefficient_inverse hr hu hc hk hkc hm hM α (fun r => e r*r) (hec.mul continuous_id) ha]
  have hg := radius_strength_growth hab he hepos hem hκ hp
  have hmα := (inverseConstraint_strictMonoOn hc hk hkc α.property).monotoneOn ha hb hab
  have hh := hh₀ (inverseConstraint_mass_mem hr hc hk hkc α ha)
    (inverseConstraint_mass_mem hr hc hk hkc α hb) hmα
  linarith

end SKFluctuations

 

 

namespace SKFluctuations
open Set Hierarchy
open scoped NNReal

 theorem changedField_toNNReal_radius_growth {r₀ u₀ c : ℝ} {k M : ℝ → ℝ}
    (hr : r₀≤1) (hu : u₀≤1) (hu₀ : 0≤u₀) (hc : 0<c)
    (hk : ContinuousOn k (Icc r₀ 1)) (hkc : ∀ t ∈ Icc r₀ 1, c≤k t)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)
    (α : inverseIntegralConstraints r₀ u₀ k M)
    (e h₀ : ℝ → ℝ) (hec : Continuous e)
    (hbare : MonotoneOn h₀ (Icc u₀ 1))
    (hchanged : MonotoneOn (fun u => h₀ u+omittedExtension hu
      (constrainedCoefficient hr hc hk hkc hm hM (fun r => e r*r)
        (hec.mul continuous_id) α) u) (Icc (0:ℝ) 1))
    (hzero : 0≤h₀ 0+omittedExtension hu
      (constrainedCoefficient hr hc hk hkc hm hM (fun r => e r*r)
        (hec.mul continuous_id) α) 0)
    {a b κ : ℝ} (ha : a ∈ Icc r₀ 1) (hb : b ∈ Icc r₀ 1) (hab : a≤b)
    (he : ∀ t ∈ Icc a b, DifferentiableAt ℝ e t)
    (hepos : ∀ t ∈ Icc a b, 0<e t) (hem : AntitoneOn e (Icc a b))
    (hκ : 0≤κ) (hp : ∀ t ∈ Icc a b, κ≤1-comparisonLogSlope e t) :
    let h := fun u => (h₀ u+omittedExtension hu
      (constrainedCoefficient hr hc hk hkc hm hM (fun r => e r*r)
        (hec.mul continuous_id) α) u).toNNReal
    κ*e b*(b-a) ≤ (h (α.val.val b):ℝ)-(h (α.val.val a):ℝ) := by
  dsimp only
  have hnon : ∀ r ∈ Icc r₀ 1, 0≤h₀ (α.val.val r)+omittedExtension hu
      (constrainedCoefficient hr hc hk hkc hm hM (fun r => e r*r)
        (hec.mul continuous_id) α) (α.val.val r) := by
    intro r hri
    have hur := inverseConstraint_mass_mem hr hc hk hkc α hri
    exact hzero.trans (hchanged ⟨by norm_num,by norm_num⟩
      ⟨hu₀.trans hur.1,hur.2⟩ (hu₀.trans hur.1))
  rw [Real.coe_toNNReal _ (hnon b hb),Real.coe_toNNReal _ (hnon a ha)]
  exact changedField_radius_growth hr hu hc hk hkc hm hM α e h₀ hec ha hb hab
    hbare he hepos hem hκ hp

end SKFluctuations

 

 

namespace SKFluctuations
open Set

 theorem hasDerivAt_comparisonStrength {f : ℝ → ℝ} {d lam r : ℝ}
    (hf : DifferentiableAt ℝ f (lam*r/d^3)) :
    HasDerivAt (comparisonStrength f d lam) (lam*(deriv f (lam*r/d^3)*(lam/d^3))) r := by
  change HasDerivAt (fun y : ℝ => lam*f (lam*y/d^3)) _ r
  convert
    (hf.hasDerivAt.comp r (((hasDerivAt_id r).const_mul lam).div_const (d^3))).const_mul lam using 1
  · rfl
  · simp

 theorem comparisonLogSlope_strength {f : ℝ → ℝ} {d lam r : ℝ}
    (hd : d ≠ 0) (hl : lam ≠ 0) (hf : DifferentiableAt ℝ f (lam*r/d^3))
    (hfp : f (lam*r/d^3) ≠ 0) :
    comparisonLogSlope (comparisonStrength f d lam) r=comparisonLogSlope f (lam*r/d^3) := by
  unfold comparisonLogSlope
  rw [(hasDerivAt_comparisonStrength hf).deriv]
  unfold comparisonStrength
  apply (div_eq_iff (mul_ne_zero hl hfp)).mpr
  field_simp
  rw [mul_comm r lam, mul_div_cancel_right₀ _ hfp]

 theorem strength_radial_monotonicities {e : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (he : ∀ r ∈ Icc a b, DifferentiableAt ℝ e r)
    (hp : ∀ r ∈ Icc a b, 0 < e r)
    (hs : ∀ r ∈ Icc a b, 0 ≤ comparisonLogSlope e r ∧ comparisonLogSlope e r ≤ 1) :
    AntitoneOn e (Icc a b) ∧ MonotoneOn (fun r => r*e r) (Icc a b) ∧
      MonotoneOn (fun r => e r*r^2) (Icc a b) := by
  rcases hab.eq_or_lt with rfl | _
  · simp only [Icc_self]
    exact ⟨antitoneOn_singleton _, monotoneOn_singleton _, monotoneOn_singleton _⟩
  have hder (r : ℝ) (hr : r ∈ Icc a b) : deriv e r ≤ 0 := by
    have hh := (div_nonneg_iff.mp (hs r hr).1).resolve_right (by intro hh; exact (not_le_of_gt (hp r hr)) hh.2)
    have hrp : 0 < r := ha.trans_le hr.1
    nlinarith [hh.1]
  have hanti : AntitoneOn e (Icc a b) := antitoneOn_of_deriv_nonpos (convex_Icc a b)
    (fun r hr => (he r hr).continuousAt.continuousWithinAt)
    (fun r hr => (he r (interior_subset hr)).differentiableWithinAt)
    (fun r hr => hder r (interior_subset hr))
  have hmono : MonotoneOn (fun r => r*e r) (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
      (fun r hr => (continuousAt_id.mul (he r hr).continuousAt).continuousWithinAt)
      (fun r hr => (differentiableAt_id.mul (he r (interior_subset hr))).differentiableWithinAt)
    intro r hr
    have hd := (hasDerivAt_radius_strength (he r (interior_subset hr)) (hp r (interior_subset hr)).ne')
    have heq : (fun r => r*e r)=(fun r => e r*r) := by funext r; ring
    change 0 ≤ deriv (fun r => r*e r) r
    rw [heq,hd.deriv]
    exact mul_nonneg (by linarith [(hs r (interior_subset hr)).2]) (hp r (interior_subset hr)).le
  refine ⟨hanti,hmono,?_⟩
  intro r hr s hs' hrs
  have hrr : 0 ≤ r := (ha.trans_le hr.1).le
  have hss : 0 ≤ s*e s := mul_nonneg (ha.trans_le hs'.1).le (hp s hs').le
  have hh := mul_le_mul (hmono hr hs' hrs) hrs hrr hss
  nlinarith

end SKFluctuations

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

 

def pathTailTest (pre tail : List (GaussianStep ι))
    (F : (ι → ℝ) → ForwardPath (ι → ℝ) S tail.length → ℝ)
    (x : ι → ℝ) : ForwardPath (ι → ℝ) S (pre++tail).length → ℝ :=
  match pre with
  | [] => F x
  | _::pre => fun p => pathTailTest pre tail F (x+p.1) p.2

variable [MeasurableSpace S] [StandardBorelSpace S]

omit [Fintype ι] [Fintype S] [Nonempty S] [StandardBorelSpace S] in
 theorem pathTailTest_measurable [Fintype ι] (pre tail : List (GaussianStep ι))
    {F : (ι → ℝ) → ForwardPath (ι → ℝ) S tail.length → ℝ}
    (hF : Measurable (Function.uncurry F)) :
    Measurable (Function.uncurry (pathTailTest pre tail F)) := by
  induction pre with
  | nil => exact hF
  | cons st pre ih =>
    exact ih.comp ((measurable_fst.add (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd))

omit [Fintype ι] [Fintype S] [Nonempty S] [MeasurableSpace S] [StandardBorelSpace S] in
 theorem pathTailTest_abs_le [Fintype ι] [Fintype S] [Nonempty S]
    (pre tail : List (GaussianStep ι))
    (F : (ι → ℝ) → ForwardPath (ι → ℝ) S tail.length → ℝ)
    {C : ℝ} (hC : ∀ x p, |F x p| ≤ C) (x : ι → ℝ)
    (p : ForwardPath (ι → ℝ) S (pre++tail).length) :
    |pathTailTest pre tail F x p| ≤ C := by
  induction pre generalizing x with
  | nil => exact hC x p
  | cons st pre ih => exact ih (x+p.1) p.2

 theorem pathTailTest_integrable {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (pre tail : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a (pre++tail))
    {F : (ι → ℝ) → ForwardPath (ι → ℝ) S tail.length → ℝ}
    (hF : Measurable (Function.uncurry F)) {C : ℝ} (hC : ∀ x p, |F x p| ≤ C)
    (x : ι → ℝ) :
    Integrable (pathTailTest pre tail F x) (hierarchyPathKernel w φ (pre++tail) x) := by
  have := hierarchyPathKernel_markov hw φ (pre++tail) ha
  apply Integrable.of_bound
    (((pathTailTest_measurable pre tail hF).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable) C
  exact Eventually.of_forall fun p => by
    change |pathTailTest pre tail F x p| ≤ C
    exact pathTailTest_abs_le pre tail F hC x p

 
 theorem integral_pathTailTest {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (pre tail : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a (pre++tail))
    {F : (ι → ℝ) → ForwardPath (ι → ℝ) S tail.length → ℝ}
    (hF : Measurable (Function.uncurry F)) {C : ℝ} (hC : ∀ x p, |F x p| ≤ C)
    {B : (ι → ℝ) → ℝ} (hB : BddSmooth 0 B)
    (hE : ∀ y, (∫ p, F y p ∂hierarchyPathKernel w φ tail y) = B y)
    (x : ι → ℝ) :
    (∫ p, pathTailTest pre tail F x p ∂hierarchyPathKernel w φ (pre++tail) x) =
      prefixTest pre (gaussianHierarchy w φ tail) B x := by
  induction pre generalizing a x B with
  | nil => exact hE x
  | cons st pre ih =>
    rcases st with ⟨m,q⟩
    have := plantedStepKernel_markov hw φ m q (pre++tail) ha
    have := hierarchyPathKernel_markov hw φ (pre++tail) ha.2.2.2
    have hf := pathTailTest_integrable hw φ ((m,q)::pre) tail ha hF hC x
    change Integrable (fun p : (ι → ℝ) × ForwardPath (ι → ℝ) S (pre++tail).length =>
      pathTailTest pre tail F (x+p.1) p.2)
      ((plantedStepKernel w φ m q (pre++tail) ⊗ₖ
        (hierarchyPathKernel w φ (pre++tail)).comap (fun p => p.1+p.2)
          (measurable_fst.add measurable_snd)) x) at hf
    change (∫ p : (ι → ℝ) × ForwardPath (ι → ℝ) S (pre++tail).length,
      pathTailTest pre tail F (x+p.1) p.2 ∂
      ((plantedStepKernel w φ m q (pre++tail) ⊗ₖ
        (hierarchyPathKernel w φ (pre++tail)).comap (fun p => p.1+p.2)
          (measurable_fst.add measurable_snd)) x)) = _
    rw [ProbabilityTheory.integral_compProd hf]
    simp only [Kernel.comap_apply]
    simp_rw [ih ha.2.2.2 hB hE]
    rw [plantedStepKernel_eq_tilted hw φ m q (pre++tail) ha x,
      integral_tiltedLaw (F := fun z => gaussianHierarchy w φ (pre++tail) (x+z))
        ((gaussianHierarchy_continuous hw φ (pre++tail) ha.2.2.2).comp
          (continuous_const.add continuous_id)).measurable
        (gaussianHierarchy_integrable hw φ (pre++tail) ha.2.2.2 m q x)]
    simp only [prefixTest, prefixContinuation_hierarchy, shiftedMean]

 

def pathLayerEnergy (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ) :
    (bs : List (GaussianLayer ι)) → (ι → ℝ) → (ι → ℝ) →
      ForwardPath (ι → ℝ) S (layerSteps bs).length → ℝ
  | [] => fun x v σ => (φ σ v-gaussianHierarchyMean w φ (fun σ => φ σ v) [] x)^2
  | (μ,pre)::bs => fun x v p =>
      μ*(gaussianHierarchyMean w φ (fun σ => φ σ v) (layerSteps bs)
        (actualCutField pre (layerSteps bs) x p) -
        gaussianHierarchyMean w φ (fun σ => φ σ v) (pre++layerSteps bs) x)^2 +
      pathTailTest pre (layerSteps bs) (fun y q => pathLayerEnergy w φ bs y v q) x p

 theorem pathLayerEnergy_measurable {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (bs : List (GaussianLayer ι))
    {a : ℝ} (ha : OrderedSteps a (layerSteps bs)) (v : ι → ℝ) :
    Measurable (fun p : (ι → ℝ) × ForwardPath (ι → ℝ) S (layerSteps bs).length =>
      pathLayerEnergy w φ bs p.1 v p.2) := by
  induction bs generalizing a with
  | nil =>
    exact (((measurable_of_countable (fun σ : S => φ σ v)).comp measurable_snd).sub
      ((gaussianHierarchyMean_smooth hw φ (fun σ => φ σ v) [] ha 0).continuous.measurable.comp
        measurable_fst)).pow_const 2
  | cons B bs ih =>
    rcases B with ⟨μ,pre⟩
    change OrderedSteps a (pre++layerSteps bs) at ha
    have ht := ha.suffix pre (layerSteps bs)
    have hm : Measurable (fun p : (ι → ℝ) × ForwardPath (ι → ℝ) S (pre++layerSteps bs).length =>
        gaussianHierarchyMean w φ (fun σ => φ σ v) (layerSteps bs)
          (actualCutField pre (layerSteps bs) p.1 p.2) -
        gaussianHierarchyMean w φ (fun σ => φ σ v) (pre++layerSteps bs) p.1) :=
      ((gaussianHierarchyMean_smooth hw φ (fun σ => φ σ v) (layerSteps bs)
      ht 0).continuous.measurable.comp (actualCutField_measurable_joint pre (layerSteps bs))).sub
      ((gaussianHierarchyMean_smooth hw φ (fun σ => φ σ v) (pre++layerSteps bs)
        ha 0).continuous.measurable.comp measurable_fst)
    exact ((hm.pow_const 2).const_mul μ).add
      (pathTailTest_measurable pre (layerSteps bs)
        (F := fun y q => pathLayerEnergy w φ bs y v q) (ih ht))

omit [MeasurableSpace S] [StandardBorelSpace S] in
 theorem pathLayerEnergy_bounded [MeasurableSpace S] [StandardBorelSpace S]
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (bs : List (GaussianLayer ι))
    {a : ℝ} (ha : OrderedSteps a (layerSteps bs)) (v : ι → ℝ) :
    ∃ C : ℝ, ∀ x p, |pathLayerEnergy w φ bs x v p| ≤ C := by
  classical
  let K := ∑ σ, |φ σ v|
  have hK : ∀ σ, |φ σ v| ≤ K := fun σ =>
    Finset.single_le_sum (fun τ _ => abs_nonneg (φ τ v)) (Finset.mem_univ σ)
  have hM (ss : List (GaussianStep ι)) {b : ℝ} (hb : OrderedSteps b ss) (x : ι → ℝ) :
      |gaussianHierarchyMean w φ (fun σ => φ σ v) ss x| ≤ K :=
    gaussianHierarchyMean_abs_le hw φ hK ss hb x
  have hsq {y z : ℝ} (hy : |y| ≤ K) (hz : |z| ≤ K) : |(y-z)^2| ≤ (2*K)^2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    have hd : |y-z| ≤ 2*K := (abs_sub y z).trans (by linarith)
    calc
      (y-z)^2 = |y-z|^2 := (sq_abs (y-z)).symm
      _ ≤ (2*K)^2 := pow_le_pow_left₀ (abs_nonneg _) hd 2
  induction bs generalizing a with
  | nil => exact ⟨(2*K)^2, fun x σ => hsq (hK σ) (hM [] ha x)⟩
  | cons B bs ih =>
    rcases B with ⟨μ,pre⟩
    change OrderedSteps a (pre++layerSteps bs) at ha
    have ht := ha.suffix pre (layerSteps bs)
    obtain ⟨C,hC⟩ := ih ht
    refine ⟨|μ| * (2*K)^2+C, fun x p => ?_⟩
    change |μ*(_)^2+pathTailTest pre (layerSteps bs)
      (fun y q => pathLayerEnergy w φ bs y v q) x p| ≤ _
    apply (abs_add_le _ _).trans
    apply add_le_add
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (hsq (hM (layerSteps bs) ht _) (hM (pre++layerSteps bs) ha x)) (abs_nonneg μ)
    · exact pathTailTest_abs_le pre (layerSteps bs) _ hC x p

 theorem pathLayerEnergy_integrable {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (bs : List (GaussianLayer ι))
    {a : ℝ} (ha : OrderedSteps a (layerSteps bs)) (x v : ι → ℝ) :
    Integrable (pathLayerEnergy w φ bs x v) (hierarchyPathKernel w φ (layerSteps bs) x) := by
  have := hierarchyPathKernel_markov hw φ (layerSteps bs) ha
  obtain ⟨C,hC⟩ := pathLayerEnergy_bounded hw φ bs ha v
  apply Integrable.of_bound
    (((pathLayerEnergy_measurable hw φ bs ha v).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable) C
  exact Eventually.of_forall fun p => by
    change |pathLayerEnergy w φ bs x v p| ≤ C
    exact hC x p

 theorem integral_pathLayerEnergy_nil {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (x v : ι → ℝ) :
    (∫ p, pathLayerEnergy w φ [] x v p ∂hierarchyPathKernel w φ [] x) =
      gaussianHierarchyHessian w φ [] x v v := by
  classical
  rw [show (pathLayerEnergy w φ [] x v) =
    (fun σ => (φ σ v-gaussianHierarchyMean w φ (fun σ => φ σ v) [] x)^2) from rfl]
  change (∫ σ, (φ σ v-gaussianHierarchyMean w φ (fun σ => φ σ v) [] x)^2
    ∂terminalSpinKernel w φ x) = _
  rw [integral_terminalSpinKernel hw φ]
  let c := gaussianHierarchyMean w φ (fun σ => φ σ v) [] x
  have he : (∑ σ, spinWeight w φ x σ*(φ σ v-c)^2) =
      (∑ σ, spinWeight w φ x σ*φ σ v*φ σ v) -
        2*c*(∑ σ, spinWeight w φ x σ*φ σ v)+c^2*(∑ σ, spinWeight w φ x σ) := by
    calc
      _ = ∑ σ, (spinWeight w φ x σ*φ σ v*φ σ v -
        2*c*(spinWeight w φ x σ*φ σ v)+c^2*spinWeight w φ x σ) := by
          apply Finset.sum_congr rfl
          intro σ _
          ring
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  change (∑ σ, spinWeight w φ x σ*(φ σ v-c)^2) = _
  rw [he, sum_spinWeight hw φ x]
  change (∑ σ, spinWeight w φ x σ*φ σ v*φ σ v)-2*c*c+c^2*1 =
    (∑ σ, spinWeight w φ x σ*φ σ v*φ σ v)-c*c
  ring

 

 theorem integral_pathLayerEnergy {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (bs : List (GaussianLayer ι))
    {a : ℝ} (ha : OrderedSteps a (layerSteps bs)) (x v : ι → ℝ) :
    (∫ p, pathLayerEnergy w φ bs x v p ∂hierarchyPathKernel w φ (layerSteps bs) x) =
      hierarchyLayerBound w φ bs x v := by
  induction bs generalizing a x with
  | nil => exact integral_pathLayerEnergy_nil hw φ x v
  | cons B bs ih =>
    rcases B with ⟨μ,pre⟩
    change OrderedSteps a (pre++layerSteps bs) at ha
    have ht := ha.suffix pre (layerSteps bs)
    have hM := gaussianHierarchyMean_smooth hw φ (fun σ => φ σ v) (layerSteps bs) ht 0
    let c := gaussianHierarchyMean w φ (fun σ => φ σ v) (pre++layerSteps bs) x
    have hD : BddSmooth 0 (fun y => (gaussianHierarchyMean w φ (fun σ => φ σ v)
        (layerSteps bs) y-c)^2) := by
      simpa only [pow_two] using (hM.sub (BddSmooth.const 0 c)).mul (hM.sub (BddSmooth.const 0 c))
    have hI := integrable_actualCutField_test hw φ pre (layerSteps bs) ha hD x
    obtain ⟨C,hC⟩ := pathLayerEnergy_bounded hw φ bs ht v
    have hF := pathLayerEnergy_measurable hw φ bs ht v
    have hJ := pathTailTest_integrable hw φ pre (layerSteps bs) ha
      (F := fun y q => pathLayerEnergy w φ bs y v q) hF hC x
    change (∫ p, μ*(_)^2+pathTailTest pre (layerSteps bs)
      (fun y q => pathLayerEnergy w φ bs y v q) x p
      ∂hierarchyPathKernel w φ (pre++layerSteps bs) x) = _
    rw [integral_add (hI.const_mul μ) hJ, integral_const_mul,
      ← hierarchyBlockVariance_eq_actualPath hw φ pre (layerSteps bs) ha x v,
      integral_pathTailTest hw φ pre (layerSteps bs) ha
        (F := fun y q => pathLayerEnergy w φ bs y v q) hF hC
        (hierarchyLayerBound_smooth hw φ bs ht v) (fun y => ih ht y)]
    rfl

 

 theorem gaussianHierarchyHessian_le_physical_layers {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (bs : List (GaussianLayer ι))
    {a : ℝ} (ha : OrderedSteps a (layerSteps bs))
    (hm : ∀ B ∈ bs, ∀ st ∈ B.2, st.1 ≤ B.1) (x v : ι → ℝ) :
    gaussianHierarchyHessian w φ (layerSteps bs) x v v ≤
      ∫ p, pathLayerEnergy w φ bs x v p ∂hierarchyPathKernel w φ (layerSteps bs) x := by
  rw [integral_pathLayerEnergy hw φ bs ha]
  exact gaussianHierarchyHessian_le_layers hw φ bs ha hm x v

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

 

def layerCutSchedule : List (GaussianLayer ι) → List (ℝ × ℕ)
  | [] => [(1,1)]
  | (μ,pre)::bs => (μ,pre.length)::
      (layerCutSchedule bs).map (fun c => (c.1,pre.length+c.2))

def weightedPathIncrements : List (ℝ × ℕ) → (ℕ → ℝ) → ℕ → ℝ
  | [], _, _ => 0
  | (μ,k)::cs, M, j => μ*(M k-M j)^2+weightedPathIncrements cs M k

 theorem weightedPathIncrements_shift (cs : List (ℝ × ℕ)) (M : ℕ → ℝ) (d j : ℕ) :
    weightedPathIncrements (cs.map (fun c => (c.1,d+c.2))) M (d+j) =
      weightedPathIncrements cs (fun k => M (d+k)) j := by
  induction cs generalizing j with
  | nil => rfl
  | cons c cs ih =>
    rcases c with ⟨μ,k⟩
    simp only [List.map_cons, weightedPathIncrements, ih]

 

omit [Nonempty S] in
 theorem hierarchyMeanPath_source [Nonempty S] (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (A : S → ℝ) (steps : List (GaussianStep ι)) {P : Type}
    (x : P → ι → ℝ) (k : ℕ) (p : P) (q : ForwardPath (ι → ℝ) S steps.length) :
    hierarchyMeanPath w φ A steps x k (p,q) =
      hierarchyMeanPath w φ A steps (fun _ : Unit => x p) k ((),q) := by
  induction steps generalizing P k with
  | nil => cases k <;> rfl
  | cons st steps ih =>
    cases k with
    | zero => rfl
    | succ k =>
      change hierarchyMeanPath w φ A steps (fun r : P × (ι → ℝ) => x r.1+r.2)
        k ((p,q.1),q.2) =
        hierarchyMeanPath w φ A steps (fun r : Unit × (ι → ℝ) => x p+r.2)
        k (((),q.1),q.2)
      exact (ih (fun r : P × (ι → ℝ) => x r.1+r.2) k (p,q.1) q.2).trans
        (ih (fun r : Unit × (ι → ℝ) => x p+r.2) k ((),q.1) q.2).symm

 theorem pathTailTest_meanPath (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (A : S → ℝ) (pre tail : List (GaussianStep ι)) (x : ι → ℝ) (k : ℕ)
    (p : ForwardPath (ι → ℝ) S (pre++tail).length) :
    pathTailTest pre tail (fun y q =>
      hierarchyMeanPath w φ A tail (fun _ : Unit => y) k ((),q)) x p =
    hierarchyMeanPath w φ A (pre++tail) (fun _ : Unit => x) (pre.length+k) ((),p) := by
  induction pre generalizing x with
  | nil => simp only [pathTailTest, List.nil_append, List.length_nil, Nat.zero_add]
  | cons st pre ih =>
    simp only [pathTailTest, List.cons_append, List.length_cons, Nat.succ_add,
      hierarchyMeanPath]
    rw [ih]
    exact (hierarchyMeanPath_source w φ A (pre++tail)
      (fun q : Unit × (ι → ℝ) => x+q.2) (pre.length+k) ((),p.1) p.2).symm

omit [Fintype ι] [Fintype S] [Nonempty S] in
 theorem pathTailTest_weightedPathIncrements [Fintype ι] [Fintype S] [Nonempty S]
    (pre tail : List (GaussianStep ι))
    (M : (ι → ℝ) → ForwardPath (ι → ℝ) S tail.length → ℕ → ℝ)
    (x : ι → ℝ) (p : ForwardPath (ι → ℝ) S (pre++tail).length)
    (cs : List (ℝ × ℕ)) (j : ℕ) :
    pathTailTest pre tail (fun y q => weightedPathIncrements cs (M y q) j) x p =
      weightedPathIncrements cs (fun k => pathTailTest pre tail (fun y q => M y q k) x p) j := by
  induction pre generalizing x with
  | nil => rfl
  | cons st pre ih => exact ih (x+p.1) p.2

 

 theorem pathLayerEnergy_eq_weightedPathIncrements (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (bs : List (GaussianLayer ι)) (x v : ι → ℝ)
    (p : ForwardPath (ι → ℝ) S (layerSteps bs).length) :
    pathLayerEnergy w φ bs x v p =
      weightedPathIncrements (layerCutSchedule bs)
        (fun k => hierarchyMeanPath w φ (fun σ => φ σ v) (layerSteps bs)
          (fun _ : Unit => x) k ((),p)) 0 := by
  induction bs generalizing x with
  | nil =>
    change ((φ p) v-gaussianHierarchyMean w φ (fun σ => φ σ v) [] x)^2 =
      1*((φ p) v-gaussianHierarchyMean w φ (fun σ => φ σ v) [] x)^2+0
    ring
  | cons B bs ih =>
    rcases B with ⟨μ,pre⟩
    change ForwardPath (ι → ℝ) S (pre++layerSteps bs).length at p
    change μ*(gaussianHierarchyMean w φ (fun σ => φ σ v) (layerSteps bs)
        (actualCutField pre (layerSteps bs) x p)-
      gaussianHierarchyMean w φ (fun σ => φ σ v) (pre++layerSteps bs) x)^2 +
      pathTailTest pre (layerSteps bs) (fun y q => pathLayerEnergy w φ bs y v q) x p =
      μ*(hierarchyMeanPath w φ (fun σ => φ σ v) (pre++layerSteps bs)
          (fun _ : Unit => x) pre.length ((),p)-
        hierarchyMeanPath w φ (fun σ => φ σ v) (pre++layerSteps bs)
          (fun _ : Unit => x) 0 ((),p))^2 +
      weightedPathIncrements ((layerCutSchedule bs).map (fun c => (c.1,pre.length+c.2)))
        (fun k => hierarchyMeanPath w φ (fun σ => φ σ v) (pre++layerSteps bs)
          (fun _ : Unit => x) k ((),p)) pre.length
    congr 1
    · rw [hierarchyMeanPath_at_cut, hierarchyMeanPath_zero]
    · simp_rw [ih]
      rw [pathTailTest_weightedPathIncrements pre (layerSteps bs)
        (fun y q k => hierarchyMeanPath w φ (fun σ => φ σ v) (layerSteps bs)
          (fun _ : Unit => y) k ((),q)) x p]
      simp_rw [pathTailTest_meanPath]
      exact (weightedPathIncrements_shift (layerCutSchedule bs)
        (fun k => hierarchyMeanPath w φ (fun σ => φ σ v) (pre++layerSteps bs)
          (fun _ : Unit => x) k ((),p)) pre.length 0).symm

end SKFluctuations.Hierarchy

end

end OAI
