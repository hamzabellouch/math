import Mathlib
import OAI.Probability.SKFluctuations.PhysicalTerminalPairLaw

namespace OAI

/-! Comparison Minimum Real Overlap Conclusion. -/

noncomputable section


namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 theorem comparison_minimum_retained_overlap_real_moment_normalized
    (p : ℝ) (hpower : 2 ≤ p) (Bclock : ℝ) {m δ cl cu Az κ₀ C₀ Ct D : ℝ}
    (hm₀ : 0 < m) (hδ : 0 < δ) (hδm : δ < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hκ₀ : 0 < κ₀) (hC₀ : 0 < C₀) (hCt : 0 ≤ Ct) :
    ∃ C : ℝ, 0 < C ∧
    ∀ᶠ n : ℕ in atTop, ∀ {E d r₀ u₀ : ℝ}
    (hn : 0 < n) (hE : 0 < E) (hd : 0 < d)
    (hr₀ : r₀ ∈ Icc (0:ℝ) (1/4)) (hu₀ : u₀ ∈ Icc (0:ℝ) (1/4)) (g : ℝ → ℝ),
    let N := (n:ℝ)
    let U := comparisonSmallMass N E
    let L := comparisonConstraintLength N E d
    let hN : 0 < N := by dsimp only [N]; exact_mod_cast hn
    let hU := comparisonSmallMass_pos hN hE
    let hL := comparisonConstraintLength_pos hN hE hd
    let k := comparisonFloor N δ U
    let M := comparisonCap N δ U L E d
    let c := k 1
    let hr : r₀ ≤ 1 := le_trans hr₀.2 (by norm_num)
    let hu : u₀ ∈ Icc (0:ℝ) 1 := ⟨hu₀.1,le_trans hu₀.2 (by norm_num)⟩
    let hc : 0 < c := comparisonFloor_pos hN hU (by norm_num)
    let hk := comparisonFloor_continuousOn (δ:=δ) hN hU hr₀.1
    let hkc := fun r (hri : r ∈ Icc r₀ 1) => comparisonFloor_lower_on (δ:=δ) hN hU hr₀.1 hri
    let hm := comparisonCap_monotoneOn (δ:=δ) hN hU.le hL hE hd.le
    let hM := comparisonCap_nonneg (δ:=δ) hN hU.le hL hE hd.le (show (0:ℝ) ≤ 1 by norm_num)
    ∀ (α : inverseIntegralConstraints r₀ u₀ k M)
    (hg : ContDiff ℝ 1 g)
    (hgpos : ∀ r ∈ Icc r₀ 1, 0<g r)
    (hp : ∀ r ∈ Ioc r₀ 1, comparisonLogSlope g r ∈ Icc (0:ℝ) 1)
    (b h : ℝ → ℝ)
    (hb : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      MonotoneOn (fun u => b u-omittedExtension hu.2
        (constrainedCoefficient hr hc hk hkc hm hM g hg.continuous β) u) (Icc (0:ℝ) 1))
    (hh : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      MonotoneOn (fun u => h u+omittedExtension hu.2
        (constrainedCoefficient hr hc hk hkc hm hM (fun r => g r*r)
          (hg.continuous.mul continuous_id) β) u) (Icc (0:ℝ) 1))
    (hbn : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      0 ≤ b 0-omittedExtension hu.2 (constrainedCoefficient hr hc hk hkc hm hM g hg.continuous β) 0)
    (hhn : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      0 ≤ h 0+omittedExtension hu.2 (constrainedCoefficient hr hc hk hkc hm hM (fun r => g r*r)
        (hg.continuous.mul continuous_id) β) 0)
    (hmin : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      inverseCompensatedPressure hr hu.2 hc hk hkc hm hM g hg.continuous n b h 0 α ≤
      inverseCompensatedPressure hr hu.2 hc hk hkc hm hM g hg.continuous n b h 0 β),
    let b' := fun u => (b u-omittedExtension hu.2
      (constrainedCoefficient hr hc hk hkc hm hM g hg.continuous α) u).toNNReal
    let h' := fun u => (h u+omittedExtension hu.2
      (constrainedCoefficient hr hc hk hkc hm hM (fun r => g r*r)
        (hg.continuous.mul continuous_id) α) u).toNNReal
    ∀ (u : PositiveMass) (huobs : u.val ≤ 1) (xs z : ℝ),
      0 < xs → comparisonLowerScale n E d ≤ xs → u₀ ≤ xs → r₀ ≤ U →
      z ∈ Icc r₀ 1 → z ≤ Az*xs → d ≤ D →
      Real.sqrt (n:ℝ)*E ≤ d^2 → (n:ℝ)^(-(2:ℝ)/3+m)*d ≤ C₀*E →
      (n:ℝ)*E^2 ≤ Ct*g xs*xs^2 →
      (∀ r ∈ Icc z 1, cl*r ≤ α.val.val r ∧ α.val.val r ≤ cu*r) →
      (∀ r ∈ Icc z 1, κ₀/Real.log (n:ℝ) ≤ 1-comparisonLogSlope g r) →
      MonotoneOn h (Icc u₀ 1) → (h' 1:ℝ)-(h' 0:ℝ) ≤ Bclock →
      pathPairMoment (uniformWeight n) (finiteFeature n) (completedPathClock n b' h')
        (fun σ τ => |orderedOverlap n σ τ|^p) u.val ≤ C*(xs+u.val)^p := by
  let ℓ := Nat.ceil p
  have hpℓ : p ≤ (ℓ:ℝ) := Nat.le_ceil p
  have hpk : p ≤ ((2*(ℓ+1):ℕ):ℝ) := by push_cast; have := Nat.cast_nonneg (α:=ℝ) ℓ; linarith
  obtain ⟨C,hC,hraw⟩ := comparison_minimum_retained_overlap_moment_normalized (D:=D)
    ℓ Bclock hm₀ hδ hδm hcl hcu hAz hκ₀ hC₀ hCt
  refine ⟨1+C,by linarith,?_⟩
  filter_upwards [hraw] with n hnraw
  intro E d r₀ u₀ hn hE hd hr₀ hu₀ g
  dsimp only
  intro α hg hgpos hp b h hb hh hbn hhn hmin
  let N := (n:ℝ)
  let U := comparisonSmallMass N E
  let Len := comparisonConstraintLength N E d
  have hN : 0 < N := by dsimp only [N]; exact_mod_cast hn
  have hU := comparisonSmallMass_pos hN hE
  have hLen := comparisonConstraintLength_pos hN hE hd
  let k := comparisonFloor N δ U
  let M := comparisonCap N δ U Len E d
  let c := k 1
  let hr : r₀ ≤ 1 := le_trans hr₀.2 (by norm_num)
  let hu : u₀ ≤ 1 := le_trans hu₀.2 (by norm_num)
  let hc : 0 < c := comparisonFloor_pos hN hU (by norm_num)
  let hk := comparisonFloor_continuousOn (δ:=δ) hN hU hr₀.1
  let hkc := fun r (hri : r ∈ Icc r₀ 1) => comparisonFloor_lower_on (δ:=δ) hN hU hr₀.1 hri
  let hm := comparisonCap_monotoneOn (δ:=δ) hN hU.le hLen hE hd.le
  let hM := comparisonCap_nonneg (δ:=δ) hN hU.le hLen hE hd.le (show (0:ℝ) ≤ 1 by norm_num)
  let b' := fun w => (b w-omittedExtension hu
    (constrainedCoefficient hr hc hk hkc hm hM g hg.continuous α) w).toNNReal
  let h' := fun w => (h w+omittedExtension hu
    (constrainedCoefficient hr hc hk hkc hm hM (fun r => g r*r)
      (hg.continuous.mul continuous_id) α) w).toNNReal
  intro u huobs xs z hxs hscale hu₀xs hr₀U hz hzxs hdD hupper hlower htest hreg hslow hbare hBclock
  have hb' : MonotoneOn b' (Icc (0:ℝ) 1) := by
    intro u hu v hv huv
    exact Real.toNNReal_mono (hb α hu hv huv)
  have hh' : MonotoneOn h' (Icc (0:ℝ) 1) := by
    intro u hu v hv huv
    exact Real.toNNReal_mono (hh α hu hv huv)
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hr := hnraw hn hE hd hr₀ hu₀ g α hg hgpos hp b h hb hh hbn hhn hmin
    u huobs xs z hxs hscale hu₀xs hr₀U hz hzxs hdD hupper hlower htest hreg hslow hbare hBclock
  exact pathPairMoment_rpow_from_nat (uniformWeight_pos n) (finiteFeature n)
    (completedPathClock n b' h') (completedPathClock_monotone n hb' hh')
    (fun σ τ => |orderedOverlap n σ τ|) (fun σ τ => abs_nonneg _)
    ⟨u.property,huobs⟩ (add_pos hxs u.property) (by linarith) (2*(ℓ+1)) hpk hr

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 theorem orderedOverlap_pow_gram (n k : ℕ) (σ τ : Spin n) :
    orderedOverlap n σ τ ^ k = (1/(n:ℝ))^k *
      ∑ f : Fin k → Fin n, (∏ i, spinValue (σ (f i)))*(∏ i, spinValue (τ (f i))) := by
  classical
  have he : orderedOverlap n σ τ = (1/(n:ℝ))*∑ i, spinValue (σ i)*spinValue (τ i) := by
    unfold orderedOverlap
    ring
  rw [he,mul_pow,Fintype.sum_pow]
  congr 1
  exact Finset.sum_congr rfl (fun f _ => Finset.prod_mul_distrib)

 theorem levelPairMean_overlap_pow_monotone {ι : Type*} [Fintype ι] (n k : ℕ)
    {w : Spin n → ℝ} (hw : ∀ σ, 0 < w σ) (φ : Spin n → (ι → ℝ) →L[ℝ] ℝ)
    (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps) (x : ι → ℝ) :
    Monotone (fun j => levelPairMean w φ (fun σ τ => orderedOverlap n σ τ ^ k) steps j x) := by
  classical
  have he : (fun σ τ : Spin n => orderedOverlap n σ τ ^ k) =
      fun σ τ => (1/(n:ℝ))^k * ∑ f : Fin k → Fin n,
        (∏ i, spinValue (σ (f i)))*(∏ i, spinValue (τ (f i))) := by
    funext σ τ
    exact orderedOverlap_pow_gram n k σ τ
  intro j l hjl
  change levelPairMean w φ (fun σ τ => orderedOverlap n σ τ ^ k) steps j x ≤
    levelPairMean w φ (fun σ τ => orderedOverlap n σ τ ^ k) steps l x
  rw [he,levelPairMean_const_mul hw φ _ steps ha j,levelPairMean_const_mul hw φ _ steps ha l,
    levelPairMean_sum hw φ _ steps ha j,levelPairMean_sum hw φ _ steps ha l]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun f _ =>
    levelPairMean_product_monotone hw φ (fun σ => ∏ i, spinValue (σ (f i))) steps ha x hjl)
      (by positivity)

 theorem rootLevelPairMean_overlap_even_monotone {ι : Type*} [Fintype ι] (n k : ℕ)
    {w : Spin n → ℝ} (hw : ∀ σ, 0 < w σ) (φ : Spin n → (ι → ℝ) →L[ℝ] ℝ)
    (q : ι → ℝ≥0) (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps) :
    Monotone (fun j => rootLevelPairMean w φ q
      (fun σ τ => |orderedOverlap n σ τ|^(2*k)) steps j) := by
  have he : (fun σ τ : Spin n => |orderedOverlap n σ τ|^(2*k)) =
      fun σ τ => orderedOverlap n σ τ ^ (2*k) := by
    funext σ τ
    exact (even_two_mul k).pow_abs _
  rw [he]
  intro j l hjl
  exact integral_mono
    ((levelPairMean_smooth hw φ _ steps ha j 0).integrable_zero_shift 0)
    ((levelPairMean_smooth hw φ _ steps ha l 0).integrable_zero_shift 0)
    (fun x => levelPairMean_overlap_pow_monotone n (2*k) hw φ steps ha (0+x) hjl)

 theorem physicalOverlapMoment_eq_rootLevelPairMean (n k : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q₀ : FeatureIndex n → ℝ≥0) (j : ℕ) (hj : j ≤ steps.length) :
    physicalOverlapMoment n k steps (Measure.pi fun i => gaussianReal 0 (q₀ i))
      id measurable_id j = rootLevelPairMean (uniformWeight n) (finiteFeature n) q₀
        (fun σ τ => |orderedOverlap n σ τ|^(2*k)) steps j := by
  have hsplit : steps.take j++steps.drop j=steps := List.take_append_drop ..
  have ho : OrderedSteps 0 (steps.take j++steps.drop j) := by rwa [hsplit]
  have he := physicalOverlapMoment_eq_stepPairDisorder n k (steps.take j) (steps.drop j) ho q₀
  unfold stepPairDisorder at he
  rw [stepPairMean_eq_levelPairMean (uniformWeight_pos n) (finiteFeature n)
    (fun σ τ => |orderedOverlap n σ τ|^(2*k)) _ _ (ho.suffix _ _)] at he
  simpa only [hsplit,List.length_take,min_eq_left hj,rootLevelPairMean] using he

 theorem physicalOverlapMoment_mono (n k : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q₀ : FeatureIndex n → ℝ≥0) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ steps.length) :
    physicalOverlapMoment n k steps (Measure.pi fun t => gaussianReal 0 (q₀ t))
      id measurable_id i ≤
    physicalOverlapMoment n k steps (Measure.pi fun t => gaussianReal 0 (q₀ t))
      id measurable_id j := by
  rw [physicalOverlapMoment_eq_rootLevelPairMean n k steps ha q₀ i (hij.trans hj),
    physicalOverlapMoment_eq_rootLevelPairMean n k steps ha q₀ j hj]
  exact rootLevelPairMean_overlap_even_monotone n k (uniformWeight_pos n) (finiteFeature n) q₀ steps ha hij

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 theorem physicalSpinMoment_mono (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {a : ℝ} (ha : OrderedSteps a steps) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
    {p : ℝ} (hp : 1 ≤ p) {i j : ℕ} (hij : i ≤ j) :
    (∫ z, ‖actualSpinPath n steps x i z‖^p ∂physicalPathLaw μ n steps x hx) ≤
      ∫ z, ‖actualSpinPath n steps x j z‖^p ∂physicalPathLaw μ n steps x hx := by
  have hmarkov := hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) steps ha
  let ν := physicalPathLaw μ n steps x hx
  let : IsFiniteMeasure ν := by dsimp [ν,physicalPathLaw]; infer_instance
  have hjm := actualSpinPath_measurable n steps ha x hx j
  have hint : Integrable (fun z => ‖actualSpinPath n steps x j z‖^p) ν := by
    apply Integrable.of_bound (hjm.norm.pow_const p).aestronglyMeasurable (1:ℝ)
    apply Eventually.of_forall
    intro z
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact Real.rpow_le_one (norm_nonneg _) (actualSpinPath_norm_le n steps ha x j z) (by linarith)
  have hmart := actualSpinPath_martingale n steps ha μ x hx
  have he := hmart.condExp_ae_eq hij
  have hb := integral_norm_condExp_rpow_le (μ:=ν)
    (m := (forwardFiltration P (FeatureIndex n → ℝ) (Spin n) steps.length) i) hp hint
  apply le_trans ?_ hb
  apply le_of_eq
  apply integral_congr_ae
  filter_upwards [he] with z hz
  dsimp only [ν,physicalPathLaw]
  rw [hz]

end SKFluctuations

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

 theorem prefixContinuation_merge_same_mass {F : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) {m : ℝ} (hm : m ≠ 0) (q r : ι → ℝ≥0)
    (pre : List (GaussianStep ι)) :
    prefixContinuation (pre++[(m,q),(m,r)]) F =
      prefixContinuation (pre++[(m,fun i => q i+r i)]) F := by
  rw [prefixContinuation_append,prefixContinuation_append]
  congr 1
  funext x
  exact shiftedContinuation_productGaussian_add hF hm q r x

 theorem prefixTest_merge_same_mass {F A : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hA : BddSmooth 0 A) {m : ℝ} (hm : m ≠ 0)
    (q r : ι → ℝ≥0) (pre : List (GaussianStep ι)) :
    prefixTest (pre++[(m,q),(m,r)]) F A =
      prefixTest (pre++[(m,fun i => q i+r i)]) F A := by
  rw [prefixTest_append,prefixTest_append]
  have hc := prefixContinuation_merge_same_mass hF hm q r []
  simp only [List.nil_append] at hc
  rw [hc]
  congr 1
  funext x
  exact shiftedMean_productGaussian_add hF hA hm q r x

 theorem levelPairMean_after_same_mass {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (P : S → S → ℝ)
    (pre tail : List (GaussianStep ι)) {m : ℝ} (hm : m ≠ 0)
    (q r : ι → ℝ≥0) (htail : OrderedSteps m tail) :
    levelPairMean w φ P ((pre++[(m,q),(m,r)])++tail) (pre.length+2) =
      levelPairMean w φ P ((pre++[(m,fun i => q i+r i)])++tail) (pre.length+1) := by
  have hF := (gaussianHierarchy_regular hw φ tail htail 0).1.choose_spec
  have hA := hierarchyPairMean_smooth hw φ P tail htail 0
  have he := prefixTest_merge_same_mass hF hA hm q r pre
  simpa only [←levelPairMean_prefix,List.length_append,List.length_cons,List.length_nil,
    Nat.add_zero] using he

 theorem stepPowerDisorder_after_same_mass {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (P : S → S → ℝ) (l : ℕ)
    (pre tail : List (GaussianStep ι)) {m : ℝ} (hm : m ≠ 0)
    (q r q₀ : ι → ℝ≥0) (htail : OrderedSteps m tail) :
    stepPowerDisorder w φ q₀ (pre++[(m,q),(m,r)]) tail P l =
      stepPowerDisorder w φ q₀ (pre++[(m,fun i => q i+r i)]) tail P l := by
  have hF := (gaussianHierarchy_regular hw φ tail htail 0).1.choose_spec
  have hA := (hierarchyPairMean_smooth hw φ P tail htail 0).pow l
  have he := prefixTest_merge_same_mass hF hA hm q r pre
  unfold stepPowerDisorder stepPowerMean
  have htest : (fun x => (gaussianHierarchyMean w φ
      (fun σ => gaussianHierarchyMean w φ (P σ) tail x) tail x)^l) =
      fun x => (hierarchyPairMean w φ P tail x)^l := by
    funext x
    rw [hierarchyPairMean_eq_nested hw φ P tail htail]
  rw [htest,he]

end SKFluctuations.Hierarchy
namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 theorem physicalOverlap_after_same_mass (n l : ℕ)
    (pre tail : List (GaussianStep (FeatureIndex n))) {m : ℝ} (hm : 0 < m)
    (q r q₀ : FeatureIndex n → ℝ≥0)
    (hsplit : OrderedSteps 0 ((pre++[(m,q),(m,r)])++tail))
    (hmerged : OrderedSteps 0 ((pre++[(m,fun i => q i+r i)])++tail))
    (htail : OrderedSteps m tail) :
    physicalOverlapMoment n l ((pre++[(m,q),(m,r)])++tail)
      (Measure.pi fun i => gaussianReal 0 (q₀ i)) id measurable_id (pre.length+2) =
    physicalOverlapMoment n l ((pre++[(m,fun i => q i+r i)])++tail)
      (Measure.pi fun i => gaussianReal 0 (q₀ i)) id measurable_id (pre.length+1) := by
  rw [physicalOverlapMoment_eq_rootLevelPairMean n l _ hsplit q₀ _ (by simp),
    physicalOverlapMoment_eq_rootLevelPairMean n l _ hmerged q₀ _ (by simp)]
  unfold rootLevelPairMean
  rw [levelPairMean_after_same_mass (uniformWeight_pos n) (finiteFeature n) _ pre tail hm.ne' q r htail]

 theorem physicalOverlap_intermediate_same_mass_le (n l : ℕ)
    (pre tail : List (GaussianStep (FeatureIndex n))) {m : ℝ} (hm : 0 < m)
    (q r q₀ : FeatureIndex n → ℝ≥0)
    (hsplit : OrderedSteps 0 ((pre++[(m,q),(m,r)])++tail))
    (hmerged : OrderedSteps 0 ((pre++[(m,fun i => q i+r i)])++tail))
    (htail : OrderedSteps m tail) :
    physicalOverlapMoment n l ((pre++[(m,q),(m,r)])++tail)
      (Measure.pi fun i => gaussianReal 0 (q₀ i)) id measurable_id (pre.length+1) ≤
    physicalOverlapMoment n l ((pre++[(m,fun i => q i+r i)])++tail)
      (Measure.pi fun i => gaussianReal 0 (q₀ i)) id measurable_id (pre.length+1) := by
  exact (physicalOverlapMoment_mono n l _ hsplit q₀ (by omega) (by simp)).trans_eq
    (physicalOverlap_after_same_mass n l pre tail hm q r q₀ hsplit hmerged htail)

 theorem physicalSpin_after_same_mass (n l : ℕ)
    (pre tail : List (GaussianStep (FeatureIndex n))) {m : ℝ} (hm : 0 < m)
    (q r q₀ : FeatureIndex n → ℝ≥0)
    (hsplit : OrderedSteps 0 ((pre++[(m,q),(m,r)])++tail))
    (hmerged : OrderedSteps 0 ((pre++[(m,fun i => q i+r i)])++tail))
    (htail : OrderedSteps m tail) :
    (∫ z, ‖actualSpinPath n ((pre++[(m,q),(m,r)])++tail) id (pre.length+2) z‖^(2*l)
      ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ ((pre++[(m,q),(m,r)])++tail)) =
    ∫ z, ‖actualSpinPath n ((pre++[(m,fun i => q i+r i)])++tail) id (pre.length+1) z‖^(2*l)
      ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀
        ((pre++[(m,fun i => q i+r i)])++tail) := by
  have hleft := physicalPowerMoment_eq_stepPowerDisorder n l (pre++[(m,q),(m,r)]) tail hsplit q₀
  have hright := physicalPowerMoment_eq_stepPowerDisorder n l
    (pre++[(m,fun i => q i+r i)]) tail hmerged q₀
  simp only [List.length_append,List.length_cons,List.length_nil] at hleft hright
  rw [hleft,hright,stepPowerDisorder_after_same_mass (uniformWeight_pos n) (finiteFeature n)
    (orderedOverlap n) l pre tail hm.ne' q r q₀ htail]

 theorem physicalSpin_intermediate_same_mass_le (n l : ℕ) (hl : 0 < l)
    (pre tail : List (GaussianStep (FeatureIndex n))) {m : ℝ} (hm : 0 < m)
    (q r q₀ : FeatureIndex n → ℝ≥0)
    (hsplit : OrderedSteps 0 ((pre++[(m,q),(m,r)])++tail))
    (hmerged : OrderedSteps 0 ((pre++[(m,fun i => q i+r i)])++tail))
    (htail : OrderedSteps m tail) :
    (∫ z, ‖actualSpinPath n ((pre++[(m,q),(m,r)])++tail) id (pre.length+1) z‖^(2*l)
      ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ ((pre++[(m,q),(m,r)])++tail)) ≤
    ∫ z, ‖actualSpinPath n ((pre++[(m,fun i => q i+r i)])++tail) id (pre.length+1) z‖^(2*l)
      ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀
        ((pre++[(m,fun i => q i+r i)])++tail) := by
  have hp : (1:ℝ) ≤ ((2*l:ℕ):ℝ) := by exact_mod_cast (show 1 ≤ 2*l by omega)
  have hb := physicalSpinMoment_mono n _ hsplit
    (Measure.pi fun i => gaussianReal 0 (q₀ i)) id measurable_id hp
    (show pre.length+1 ≤ pre.length+2 by omega)
  simp only [Real.rpow_natCast, ←rootedHierarchyPathLaw_eq_physical] at hb
  exact hb.trans_eq (physicalSpin_after_same_mass n l pre tail hm q r q₀ hsplit hmerged htail)

end SKFluctuations

end

end OAI
