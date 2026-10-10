import Mathlib
import OAI.Probability.SKFluctuations.PhysicalNearPairIntegral

namespace OAI

/-! Physical Common Cut Swap. -/

noncomputable section


namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 theorem integral_commonKernel_swap {P A : Type*}
    [MeasurableSpace P] [MeasurableSpace A] (μ : Measure P) [IsFiniteMeasure μ]
    (κ : Kernel P A) [IsMarkovKernel κ]
    {F : (P × A) × (P × A) → ℝ} (hF : Measurable F) {R : ℝ}
    (hR : ∀ z, |F z| ≤ R) :
    (∫ p : P × A, (∫ q, F (p,(p.1,q)) ∂κ p.1) ∂μ ⊗ₘ κ) =
      ∫ p : P × A, (∫ q, F ((p.1,q),p) ∂κ p.1) ∂μ ⊗ₘ κ := by
  let jl : (P × A) × A → (P × A) × (P × A) := fun z => (z.1,(z.1.1,z.2))
  let jr : (P × A) × A → (P × A) × (P × A) := fun z => ((z.1.1,z.2),z.1)
  have hjl : Measurable jl := measurable_fst.prodMk
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hjr : Measurable jr :=
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk measurable_fst
  have hl : Integrable (fun p : P × A => ∫ q, F (p,(p.1,q)) ∂κ p.1) (μ ⊗ₘ κ) := by
    apply Integrable.of_bound ((hF.comp hjl).stronglyMeasurable.integral_kernel_prod_right'
      (κ := κ.comap Prod.fst measurable_fst)).aestronglyMeasurable R
    exact Eventually.of_forall fun p =>
      (norm_integral_le_of_norm_le_const (Eventually.of_forall fun q => hR (p,(p.1,q)))).trans_eq (by simp)
  have hr : Integrable (fun p : P × A => ∫ q, F ((p.1,q),p) ∂κ p.1) (μ ⊗ₘ κ) := by
    apply Integrable.of_bound ((hF.comp hjr).stronglyMeasurable.integral_kernel_prod_right'
      (κ := κ.comap Prod.fst measurable_fst)).aestronglyMeasurable R
    exact Eventually.of_forall fun p =>
      (norm_integral_le_of_norm_le_const (Eventually.of_forall fun q => hR ((p.1,q),p))).trans_eq (by simp)
  rw [Measure.integral_compProd hl,Measure.integral_compProd hr]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro p
  have hi : Integrable (fun z : A × A => F ((p,z.1),(p,z.2))) ((κ p).prod (κ p)) :=
    Integrable.of_bound (hF.comp ((measurable_const.prodMk measurable_fst).prodMk
      (measurable_const.prodMk measurable_snd))).aestronglyMeasurable R
      (Eventually.of_forall fun z => hR ((p,z.1),(p,z.2)))
  exact integral_integral_swap (f := fun u v => F ((p,u),(p,v))) hi

variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
  [MeasurableSpace S] [StandardBorelSpace S]

 theorem integral_conditionalForkTest_swap {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (x : P → ι → ℝ) (hx : Measurable x) (k : ℕ)
    {F : (P × ForwardPath (ι → ℝ) S steps.length) ×
      (P × ForwardPath (ι → ℝ) S steps.length) → ℝ} (hF : Measurable F) {R : ℝ}
    (hR : ∀ z, |F z| ≤ R) :
    (∫ p, conditionalForkTest w φ steps x k F p
      ∂μ ⊗ₘ (hierarchyPathKernel w φ steps).comap x hx) =
    (∫ p, conditionalForkTest w φ steps x k (F ∘ Prod.swap) p
      ∂μ ⊗ₘ (hierarchyPathKernel w φ steps).comap x hx) := by
  induction steps generalizing P a k with
  | nil =>
    have := hierarchyPathKernel_markov hw φ [] ha
    cases k with
    | zero => exact integral_commonKernel_swap μ ((hierarchyPathKernel w φ []).comap x hx) hF hR
    | succ k => rfl
  | cons st tail ih =>
    have := hierarchyPathKernel_markov hw φ (st::tail) ha
    cases k with
    | zero => exact integral_commonKernel_swap μ ((hierarchyPathKernel w φ (st::tail)).comap x hx) hF hR
    | succ k =>
      rcases st with ⟨m,q⟩
      have := plantedStepKernel_markov hw φ m q tail ha
      let ν := μ ⊗ₘ (hierarchyPathKernel w φ ((m,q)::tail)).comap x hx
      let μ' := μ ⊗ₘ (plantedStepKernel w φ m q tail).comap x hx
      let x' : P × (ι → ℝ) → ι → ℝ := fun p => x p.1+p.2
      have hx' : Measurable x' := (hx.comp measurable_fst).add measurable_snd
      let e : (P × ForwardPath (ι → ℝ) S (((m,q)::tail).length)) ≃ᵐ
          ((P × (ι → ℝ)) × ForwardPath (ι → ℝ) S tail.length) := MeasurableEquiv.prodAssoc.symm
      have hmap : ν.map e = μ' ⊗ₘ (hierarchyPathKernel w φ tail).comap x' hx' :=
        hierarchyPathLaw_cons hw φ m q tail ha μ x hx
      let F' : (((P × (ι → ℝ)) × ForwardPath (ι → ℝ) S tail.length) ×
        ((P × (ι → ℝ)) × ForwardPath (ι → ℝ) S tail.length)) → ℝ :=
          F ∘ (fun z => (e.symm z.1,e.symm z.2))
      have hF' : Measurable F' := hF.comp
        ((e.symm.measurable.comp measurable_fst).prodMk (e.symm.measurable.comp measurable_snd))
      have he := ih ha.2.2.2 μ' x' hx' k hF' (fun z => hR (e.symm z.1,e.symm z.2))
      rw [← hmap] at he
      have hl := integral_map (μ := ν) e.measurable.aemeasurable
        (conditionalForkTest_measurable hw φ tail ha.2.2.2 x' hx' k hF').aestronglyMeasurable
      have hr := integral_map (μ := ν) e.measurable.aemeasurable
        (conditionalForkTest_measurable hw φ tail ha.2.2.2 x' hx' k (hF'.comp measurable_swap)).aestronglyMeasurable
      rw [hl,hr] at he
      exact he

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
  [MeasurableSpace S] [StandardBorelSpace S]

 theorem conditionalForkTest_integrable {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (x : P → ι → ℝ) (hx : Measurable x) (k : ℕ)
    {F : (P × ForwardPath (ι → ℝ) S steps.length) ×
      (P × ForwardPath (ι → ℝ) S steps.length) → ℝ} (hF : Measurable F) {R : ℝ}
    (hR : ∀ z, |F z| ≤ R) :
    Integrable (conditionalForkTest w φ steps x k F)
      (μ ⊗ₘ (hierarchyPathKernel w φ steps).comap x hx) := by
  have := hierarchyPathKernel_markov hw φ steps ha
  apply Integrable.of_bound
    (conditionalForkTest_measurable hw φ steps ha x hx k hF).aestronglyMeasurable R
  exact Eventually.of_forall fun p =>
    conditionalPathAverage_abs_le hw φ steps ha x k (fun q => hR (p,q)) p

 theorem integral_conditionalForkTest_power_swap {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (x : P → ι → ℝ) (hx : Measurable x) (k : ℕ)
    {F : (P × ForwardPath (ι → ℝ) S steps.length) ×
      (P × ForwardPath (ι → ℝ) S steps.length) → ℝ} (hF : Measurable F) {R : ℝ}
    (h0 : ∀ z, 0 ≤ F z) (hR : ∀ z, F z ≤ R) {l : ℕ} (hl : 0 < l) :
    (∫ p, (conditionalForkTest w φ steps x k F p)^l
      ∂μ ⊗ₘ (hierarchyPathKernel w φ steps).comap x hx) ≤
    (∫ p, conditionalForkTest w φ steps x k (fun z => F z.swap ^ l) p
      ∂μ ⊗ₘ (hierarchyPathKernel w φ steps).comap x hx) := by
  let ν := μ ⊗ₘ (hierarchyPathKernel w φ steps).comap x hx
  have := hierarchyPathKernel_markov hw φ steps ha
  have hpR : ∀ z, |F z ^ l| ≤ R^l := fun z => by
    rw [abs_of_nonneg (pow_nonneg (h0 z) l)]
    exact pow_le_pow_left₀ (h0 z) (hR z) l
  have hr := conditionalForkTest_integrable hw φ steps ha μ x hx k (hF.pow_const l) hpR
  have ht : Integrable (fun p => (conditionalForkTest w φ steps x k F p)^l) ν := by
    apply Integrable.of_bound
      ((conditionalForkTest_measurable hw φ steps ha x hx k hF).pow_const l).aestronglyMeasurable (R^l)
    exact Eventually.of_forall fun p => by
      rw [norm_pow,Real.norm_eq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _)
        (conditionalPathAverage_abs_le hw φ steps ha x k
          (fun q => by rw [abs_of_nonneg (h0 (p,q))]; exact hR (p,q)) p) l
  have hh : (∫ p, (conditionalForkTest w φ steps x k F p)^l ∂ν) ≤
      ∫ p, conditionalForkTest w φ steps x k (fun z => F z^l) p ∂ν := by
    apply integral_mono_ae ht hr
    exact Eventually.of_forall fun p =>
      conditionalPathAverage_power_le hw φ steps ha x k
        (hF.comp measurable_prodMk_left) (fun q => h0 (p,q)) (fun q => hR (p,q)) hl p
  exact hh.trans_eq (integral_conditionalForkTest_swap hw φ steps ha μ x hx k (hF.pow_const l) hpR)

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 theorem abs_dot_physicalFuturePairIncrement_le (n : ℕ) (V : Fin n → ℝ)
    (common tail mid pre : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a (pre++(mid++tail))) {P : Type} (x : P → FeatureIndex n → ℝ)
    (p : PhysicalPathState P n (common++(pre++(mid++tail)))) :
    |∑ i, V i*physicalFuturePairIncrement n common tail mid pre x p i| ≤
      2*projectionEuclideanNorm n V :=
  abs_dot_physicalPairIncrement_le n V tail mid pre ha id _

 theorem eventually_common_cut_observed_square_projection (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Type) [MeasurableSpace P]
      (common tail mid pre skip : List (GaussianStep (FeatureIndex n)))
      (a a₀ D : ℝ), 0 < a → 0 < D → D ≤ B →
      OrderedSteps a (pre++(mid++tail)) →
      OrderedSteps a₀ (common++((skip++pre)++(mid++tail))) →
    ∀ (μ : Measure P) [IsFiniteMeasure μ]
      (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
      (V : PhysicalPathState P n (common++((skip++pre)++(mid++tail))) → Fin n → ℝ)
      (_hV : Measurable V) (R : ℝ),
      (∀ p, projectionEuclideanNorm n (V p) ≤ R) →
      (∀ p, AlignedFieldClock (fieldProjectionDirection n (V p)) D pre) →
    (∫ p, (conditionalPathAverage (uniformWeight n) (finiteFeature n)
      (common++((skip++pre)++(mid++tail))) x common.length
      (fun q => (∑ i, V q i * physicalFuturePairIncrement n common tail mid (skip++pre) x p i)^2) p)^(k+1)
      ∂physicalPathLaw μ n (common++((skip++pre)++(mid++tail))) x hx) ≤
      (projectionLpConstant k*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*D)))^(2*k+2)*
        ∫ p, (projectionEuclideanNorm n (V p))^(2*k+2)
          ∂physicalPathLaw μ n (common++((skip++pre)++(mid++tail))) x hx := by
  filter_upwards [eventually_common_cut_projection_moment k B] with n hn
  intro P _ common tail mid pre skip a a₀ D ha hD hDB ho hs μ _ x hx V hV R hR hc
  let rest := (skip++pre)++(mid++tail)
  let Ω := PhysicalPathState P n (common++rest)
  let U : Ω → Fin n → ℝ := physicalFuturePairIncrement n common tail mid (skip++pre) x
  have hr : OrderedSteps a₀ rest := hs.suffix common rest
  have hU : Measurable U := physicalFuturePairIncrement_measurable n common tail mid (skip++pre) hr x hx
  let F : Ω × Ω → ℝ := fun z => (∑ i, V z.2 i*U z.1 i)^2
  have hF : Measurable F := by
    apply Measurable.pow_const
    apply Finset.measurable_sum
    intro i _
    exact ((measurable_pi_apply i).comp (hV.comp measurable_snd)).mul
      ((measurable_pi_apply i).comp (hU.comp measurable_fst))
  have h0 : ∀ z, 0 ≤ F z := fun z => sq_nonneg _
  have hFR : ∀ z, F z ≤ (2*R)^2 := fun z => by
    dsimp only [F]
    rw [← sq_abs]
    apply pow_le_pow_left₀ (abs_nonneg _)
    exact (abs_dot_physicalFuturePairIncrement_le n (V z.2) common tail mid (skip++pre) hr x z.1).trans
      (by linarith [hR z.2])
  have hh := integral_conditionalForkTest_power_swap (uniformWeight_pos n) (finiteFeature n)
    (common++rest) hs μ x hx common.length hF h0 hFR (Nat.succ_pos k)
  have he : (fun z : Ω × Ω => F z.swap ^ (k+1)) =
      (fun z => |∑ i, V z.1 i*U z.2 i|^(2*k+2)) := by
    funext z
    dsimp [F]
    rw [← sq_abs,← pow_mul]
    congr 1
  rw [he] at hh
  exact hh.trans (hn P common tail mid pre skip a a₀ D ha hD hDB ho hs μ x hx V hV R hR hc)

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 def physicalFutureTerminalIncrement (n : ℕ) (common tail pre : List (GaussianStep (FeatureIndex n)))
    {P : Type} (x : P → FeatureIndex n → ℝ)
    (q : PhysicalPathState P n (common++(pre++tail))) : Fin n → ℝ :=
  physicalTerminalIncrement n tail pre id
    (continuationState common (pre++tail) (x q.1) q.2)

 theorem physicalFutureTerminalIncrement_eq_spinPath (n : ℕ)
    (common tail pre : List (GaussianStep (FeatureIndex n)))
    {P : Type} (x : P → FeatureIndex n → ℝ)
    (q : PhysicalPathState P n (common++(pre++tail))) :
    WithLp.toLp 2 (physicalFutureTerminalIncrement n common tail pre x q) =
      actualSpinPath n (common++(pre++tail)) x (common.length+((pre++tail).length+1)) q -
        actualSpinPath n (common++(pre++tail)) x (common.length+pre.length) q := by
  rw [actualSpinPath_after_prefix n common (pre++tail) x ((pre++tail).length+1),
    actualSpinPath_after_prefix n common (pre++tail) x pre.length]
  exact physicalTerminalIncrement_eq_spinPath n tail pre id _

 theorem physicalFutureTerminalIncrement_measurable (n : ℕ)
    (common tail pre : List (GaussianStep (FeatureIndex n)))
    {a : ℝ} (ha : OrderedSteps a (pre++tail))
    {P : Type} [MeasurableSpace P] (x : P → FeatureIndex n → ℝ) (hx : Measurable x) :
    Measurable (physicalFutureTerminalIncrement n common tail pre x) :=
  (physicalTerminalIncrement_measurable n tail pre ha measurable_id).comp
    ((continuationState_measurable common (pre++tail)).comp
      ((hx.comp measurable_fst).prodMk measurable_snd))

 theorem physicalFutureTerminalAverage (n : ℕ) (common tail pre : List (GaussianStep (FeatureIndex n)))
    {P : Type} (x : P → FeatureIndex n → ℝ) (V : Fin n → ℝ) (l : ℕ)
    (p : PhysicalPathState P n (common++(pre++tail))) :
    conditionalPathAverage (uniformWeight n) (finiteFeature n) (common++(pre++tail))
      x common.length (fun q => (∑ i, V i*physicalFutureTerminalIncrement n common tail pre x q i)^l) p =
    ∫ q, (∑ i, V i*physicalTerminalIncrement n tail pre id
      (actualCutField common (pre++tail) (x p.1) p.2,q) i)^l
      ∂hierarchyPathKernel (uniformWeight n) (finiteFeature n) (pre++tail)
        (actualCutField common (pre++tail) (x p.1) p.2) := by
  exact conditionalPathAverage_continuation _ _ common (pre++tail) x
    (fun q => (∑ i, V i*physicalTerminalIncrement n tail pre id q i)^l) p

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 theorem eventually_common_cut_terminal_conditional_square_projection (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Type) [MeasurableSpace P]
      (common tail pre skip : List (GaussianStep (FeatureIndex n)))
      (a a₀ D : ℝ), 0 < a → 0 < D → D ≤ B →
      OrderedSteps a (pre++tail) →
      OrderedSteps a₀ (common++((skip++pre)++tail)) →
    ∀ (μ : Measure P) [IsFiniteMeasure μ]
      (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
      (V : PhysicalPathState P n (common++((skip++pre)++tail)) → Fin n → ℝ)
      (_hV : Measurable V) (R : ℝ),
      (∀ p, projectionEuclideanNorm n (V p) ≤ R) →
      (∀ p, AlignedFieldClock (fieldProjectionDirection n (V p)) D pre) →
    (∫ p, (conditionalPathAverage (uniformWeight n) (finiteFeature n)
      (common++((skip++pre)++tail)) x common.length
      (fun q => (∑ i, V p i * physicalFutureTerminalIncrement n common tail (skip++pre) x q i)^2) p)^(k+1)
      ∂physicalPathLaw μ n (common++((skip++pre)++tail)) x hx) ≤
      (projectionLpConstant k*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*D)))^(2*k+2)*
        ∫ p, (projectionEuclideanNorm n (V p))^(2*k+2)
          ∂physicalPathLaw μ n (common++((skip++pre)++tail)) x hx := by
  filter_upwards [eventually_physical_terminal_conditional_square_projection k B] with n hn
  intro P _ common tail pre skip a a₀ D ha hD hDB ho hs μ _ x hx V hV R hR hc
  let rest := (skip++pre)++tail
  let Ω := PhysicalPathState P n (common++rest)
  let ν := physicalPathLaw μ n (common++rest) x hx
  have := physicalPathLaw_finite μ n (common++rest) hs x hx
  let xc : Ω → FeatureIndex n → ℝ := fun p => actualCutField common rest (x p.1) p.2
  have hxc : Measurable xc := (actualCutField_measurable_joint common rest).comp
    ((hx.comp measurable_fst).prodMk measurable_snd)
  have hh := hn Ω tail pre skip a a₀ D ha hD hDB ho (hs.suffix common rest)
    ν V hV xc hxc R hR hc
  simp_rw [physicalFutureTerminalAverage]
  exact hh

 theorem eventually_common_cut_terminal_projection_moment (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Type) [MeasurableSpace P]
      (common tail pre skip : List (GaussianStep (FeatureIndex n)))
      (a a₀ D : ℝ), 0 < a → 0 < D → D ≤ B →
      OrderedSteps a (pre++tail) →
      OrderedSteps a₀ (common++((skip++pre)++tail)) →
    ∀ (μ : Measure P) [IsFiniteMeasure μ]
      (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
      (V : PhysicalPathState P n (common++((skip++pre)++tail)) → Fin n → ℝ)
      (_hV : Measurable V) (R : ℝ),
      (∀ p, projectionEuclideanNorm n (V p) ≤ R) →
      (∀ p, AlignedFieldClock (fieldProjectionDirection n (V p)) D pre) →
    (∫ p, conditionalPathAverage (uniformWeight n) (finiteFeature n)
      (common++((skip++pre)++tail)) x common.length
      (fun q => |∑ i, V p i * physicalFutureTerminalIncrement n common tail (skip++pre) x q i|^(2*k+2)) p
      ∂physicalPathLaw μ n (common++((skip++pre)++tail)) x hx) ≤
      (projectionLpConstant k*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*D)))^(2*k+2)*
        ∫ p, (projectionEuclideanNorm n (V p))^(2*k+2)
          ∂physicalPathLaw μ n (common++((skip++pre)++tail)) x hx := by
  filter_upwards [eventually_physical_suffix_terminal_projection k B] with n hn
  intro P _ common tail pre skip a a₀ D ha hD hDB ho hs μ _ x hx V hV R hR hc
  let rest := (skip++pre)++tail
  let Ω := PhysicalPathState P n (common++rest)
  let ν := physicalPathLaw μ n (common++rest) x hx
  have := physicalPathLaw_finite μ n (common++rest) hs x hx
  have hr : OrderedSteps a₀ rest := hs.suffix common rest
  let xc : Ω → FeatureIndex n → ℝ := fun p => actualCutField common rest (x p.1) p.2
  have hxc : Measurable xc := (actualCutField_measurable_joint common rest).comp
    ((hx.comp measurable_fst).prodMk measurable_snd)
  have hVI : Integrable (fun p => (projectionEuclideanNorm n (V p))^(2*k+2)) ν :=
    Integrable.of_bound (((projectionEuclideanNorm_measurable n).comp hV).pow_const _).aestronglyMeasurable
      (R^(2*k+2)) (Eventually.of_forall fun p => by
        rw [Real.norm_of_nonneg (pow_nonneg (show 0 ≤ projectionEuclideanNorm n (V p) from Real.sqrt_nonneg _) _)]
        exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (hR p) _)
  have hh := hn Ω tail pre skip a a₀ D ha hD hDB ho hr ν V hV xc hxc hVI hc
  let F : PhysicalPathState Ω n rest → ℝ := fun p =>
    |∑ i, V p.1 i * physicalTerminalIncrement n tail (skip++pre) xc p i|^(2*k+2)
  have hF : Measurable F := by
    apply Measurable.pow_const
    apply Measurable.abs
    apply Finset.measurable_sum
    intro i _
    exact ((measurable_pi_apply i).comp (hV.comp measurable_fst)).mul
      ((measurable_pi_apply i).comp (physicalTerminalIncrement_measurable n tail (skip++pre) hr hxc))
  have hFI : Integrable F (physicalPathLaw ν n rest xc hxc) := by
    have := physicalPathLaw_finite ν n rest hr xc hxc
    apply Integrable.of_bound hF.aestronglyMeasurable ((2*R)^(2*k+2))
    exact Eventually.of_forall fun p => by
      dsimp only [F]
      rw [Real.norm_of_nonneg (pow_nonneg (abs_nonneg _) _)]
      apply pow_le_pow_left₀ (abs_nonneg _)
      exact (abs_dot_physicalTerminalIncrement_le n (V p.1) tail (skip++pre) hr xc p).trans
        (by linarith [hR p.1])
  have := hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) rest hr
  have he : (∫ p, F p ∂physicalPathLaw ν n rest xc hxc) =
      ∫ p, (∫ q, F (p,q) ∂hierarchyPathKernel (uniformWeight n) (finiteFeature n) rest (xc p)) ∂ν :=
    Measure.integral_compProd hFI
  change (∫ p, F p ∂physicalPathLaw ν n rest xc hxc) ≤ _ at hh
  rw [he] at hh
  have hp p := conditionalPathAverage_continuation (uniformWeight n) (finiteFeature n) common rest x
    (fun q => |∑ i, V p i*physicalTerminalIncrement n tail (skip++pre) id q i|^(2*k+2)) p
  have hrewrite : ∀ p : Ω,
    conditionalPathAverage (uniformWeight n) (finiteFeature n) (common++rest) x common.length
      (fun q => |∑ i, V p i*physicalFutureTerminalIncrement n common tail (skip++pre) x q i|^(2*k+2)) p =
      ∫ q, F (p,q) ∂hierarchyPathKernel (uniformWeight n) (finiteFeature n) rest (xc p)  := hp
  change (∫ p : Ω, _ ∂ν) ≤ _
  calc
    _ = ∫ p, (∫ q, F (p,q) ∂hierarchyPathKernel (uniformWeight n) (finiteFeature n) rest (xc p)) ∂ν :=
      integral_congr_ae (Eventually.of_forall hrewrite)
    _ ≤ _ := hh

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 theorem abs_dot_physicalFutureTerminalIncrement_le (n : ℕ) (V : Fin n → ℝ)
    (common tail pre : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a (pre++tail)) {P : Type} (x : P → FeatureIndex n → ℝ)
    (p : PhysicalPathState P n (common++(pre++tail))) :
    |∑ i, V i*physicalFutureTerminalIncrement n common tail pre x p i| ≤
      2*projectionEuclideanNorm n V :=
  abs_dot_physicalTerminalIncrement_le n V tail pre ha id _

 theorem eventually_common_cut_terminal_observed_square_projection (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Type) [MeasurableSpace P]
      (common tail pre skip : List (GaussianStep (FeatureIndex n)))
      (a a₀ D : ℝ), 0 < a → 0 < D → D ≤ B →
      OrderedSteps a (pre++tail) →
      OrderedSteps a₀ (common++((skip++pre)++tail)) →
    ∀ (μ : Measure P) [IsFiniteMeasure μ]
      (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
      (V : PhysicalPathState P n (common++((skip++pre)++tail)) → Fin n → ℝ)
      (_hV : Measurable V) (R : ℝ),
      (∀ p, projectionEuclideanNorm n (V p) ≤ R) →
      (∀ p, AlignedFieldClock (fieldProjectionDirection n (V p)) D pre) →
    (∫ p, (conditionalPathAverage (uniformWeight n) (finiteFeature n)
      (common++((skip++pre)++tail)) x common.length
      (fun q => (∑ i, V q i * physicalFutureTerminalIncrement n common tail (skip++pre) x p i)^2) p)^(k+1)
      ∂physicalPathLaw μ n (common++((skip++pre)++tail)) x hx) ≤
      (projectionLpConstant k*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*D)))^(2*k+2)*
        ∫ p, (projectionEuclideanNorm n (V p))^(2*k+2)
          ∂physicalPathLaw μ n (common++((skip++pre)++tail)) x hx := by
  filter_upwards [eventually_common_cut_terminal_projection_moment k B] with n hn
  intro P _ common tail pre skip a a₀ D ha hD hDB ho hs μ _ x hx V hV R hR hc
  let rest := (skip++pre)++tail
  let Ω := PhysicalPathState P n (common++rest)
  let U : Ω → Fin n → ℝ := physicalFutureTerminalIncrement n common tail (skip++pre) x
  have hr : OrderedSteps a₀ rest := hs.suffix common rest
  have hU : Measurable U := physicalFutureTerminalIncrement_measurable n common tail (skip++pre) hr x hx
  let F : Ω × Ω → ℝ := fun z => (∑ i, V z.2 i*U z.1 i)^2
  have hF : Measurable F := by
    apply Measurable.pow_const
    apply Finset.measurable_sum
    intro i _
    exact ((measurable_pi_apply i).comp (hV.comp measurable_snd)).mul
      ((measurable_pi_apply i).comp (hU.comp measurable_fst))
  have h0 : ∀ z, 0 ≤ F z := fun z => sq_nonneg _
  have hFR : ∀ z, F z ≤ (2*R)^2 := fun z => by
    dsimp only [F]
    rw [← sq_abs]
    apply pow_le_pow_left₀ (abs_nonneg _)
    exact (abs_dot_physicalFutureTerminalIncrement_le n (V z.2) common tail (skip++pre) hr x z.1).trans
      (by linarith [hR z.2])
  have hh := integral_conditionalForkTest_power_swap (uniformWeight_pos n) (finiteFeature n)
    (common++rest) hs μ x hx common.length hF h0 hFR (Nat.succ_pos k)
  have he : (fun z : Ω × Ω => F z.swap ^ (k+1)) =
      (fun z => |∑ i, V z.1 i*U z.2 i|^(2*k+2)) := by
    funext z
    dsimp [F]
    rw [← sq_abs,← pow_mul]
    congr 1
  rw [he] at hh
  exact hh.trans (hn P common tail pre skip a a₀ D ha hD hDB ho hs μ x hx V hV R hR hc)

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators RealInnerProductSpace

 def physicalCutIncrement (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {P : Type} (x : P → FeatureIndex n → ℝ) (a b : ℕ)
    (p : PhysicalPathState P n steps) : EuclideanSpace ℝ (Fin n) :=
  actualSpinPath n steps x b p-actualSpinPath n steps x a p

 def physicalCutPairSquare (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {P : Type} (x : P → FeatureIndex n → ℝ) (c a b d e : ℕ)
    (p : PhysicalPathState P n steps) : ℝ :=
  conditionalPathAverage (uniformWeight n) (finiteFeature n) steps x c
    (fun q => (inner ℝ (physicalCutIncrement n steps x a b p)
      (physicalCutIncrement n steps x d e q))^2) p

 theorem physicalCutIncrement_measurable (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {u : ℝ} (hu : OrderedSteps u steps) {P : Type} [MeasurableSpace P]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (a b : ℕ) :
    Measurable (physicalCutIncrement n steps x a b) :=
  (actualSpinPath_measurable n steps hu x hx b).sub (actualSpinPath_measurable n steps hu x hx a)

 theorem physicalCutIncrement_norm_le (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {u : ℝ} (hu : OrderedSteps u steps) {P : Type} (x : P → FeatureIndex n → ℝ)
    (a b : ℕ) (p : PhysicalPathState P n steps) :
    ‖physicalCutIncrement n steps x a b p‖ ≤ 2 :=
  (norm_sub_le _ _).trans (by
    linarith [actualSpinPath_norm_le n steps hu x a p,actualSpinPath_norm_le n steps hu x b p])

 theorem physicalCutPairSquare_nonneg (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {P : Type} (x : P → FeatureIndex n → ℝ) (c a b d e : ℕ)
    (p : PhysicalPathState P n steps) : 0 ≤ physicalCutPairSquare n steps x c a b d e p :=
  conditionalPathAverage_nonneg _ _ _ _ _ (fun _ => sq_nonneg _) p

 theorem physicalCutPairSquare_measurable (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {u : ℝ} (hu : OrderedSteps u steps) {P : Type} [MeasurableSpace P]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (c a b d e : ℕ) :
    Measurable (physicalCutPairSquare n steps x c a b d e) := by
  let Ω := PhysicalPathState P n steps
  have hF : Measurable (fun z : Ω × Ω =>
      (inner ℝ (physicalCutIncrement n steps x a b z.1)
        (physicalCutIncrement n steps x d e z.2))^2) :=
    (((physicalCutIncrement_measurable n steps hu x hx a b).comp measurable_fst).inner
      ((physicalCutIncrement_measurable n steps hu x hx d e).comp measurable_snd)).pow_const 2
  exact conditionalForkTest_measurable (uniformWeight_pos n) (finiteFeature n) steps hu x hx c hF

 theorem physicalCutPairSquare_le (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {u : ℝ} (hu : OrderedSteps u steps) {P : Type} [MeasurableSpace P]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (c a b d e : ℕ)
    (p : PhysicalPathState P n steps) : physicalCutPairSquare n steps x c a b d e p ≤ 16 := by
  have hF : Measurable (fun q : PhysicalPathState P n steps =>
      (inner ℝ (physicalCutIncrement n steps x a b p)
        (physicalCutIncrement n steps x d e q))^2) :=
    (measurable_const.inner (physicalCutIncrement_measurable n steps hu x hx d e)).pow_const 2
  have hbound q : (inner ℝ (physicalCutIncrement n steps x a b p)
      (physicalCutIncrement n steps x d e q))^2 ≤ 16 := by
    have hinner := norm_inner_le_norm (𝕜 := ℝ)
      (physicalCutIncrement n steps x a b p) (physicalCutIncrement n steps x d e q)
    have hprod : ‖physicalCutIncrement n steps x a b p‖*‖physicalCutIncrement n steps x d e q‖ ≤ 4 := by
      have hh := mul_le_mul (physicalCutIncrement_norm_le n steps hu x a b p)
        (physicalCutIncrement_norm_le n steps hu x d e q) (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2)
      norm_num at hh ⊢
      exact hh
    rw [Real.norm_eq_abs] at hinner
    rw [← sq_abs]
    nlinarith [abs_nonneg (inner ℝ (physicalCutIncrement n steps x a b p)
      (physicalCutIncrement n steps x d e q))]
  exact (conditionalPathAverage_mono_bounded (uniformWeight_pos n) (finiteFeature n) steps hu x c
    hF measurable_const (fun q => by rw [abs_of_nonneg (sq_nonneg _)]; exact hbound q)
    (fun q => by norm_num) hbound p).trans_eq
      (conditionalPathAverage_const (uniformWeight_pos n) (finiteFeature n) steps hu x c 16 p)

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 def physicalCutMass {ι : Type} : ℝ → List (GaussianStep ι) → ℕ → ℝ
  | c, _, 0 => c
  | _, [], _+1 => 1
  | _, st::tail, k+1 => physicalCutMass st.1 tail k

 theorem physicalCutMass_mem {ι : Type} (steps : List (GaussianStep ι))
    {c : ℝ} (ho : OrderedSteps c steps) (k : ℕ) :
    0 ≤ physicalCutMass c steps k ∧ physicalCutMass c steps k ≤ 1 := by
  induction steps generalizing c k with
  | nil => cases k <;> simp_all [physicalCutMass,OrderedSteps]
  | cons st tail ih =>
    cases k with
    | zero =>
      constructor
      · exact ho.1
      · exact ho.2.1.trans (by simpa [physicalCutMass] using (ih ho.2.2.2 0).2)
    | succ k => exact ih ho.2.2.2 k

 theorem physicalCutMass_monotone {ι : Type} (steps : List (GaussianStep ι))
    {c : ℝ} (ho : OrderedSteps c steps) : Monotone (physicalCutMass c steps) := by
  apply monotone_nat_of_le_succ
  intro k
  induction steps generalizing c k with
  | nil => cases k <;> simp_all [physicalCutMass,OrderedSteps]
  | cons st tail ih =>
    cases k with
    | zero => simpa [physicalCutMass] using ho.2.1
    | succ k => exact ih ho.2.2.2 k

 def physicalRawRatio (n l : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    (c xscale : ℝ) {P : Type} [MeasurableSpace P] (μ : Measure P)
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) : ℝ :=
  max 1 ((Finset.range (steps.length+2)).sup' (by simp)
    (fun k => (∫ p, ‖actualSpinPath n steps x k p‖^(4*l)
      ∂physicalPathLaw μ n steps x hx)^((4*l:ℕ):ℝ)⁻¹ /
      Real.sqrt (xscale+physicalCutMass c steps k)))

 theorem physicalRawRatio_one_le (n l : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    (c xscale : ℝ) {P : Type} [MeasurableSpace P] (μ : Measure P)
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) :
    1 ≤ physicalRawRatio n l steps c xscale μ x hx := le_max_left _ _

 theorem physicalRawRatio_bound (n l : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {c xs : ℝ} (ho : OrderedSteps c steps) (hxs : 0 < xs)
    {P : Type} [MeasurableSpace P] (μ : Measure P)
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
    {k : ℕ} (hk : k ≤ steps.length+1) :
    (∫ p, ‖actualSpinPath n steps x k p‖^(4*l)
      ∂physicalPathLaw μ n steps x hx)^((4*l:ℕ):ℝ)⁻¹ ≤
      physicalRawRatio n l steps c xs μ x hx * Real.sqrt (xs+physicalCutMass c steps k) := by
  have hs : 0 < Real.sqrt (xs+physicalCutMass c steps k) :=
    Real.sqrt_pos.2 (add_pos_of_pos_of_nonneg hxs (physicalCutMass_mem steps ho k).1)
  let f : ℕ → ℝ := fun j =>
    (∫ p, ‖actualSpinPath n steps x j p‖^(4*l) ∂physicalPathLaw μ n steps x hx)^((4*l:ℕ):ℝ)⁻¹ /
      Real.sqrt (xs+physicalCutMass c steps j)
  have hsup : f k ≤ (Finset.range (steps.length+2)).sup' (by simp) f :=
    Finset.le_sup' f (Finset.mem_range.mpr (show k < steps.length+2 by omega))
  exact (div_le_iff₀ hs).1 (hsup.trans (le_max_right 1 _))

 theorem physicalRawRatio_moment (n l : ℕ) (hl : 0 < l)
    (steps : List (GaussianStep (FeatureIndex n))) {c xs : ℝ}
    (ho : OrderedSteps c steps) (hxs : 0 < xs)
    {P : Type} [MeasurableSpace P] (μ : Measure P)
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
    {k : ℕ} (hk : k ≤ steps.length+1) :
    (∫ p, ‖actualSpinPath n steps x k p‖^(4*l) ∂physicalPathLaw μ n steps x hx) ≤
      (physicalRawRatio n l steps c xs μ x hx)^(4*l)*(xs+physicalCutMass c steps k)^(2*l) := by
  have h0 : 0 ≤ ∫ p, ‖actualSpinPath n steps x k p‖^(4*l)
      ∂physicalPathLaw μ n steps x hx := integral_nonneg fun _ => pow_nonneg (norm_nonneg _) _
  have hM := physicalRawRatio_bound n l steps ho hxs μ x hx hk
  have hh := pow_le_pow_left₀ (Real.rpow_nonneg h0 _) hM (4*l)
  rw [Real.rpow_inv_natCast_pow h0 (by omega : 4*l ≠ 0),mul_pow] at hh
  have hs : Real.sqrt (xs+physicalCutMass c steps k)^(4*l) =
      (xs+physicalCutMass c steps k)^(2*l) := by
    rw [show 4*l = 2*(2*l) by omega,pow_mul,
      Real.sq_sqrt (add_nonneg hxs.le (physicalCutMass_mem steps ho k).1)]
  simpa only [hs] using hh

end SKFluctuations

end

end OAI
