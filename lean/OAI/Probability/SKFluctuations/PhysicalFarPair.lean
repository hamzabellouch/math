import Mathlib
import OAI.Probability.SKFluctuations.PhysicalSusceptibility
import OAI.Probability.SKFluctuations.RadiusGridCount

namespace OAI

/-! Physical Far Pair. -/

noncomputable section


namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal ENNReal BigOperators

 theorem dot_physicalPairIncrement {P : Type} (n : ℕ) (V : Fin n → ℝ)
    (tail mid pre : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a (pre++(mid++tail))) (x : P → FeatureIndex n → ℝ)
    (p : PhysicalPathState P n (pre++(mid++tail))) :
    (∑ i, V i*physicalPairIncrement n tail mid pre x p i) =
      gaussianHierarchyMean (uniformWeight n) (finiteFeature n) (spinProjection n V) tail
        (actualPairCut pre mid tail (x p.1) p.2).2 -
      gaussianHierarchyMean (uniformWeight n) (finiteFeature n) (spinProjection n V) (mid++tail)
        (actualPairCut pre mid tail (x p.1) p.2).1 := by
  simp only [physicalPairIncrement,Pi.sub_apply,mul_sub,Finset.sum_sub_distrib,
    spinProjection_actualSpinMean n V tail ((ha.suffix pre _).suffix mid tail),
    spinProjection_actualSpinMean n V (mid++tail) (ha.suffix pre _)]

 theorem abs_dot_physicalPairIncrement_le {P : Type} (n : ℕ) (V : Fin n → ℝ)
    (tail mid pre : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a (pre++(mid++tail))) (x : P → FeatureIndex n → ℝ)
    (p : PhysicalPathState P n (pre++(mid++tail))) :
    |∑ i, V i*physicalPairIncrement n tail mid pre x p i| ≤ 2*projectionEuclideanNorm n V := by
  rw [dot_physicalPairIncrement n V tail mid pre ha x p]
  have h1 := gaussianHierarchyMean_abs_le (uniformWeight_pos n) (finiteFeature n)
    (spinProjection_abs_le n V) tail ((ha.suffix pre _).suffix mid tail)
    (actualPairCut pre mid tail (x p.1) p.2).2
  have h0 := gaussianHierarchyMean_abs_le (uniformWeight_pos n) (finiteFeature n)
    (spinProjection_abs_le n V) (mid++tail) (ha.suffix pre _)
    (actualPairCut pre mid tail (x p.1) p.2).1
  exact (abs_sub _ _).trans (by linarith)

 theorem physicalPairConditionalSquare_power_le {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (n k : ℕ)
    (tail mid pre : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a (pre++(mid++tail)))
    (V : P → Fin n → ℝ) (hV : Measurable V)
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
    {R : ℝ} (hR : ∀ p, projectionEuclideanNorm n (V p) ≤ R) :
    (∫ p, (∫ q, (∑ i, V p i * physicalPairIncrement n tail mid pre x (p,q) i)^2
      ∂hierarchyPathKernel (uniformWeight n) (finiteFeature n) (pre++(mid++tail)) (x p))^(k+1) ∂μ) ≤
    ∫ p, |∑ i, V p.1 i * physicalPairIncrement n tail mid pre x p i|^(2*k+2)
      ∂physicalPathLaw μ n (pre++(mid++tail)) x hx := by
  have := hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) (pre++(mid++tail)) ha
  let κ := (hierarchyPathKernel (uniformWeight n) (finiteFeature n) (pre++(mid++tail))).comap x hx
  let F : PhysicalPathState P n (pre++(mid++tail)) → ℝ :=
    fun p => (∑ i, V p.1 i * physicalPairIncrement n tail mid pre x p i)^2
  have hF : Measurable F := by
    apply Measurable.pow_const
    apply Finset.measurable_sum
    intro i _
    exact ((measurable_pi_apply i).comp (hV.comp measurable_fst)).mul
      ((measurable_pi_apply i).comp (physicalPairIncrement_measurable n tail mid pre ha hx))
  have hFR : ∀ z, F z ≤ (2*R)^2 := by
    intro z
    dsimp [F]
    rw [← sq_abs]
    apply pow_le_pow_left₀ (abs_nonneg _)
    exact (abs_dot_physicalPairIncrement_le n (V z.1) tail mid pre ha x z).trans
      (by linarith [hR z.1])
  have H := bounded_kernel_power_le μ κ hF (fun z => sq_nonneg _) hFR (Nat.succ_pos k)
  change _ ≤ ∫ p, _ ∂μ ⊗ₘ κ
  change (∫ p, (∫ q, F (p,q) ∂κ p)^(k+1) ∂μ) ≤ _
  convert H using 1
  congr 1
  funext p
  dsimp [F]
  rw [← sq_abs,← pow_mul]
  congr 1

 theorem eventually_physical_conditional_square_projection (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Type) [MeasurableSpace P]
      (tail mid pre skip : List (GaussianStep (FeatureIndex n)))
      (a a₀ D : ℝ), 0 < a → 0 < D → D ≤ B →
      OrderedSteps a (pre++(mid++tail)) →
      OrderedSteps a₀ ((skip++pre)++(mid++tail)) →
    ∀ (μ : Measure P) [IsFiniteMeasure μ] (V : P → Fin n → ℝ) (_hV : Measurable V)
      (x : P → FeatureIndex n → ℝ) (_hx : Measurable x) (R : ℝ),
      (∀ p, projectionEuclideanNorm n (V p) ≤ R) →
      (∀ p, AlignedFieldClock (fieldProjectionDirection n (V p)) D pre) →
    (∫ p, (∫ q, (∑ i, V p i * physicalPairIncrement n tail mid (skip++pre) x (p,q) i)^2
      ∂hierarchyPathKernel (uniformWeight n) (finiteFeature n)
        ((skip++pre)++(mid++tail)) (x p))^(k+1) ∂μ) ≤
      (projectionLpConstant k*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*D)))^(2*k+2)*
        ∫ p, (projectionEuclideanNorm n (V p))^(2*k+2) ∂μ := by
  filter_upwards [eventually_physical_suffix_random_projection k B] with n hn
  intro P _ tail mid pre skip a a₀ D ha hD hDB ho hs μ _ V hV x hx R hR hc
  have hI : Integrable (fun p => (projectionEuclideanNorm n (V p))^(2*k+2)) μ := by
    apply Integrable.of_bound (((projectionEuclideanNorm_measurable n).comp hV).pow_const _).aestronglyMeasurable
      (R^(2*k+2))
    exact Eventually.of_forall fun p => by
      have hv0 : 0 ≤ projectionEuclideanNorm n (V p) := Real.sqrt_nonneg _
      change ‖(projectionEuclideanNorm n (V p))^(2*k+2)‖ ≤ _
      rw [Real.norm_of_nonneg (pow_nonneg hv0 _)]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (hR p) _
  exact (physicalPairConditionalSquare_power_le μ n k tail mid (skip++pre) hs V hV x hx hR).trans
    (hn P tail mid pre skip a a₀ D ha hD hDB ho hs μ V hV x hx hI hc)

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal ENNReal BigOperators

 theorem abs_dot_physicalTerminalIncrement_le {P : Type} (n : ℕ) (V : Fin n → ℝ)
    (tail pre : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a (pre++tail)) (x : P → FeatureIndex n → ℝ)
    (p : PhysicalPathState P n (pre++tail)) :
    |∑ i, V i*physicalTerminalIncrement n tail pre x p i| ≤ 2*projectionEuclideanNorm n V := by
  rw [dot_physicalTerminalIncrement n V tail pre ha x p]
  have h1 := spinProjection_abs_le n V (ForwardPath.spin (pre++tail).length p.2)
  have h0 := gaussianHierarchyMean_abs_le (uniformWeight_pos n) (finiteFeature n)
    (spinProjection_abs_le n V) tail (ha.suffix pre tail)
    (actualCutField pre tail (x p.1) p.2)
  exact (abs_sub _ _).trans (by linarith)

 theorem physicalTerminalConditionalSquare_power_le {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (n k : ℕ)
    (tail pre : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a (pre++tail))
    (V : P → Fin n → ℝ) (hV : Measurable V)
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
    {R : ℝ} (hR : ∀ p, projectionEuclideanNorm n (V p) ≤ R) :
    (∫ p, (∫ q, (∑ i, V p i * physicalTerminalIncrement n tail pre x (p,q) i)^2
      ∂hierarchyPathKernel (uniformWeight n) (finiteFeature n) (pre++tail) (x p))^(k+1) ∂μ) ≤
    ∫ p, |∑ i, V p.1 i * physicalTerminalIncrement n tail pre x p i|^(2*k+2)
      ∂physicalPathLaw μ n (pre++tail) x hx := by
  have := hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) (pre++tail) ha
  let κ := (hierarchyPathKernel (uniformWeight n) (finiteFeature n) (pre++tail)).comap x hx
  let F : PhysicalPathState P n (pre++tail) → ℝ :=
    fun p => (∑ i, V p.1 i * physicalTerminalIncrement n tail pre x p i)^2
  have hF : Measurable F := by
    apply Measurable.pow_const
    apply Finset.measurable_sum
    intro i _
    exact ((measurable_pi_apply i).comp (hV.comp measurable_fst)).mul
      ((measurable_pi_apply i).comp (physicalTerminalIncrement_measurable n tail pre ha hx))
  have hFR : ∀ z, F z ≤ (2*R)^2 := by
    intro z
    dsimp [F]
    rw [← sq_abs]
    apply pow_le_pow_left₀ (abs_nonneg _)
    exact (abs_dot_physicalTerminalIncrement_le n (V z.1) tail pre ha x z).trans
      (by linarith [hR z.1])
  have H := bounded_kernel_power_le μ κ hF (fun z => sq_nonneg _) hFR (Nat.succ_pos k)
  change _ ≤ ∫ p, _ ∂μ ⊗ₘ κ
  change (∫ p, (∫ q, F (p,q) ∂κ p)^(k+1) ∂μ) ≤ _
  convert H using 1
  congr 1
  funext p
  dsimp [F]
  rw [← sq_abs,← pow_mul]
  congr 1

 theorem eventually_physical_terminal_conditional_square_projection (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Type) [MeasurableSpace P]
      (tail pre skip : List (GaussianStep (FeatureIndex n)))
      (a a₀ D : ℝ), 0 < a → 0 < D → D ≤ B →
      OrderedSteps a (pre++tail) →
      OrderedSteps a₀ ((skip++pre)++tail) →
    ∀ (μ : Measure P) [IsFiniteMeasure μ] (V : P → Fin n → ℝ) (_hV : Measurable V)
      (x : P → FeatureIndex n → ℝ) (_hx : Measurable x) (R : ℝ),
      (∀ p, projectionEuclideanNorm n (V p) ≤ R) →
      (∀ p, AlignedFieldClock (fieldProjectionDirection n (V p)) D pre) →
    (∫ p, (∫ q, (∑ i, V p i * physicalTerminalIncrement n tail (skip++pre) x (p,q) i)^2
      ∂hierarchyPathKernel (uniformWeight n) (finiteFeature n)
        ((skip++pre)++tail) (x p))^(k+1) ∂μ) ≤
      (projectionLpConstant k*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*D)))^(2*k+2)*
        ∫ p, (projectionEuclideanNorm n (V p))^(2*k+2) ∂μ := by
  filter_upwards [eventually_physical_suffix_terminal_projection k B] with n hn
  intro P _ tail pre skip a a₀ D ha hD hDB ho hs μ _ V hV x hx R hR hc
  have hI : Integrable (fun p => (projectionEuclideanNorm n (V p))^(2*k+2)) μ := by
    apply Integrable.of_bound (((projectionEuclideanNorm_measurable n).comp hV).pow_const _).aestronglyMeasurable
      (R^(2*k+2))
    exact Eventually.of_forall fun p => by
      have hv0 : 0 ≤ projectionEuclideanNorm n (V p) := Real.sqrt_nonneg _
      change ‖(projectionEuclideanNorm n (V p))^(2*k+2)‖ ≤ _
      rw [Real.norm_of_nonneg (pow_nonneg hv0 _)]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (hR p) _
  exact (physicalTerminalConditionalSquare_power_le μ n k tail (skip++pre) hs V hV x hx hR).trans
    (hn P tail pre skip a a₀ D ha hD hDB ho hs μ V hV x hx hI hc)

end SKFluctuations

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

 theorem integral_fork_swap {P A B : Type*}
    [MeasurableSpace P] [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure P) [IsFiniteMeasure μ] (κ : Kernel P A) (ν : Kernel P B)
    [IsMarkovKernel κ] [IsMarkovKernel ν]
    {F : (P × A) × B → ℝ} (hF : Measurable F) {R : ℝ} (hR : ∀ z, |F z| ≤ R) :
    (∫ z, F z ∂(μ ⊗ₘ κ) ⊗ₘ ν.comap Prod.fst measurable_fst) =
      ∫ z : (P × B) × A, F ((z.1.1,z.2),z.1.2)
        ∂(μ ⊗ₘ ν) ⊗ₘ κ.comap Prod.fst measurable_fst := by
  let flip : (P × B) × A → (P × A) × B := fun z => ((z.1.1,z.2),z.1.2)
  have hf : Measurable flip := ((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
    (measurable_snd.comp measurable_fst)
  have hI : Integrable F ((μ ⊗ₘ κ) ⊗ₘ ν.comap Prod.fst measurable_fst) :=
    Integrable.of_bound hF.aestronglyMeasurable R (Eventually.of_forall hR)
  have hJ : Integrable (F ∘ flip) ((μ ⊗ₘ ν) ⊗ₘ κ.comap Prod.fst measurable_fst) :=
    Integrable.of_bound (hF.comp hf).aestronglyMeasurable R (Eventually.of_forall (fun z => hR (flip z)))
  have hleft : Integrable (fun z : P × A => ∫ b, F (z,b) ∂ν z.1) (μ ⊗ₘ κ) := by
    apply Integrable.of_bound
      (hF.stronglyMeasurable.integral_kernel_prod_right'
        (κ := ν.comap Prod.fst measurable_fst)).aestronglyMeasurable R
    exact Eventually.of_forall fun z => by
      exact norm_integral_le_of_norm_le_const (Eventually.of_forall (fun b => hR (z,b))) |>.trans_eq (by simp)
  have hright : Integrable (fun z : P × B => ∫ a, F ((z.1,a),z.2) ∂κ z.1) (μ ⊗ₘ ν) := by
    apply Integrable.of_bound
      ((hF.comp hf).stronglyMeasurable.integral_kernel_prod_right'
        (κ := κ.comap Prod.fst measurable_fst)).aestronglyMeasurable R
    exact Eventually.of_forall fun z => by
      exact norm_integral_le_of_norm_le_const (Eventually.of_forall (fun a => hR ((z.1,a),z.2))) |>.trans_eq (by simp)
  change (∫ z, F z ∂(μ ⊗ₘ κ) ⊗ₘ ν.comap Prod.fst measurable_fst) =
    ∫ z, (F ∘ flip) z ∂(μ ⊗ₘ ν) ⊗ₘ κ.comap Prod.fst measurable_fst
  rw [Measure.integral_compProd hI, Measure.integral_compProd hJ]
  change (∫ z : P × A, (∫ b, F (z,b) ∂ν z.1) ∂μ ⊗ₘ κ) =
    ∫ z : P × B, (∫ a, F ((z.1,a),z.2) ∂κ z.1) ∂μ ⊗ₘ ν
  rw [Measure.integral_compProd hleft,Measure.integral_compProd hright]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro p
  have hi : Integrable (fun z : A × B => F ((p,z.1),z.2)) ((κ p).prod (ν p)) :=
    Integrable.of_bound (hF.comp ((measurable_const.prodMk measurable_fst).prodMk
      measurable_snd)).aestronglyMeasurable R (Eventually.of_forall fun z => hR ((p,z.1),z.2))
  exact integral_integral_swap (f := fun a b => F ((p,a),b)) hi

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
  [MeasurableSpace S] [StandardBorelSpace S]

 def conditionalPathAverage (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ) :
    (steps : List (GaussianStep ι)) → {P : Type} → (P → ι → ℝ) → ℕ →
      (P × ForwardPath (ι → ℝ) S steps.length → ℝ) →
      P × ForwardPath (ι → ℝ) S steps.length → ℝ
  | steps, _, x, 0, F, p => ∫ q, F (p.1,q) ∂hierarchyPathKernel w φ steps (x p.1)
  | [], _, _, _+1, F, p => F p
  | _st::tail, _, x, k+1, F, p =>
      conditionalPathAverage w φ tail (fun q => x q.1+q.2) k
        (fun q => F (q.1.1,(q.1.2,q.2))) ((p.1,p.2.1),p.2.2)

 theorem conditionalPathAverage_measurable {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) {P : Type} [MeasurableSpace P]
    (x : P → ι → ℝ) (hx : Measurable x) (k : ℕ)
    {F : P × ForwardPath (ι → ℝ) S steps.length → ℝ} (hF : Measurable F) :
    Measurable[forwardPrefixSpace P (ι → ℝ) S steps.length k]
      (conditionalPathAverage w φ steps x k F) := by
  induction steps generalizing P a k with
  | nil =>
    cases k with
    | zero =>
      have := hierarchyPathKernel_markov hw φ _ ha
      exact (hF.stronglyMeasurable.integral_kernel_prod_right'
        (κ := (hierarchyPathKernel w φ []).comap x hx)).measurable.comp
          (comap_measurable Prod.fst)
    | succ k => exact hF
  | cons st tail ih =>
    cases k with
    | zero =>
      have := hierarchyPathKernel_markov hw φ _ ha
      exact (hF.stronglyMeasurable.integral_kernel_prod_right'
        (κ := (hierarchyPathKernel w φ (st::tail)).comap x hx)).measurable.comp
          (comap_measurable Prod.fst)
    | succ k =>
      exact (ih ha.2.2.2 (fun q : P × (ι → ℝ) => x q.1+q.2)
        ((hx.comp measurable_fst).add measurable_snd) k
        (hF.comp MeasurableEquiv.prodAssoc.measurable)).comp
          (comap_measurable MeasurableEquiv.prodAssoc.symm)

 theorem condExp_conditionalPathAverage {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (x : P → ι → ℝ) (hx : Measurable x) (k : ℕ)
    {F : P × ForwardPath (ι → ℝ) S steps.length → ℝ} (hF : Measurable F)
    (hI : Integrable F (μ ⊗ₘ (hierarchyPathKernel w φ steps).comap x hx)) :
    (μ ⊗ₘ (hierarchyPathKernel w φ steps).comap x hx)[F |
      forwardPrefixSpace P (ι → ℝ) S steps.length k] =ᵐ[
      μ ⊗ₘ (hierarchyPathKernel w φ steps).comap x hx]
        conditionalPathAverage w φ steps x k F := by
  induction steps generalizing P a k with
  | nil =>
    have := hierarchyPathKernel_markov hw φ [] ha
    cases k with
    | zero => exact condExp_compProd_first μ ((hierarchyPathKernel w φ []).comap x hx) F hI
    | succ k =>
      exact Eventually.of_forall fun p => congrFun
        (condExp_of_stronglyMeasurable (forwardPrefixSpace_le _ _ _ _ _)
          hF.stronglyMeasurable hI) p
  | cons st tail ih =>
    rcases st with ⟨m,q⟩
    have := hierarchyPathKernel_markov hw φ ((m,q)::tail) ha
    cases k with
    | zero => exact condExp_compProd_first μ ((hierarchyPathKernel w φ ((m,q)::tail)).comap x hx) F hI
    | succ k =>
      have := plantedStepKernel_markov hw φ m q tail ha
      let ν := μ ⊗ₘ (hierarchyPathKernel w φ ((m,q)::tail)).comap x hx
      let μ' := μ ⊗ₘ (plantedStepKernel w φ m q tail).comap x hx
      let x' : P × (ι → ℝ) → ι → ℝ := fun p => x p.1+p.2
      have hx' : Measurable x' := (hx.comp measurable_fst).add measurable_snd
      let e : (P × ForwardPath (ι → ℝ) S (((m,q)::tail).length)) ≃ᵐ
          ((P × (ι → ℝ)) × ForwardPath (ι → ℝ) S tail.length) := MeasurableEquiv.prodAssoc.symm
      have hmap : ν.map e = μ' ⊗ₘ (hierarchyPathKernel w φ tail).comap x' hx' :=
        hierarchyPathLaw_cons hw φ m q tail ha μ x hx
      let G : (P × (ι → ℝ)) × ForwardPath (ι → ℝ) S tail.length → ℝ :=
        fun p => F (p.1.1,(p.1.2,p.2))
      have hI' : Integrable G (ν.map e) := by
        apply e.measurableEmbedding.integrable_map_iff.mpr
        exact hI
      have he := condExp_measurableEquiv (forwardPrefixSpace (P × (ι → ℝ)) (ι → ℝ) S tail.length k)
        e ν (forwardPrefixSpace_le _ _ _ _ _) G hI'
      have ht := ih ha.2.2.2 μ' x' hx' k (hF.comp e.symm.measurable) (hmap ▸ hI')
      rw [← hmap] at ht
      exact he.trans (ae_of_ae_map e.measurable.aemeasurable ht)

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 def physicalBlockSquare (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {P : Type} (x : P → FeatureIndex n → ℝ) (i j : ℕ) :=
  conditionalPathAverage (uniformWeight n) (finiteFeature n) steps x i
    (fun p => ‖actualSpinPath n steps x j p-actualSpinPath n steps x i p‖^2)

 theorem actualSpinPath_measurable (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {a : ℝ} (ha : OrderedSteps a steps) {P : Type} [MeasurableSpace P]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (i : ℕ) :
    Measurable (actualSpinPath n steps x i) := by
  change Measurable ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm ∘ _)
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.continuous.measurable.comp
  exact Measurable.of_eval fun j =>
    (hierarchyMeanPath_measurable (uniformWeight_pos n) (finiteFeature n)
      (fun σ => normalizedSpin n σ j) steps ha x hx i).mono
        (forwardPrefixSpace_le _ _ _ _ _) le_rfl

 theorem physicalBlockSquare_measurable (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {a : ℝ} (ha : OrderedSteps a steps) {P : Type} [MeasurableSpace P]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (i j : ℕ) :
    Measurable (physicalBlockSquare n steps x i j) :=
  (conditionalPathAverage_measurable (uniformWeight_pos n) (finiteFeature n) steps ha x hx i
    (((actualSpinPath_measurable n steps ha x hx j).sub
      (actualSpinPath_measurable n steps ha x hx i)).norm.pow_const 2)).mono
        (forwardPrefixSpace_le _ _ _ _ _) le_rfl

 theorem conditionalBlockSquare_eq_physical (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (i j : ℕ) :
    conditionalBlockSquare
      (μ ⊗ₘ (hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps).comap x hx)
      (forwardFiltration P (FeatureIndex n → ℝ) (Spin n) steps.length)
      (actualSpinPath n steps x) i j =ᵐ[
      μ ⊗ₘ (hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps).comap x hx]
        physicalBlockSquare n steps x i j := by
  have := hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) steps ha
  have hm := ((actualSpinPath_measurable n steps ha x hx j).sub
    (actualSpinPath_measurable n steps ha x hx i)).norm.pow_const 2
  apply condExp_conditionalPathAverage (uniformWeight_pos n) (finiteFeature n) steps ha μ x hx i hm
  apply Integrable.of_bound hm.aestronglyMeasurable 4
  exact Eventually.of_forall fun p => by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h := (norm_sub_le (actualSpinPath n steps x j p) (actualSpinPath n steps x i p)).trans
      (add_le_add (actualSpinPath_norm_le n steps ha x j p) (actualSpinPath_norm_le n steps ha x i p))
    simp only [Pi.sub_apply]
    nlinarith [norm_nonneg (actualSpinPath n steps x j p-actualSpinPath n steps x i p)]

 theorem conditionalBlockSquare_uniform_eq_physical (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) :
    ∀ᵐ p ∂μ ⊗ₘ (hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps).comap x hx,
      ∀ i j, conditionalBlockSquare
        (μ ⊗ₘ (hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps).comap x hx)
        (forwardFiltration P (FeatureIndex n → ℝ) (Spin n) steps.length)
        (actualSpinPath n steps x) i j p = physicalBlockSquare n steps x i j p :=
  ae_all_iff.mpr fun i => ae_all_iff.mpr fun j =>
    conditionalBlockSquare_eq_physical n steps ha μ x hx i j

 def physicalRadiusSquareIntegral (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {P : Type} (x : P → FeatureIndex n → ℝ) (τ : ℝ → ℕ) (a b η : ℝ)
    (p : P × ForwardPath (FeatureIndex n → ℝ) (Spin n) steps.length) : ℝ :=
  ∫ s in a..b, physicalBlockSquare n steps x (τ s) (τ (s+η)) p

 theorem actualRadiusSquareIntegral_eq_physical (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {c : ℝ} (hc : OrderedSteps c steps)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (τ : ℝ → ℕ) (a b η : ℝ) :
    actualRadiusSquareIntegral n steps μ x hx τ a b η =ᵐ[
      μ ⊗ₘ (hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps).comap x hx]
        physicalRadiusSquareIntegral n steps x τ a b η := by
  filter_upwards [conditionalBlockSquare_uniform_eq_physical n steps hc μ x hx] with p hp
  exact intervalIntegral.integral_congr (fun s _ => hp (τ s) (τ (s+η)))

 theorem physicalNearPairProduct_Lp (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {c : ℝ} (hc : OrderedSteps c steps) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
    {τ : ℝ → ℕ} (hτ : Monotone τ) {a b η : ℝ} (hab : a ≤ b) (hη : 0 < η)
    {p : ℕ} (hp : 0 < p) :
    (∫ q, (runningMax (fun j => ‖actualSpinPath n steps x j q‖^2) (τ (b+η))*
      physicalRadiusSquareIntegral n steps x τ a b η q)^p
      ∂(μ ⊗ₘ (hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps).comap x hx))^((p:ℝ)⁻¹) ≤
      (nearPairMomentConstant p)^((p:ℝ)⁻¹)*η*
        (∫ q, ‖actualSpinPath n steps x (τ (b+η)) q‖^(4*p)
          ∂(μ ⊗ₘ (hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps).comap x hx))^((p:ℝ)⁻¹) := by
  have he := actualRadiusSquareIntegral_eq_physical n steps hc μ x hx τ a b η
  have hh := actualNearPairProduct_Lp n steps hc μ x hx hτ hab hη hp
  convert hh using 1
  congr 1
  apply integral_congr_ae
  filter_upwards [he] with q hq
  rw [hq]

end SKFluctuations

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
  [MeasurableSpace S] [StandardBorelSpace S]

omit [Nonempty S] [StandardBorelSpace S] in
 theorem conditionalPathAverage_nonneg [Nonempty S] [StandardBorelSpace S]
    (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (steps : List (GaussianStep ι)) {P : Type} (x : P → ι → ℝ) (k : ℕ)
    {F : P × ForwardPath (ι → ℝ) S steps.length → ℝ} (hF : ∀ p, 0 ≤ F p)
    (p : P × ForwardPath (ι → ℝ) S steps.length) :
    0 ≤ conditionalPathAverage w φ steps x k F p := by
  induction steps generalizing P k with
  | nil => cases k with
    | zero => exact integral_nonneg fun q => hF (p.1,q)
    | succ k => exact hF p
  | cons st tail ih => cases k with
    | zero => exact integral_nonneg fun q => hF (p.1,q)
    | succ k =>
      exact ih (fun q : P × (ι → ℝ) => x q.1+q.2) k
        (fun q => hF (q.1.1,(q.1.2,q.2))) ((p.1,p.2.1),p.2.2)

omit [Nonempty S] [StandardBorelSpace S] in
 theorem conditionalPathAverage_const_mul [Nonempty S] [StandardBorelSpace S]
    (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (steps : List (GaussianStep ι)) {P : Type} (x : P → ι → ℝ) (k : ℕ)
    (F : P × ForwardPath (ι → ℝ) S steps.length → ℝ) (c : ℝ)
    (p : P × ForwardPath (ι → ℝ) S steps.length) :
    conditionalPathAverage w φ steps x k (fun q => c*F q) p =
      c*conditionalPathAverage w φ steps x k F p := by
  induction steps generalizing P k with
  | nil => cases k with
    | zero => exact integral_const_mul c _
    | succ k => rfl
  | cons st tail ih => cases k with
    | zero => exact integral_const_mul c _
    | succ k => exact ih _ k _ _

 theorem conditionalPathAverage_mono_bounded {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) {P : Type} [MeasurableSpace P]
    (x : P → ι → ℝ) (k : ℕ)
    {F G : P × ForwardPath (ι → ℝ) S steps.length → ℝ}
    (hF : Measurable F) (hG : Measurable G) {R : ℝ}
    (hFR : ∀ p, |F p| ≤ R) (hGR : ∀ p, |G p| ≤ R) (hFG : ∀ p, F p ≤ G p)
    (p : P × ForwardPath (ι → ℝ) S steps.length) :
    conditionalPathAverage w φ steps x k F p ≤ conditionalPathAverage w φ steps x k G p := by
  induction steps generalizing P a k with
  | nil =>
    have := hierarchyPathKernel_markov hw φ [] ha
    cases k with
    | zero =>
      exact integral_mono (Integrable.of_bound (hF.comp measurable_prodMk_left).aestronglyMeasurable R
        (Eventually.of_forall fun q => hFR (p.1,q)))
        (Integrable.of_bound (hG.comp measurable_prodMk_left).aestronglyMeasurable R
        (Eventually.of_forall fun q => hGR (p.1,q))) (fun q => hFG (p.1,q))
    | succ k => exact hFG p
  | cons st tail ih =>
    have := hierarchyPathKernel_markov hw φ (st::tail) ha
    cases k with
    | zero =>
      exact integral_mono (Integrable.of_bound (hF.comp measurable_prodMk_left).aestronglyMeasurable R
        (Eventually.of_forall fun q => hFR (p.1,q)))
        (Integrable.of_bound (hG.comp measurable_prodMk_left).aestronglyMeasurable R
        (Eventually.of_forall fun q => hGR (p.1,q))) (fun q => hFG (p.1,q))
    | succ k =>
      exact ih ha.2.2.2 (fun q : P × (ι → ℝ) => x q.1+q.2) k
        (hF.comp MeasurableEquiv.prodAssoc.measurable) (hG.comp MeasurableEquiv.prodAssoc.measurable)
        (fun q => hFR (q.1.1,(q.1.2,q.2))) (fun q => hGR (q.1.1,(q.1.2,q.2)))
        (fun q => hFG (q.1.1,(q.1.2,q.2))) ((p.1,p.2.1),p.2.2)

end SKFluctuations.Hierarchy
namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators RealInnerProductSpace

 def physicalNearLayerSquare (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {P : Type} (x : P → FeatureIndex n → ℝ) (i j : ℕ)
    (p : P × ForwardPath (FeatureIndex n → ℝ) (Spin n) steps.length) : ℝ :=
  conditionalPathAverage (uniformWeight n) (finiteFeature n) steps x i
    (fun q => (inner ℝ (actualSpinPath n steps x j p-actualSpinPath n steps x i p)
      (actualSpinPath n steps x j q-actualSpinPath n steps x i q))^2) p

 theorem physicalNearLayerSquare_le (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {a : ℝ} (ha : OrderedSteps a steps) {P : Type} [MeasurableSpace P]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (i j : ℕ)
    (p : P × ForwardPath (FeatureIndex n → ℝ) (Spin n) steps.length) :
    physicalNearLayerSquare n steps x i j p ≤
      ‖actualSpinPath n steps x j p-actualSpinPath n steps x i p‖^2 *
        physicalBlockSquare n steps x i j p := by
  let d := fun q => actualSpinPath n steps x j q-actualSpinPath n steps x i q
  have hd : Measurable d := (actualSpinPath_measurable n steps ha x hx j).sub
    (actualSpinPath_measurable n steps ha x hx i)
  have hD q : ‖d q‖ ≤ 2 := (norm_sub_le _ _).trans (by
    linarith [actualSpinPath_norm_le n steps ha x j q,actualSpinPath_norm_le n steps ha x i q])
  have hsq q : ‖d q‖^2 ≤ 4 := by nlinarith [norm_nonneg (d q),hD q]
  have hc q : (inner ℝ (d p) (d q))^2 ≤ ‖d p‖^2*‖d q‖^2 := by
    simpa only [real_inner_self_eq_norm_sq,pow_two] using real_inner_mul_inner_self_le (d p) (d q)
  have hb q : ‖d p‖^2*‖d q‖^2 ≤ 16 := by nlinarith [hsq p,hsq q,sq_nonneg ‖d p‖,sq_nonneg ‖d q‖]
  change conditionalPathAverage _ _ _ _ i (fun q => (inner ℝ (d p) (d q))^2) p ≤ _
  have hh := conditionalPathAverage_mono_bounded (uniformWeight_pos n) (finiteFeature n)
    steps ha x i ((measurable_const.inner hd).pow_const 2) ((hd.norm.pow_const 2).const_mul (‖d p‖^2))
    (R := 16) (fun q => by
      rw [abs_of_nonneg (sq_nonneg (inner ℝ (d p) (d q)))]; exact (hc q).trans (hb q))
    (fun q => by
      rw [abs_of_nonneg (mul_nonneg (sq_nonneg ‖d p‖) (sq_nonneg ‖d q‖))]; exact hb q) hc p
  rw [conditionalPathAverage_const_mul] at hh
  exact hh

end SKFluctuations

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
  [MeasurableSpace S] [StandardBorelSpace S]

 theorem conditionalPathAverage_const {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) {P : Type} (x : P → ι → ℝ)
    (k : ℕ) (c : ℝ) (p : P × ForwardPath (ι → ℝ) S steps.length) :
    conditionalPathAverage w φ steps x k (fun _ => c) p = c := by
  induction steps generalizing P a k with
  | nil =>
    have := hierarchyPathKernel_markov hw φ [] ha
    cases k <;> simp [conditionalPathAverage]
  | cons st tail ih =>
    have := hierarchyPathKernel_markov hw φ (st::tail) ha
    cases k with
    | zero => simp [conditionalPathAverage]
    | succ k => exact ih ha.2.2.2 _ k _

 theorem conditionalPathAverage_parameter_measurable {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) {P A : Type} [MeasurableSpace P] [MeasurableSpace A]
    (x : P → ι → ℝ) (hx : Measurable x) (k : ℕ)
    {F : A × (P × ForwardPath (ι → ℝ) S steps.length) → ℝ} (hF : Measurable F) :
    Measurable (fun p : A × (P × ForwardPath (ι → ℝ) S steps.length) =>
      conditionalPathAverage w φ steps x k (fun q => F (p.1,q)) p.2) := by
  induction steps generalizing P a k with
  | nil =>
    have := hierarchyPathKernel_markov hw φ [] ha
    cases k with
    | zero =>
      let G : (A × P) × ForwardPath (ι → ℝ) S 0 → ℝ :=
        fun q => F (q.1.1,(q.1.2,q.2))
      have hG : Measurable G := by unfold G; fun_prop
      have h := hG.stronglyMeasurable.integral_kernel_prod_right'
        (κ := (hierarchyPathKernel w φ []).comap (fun q : A × P => x q.2)
          (hx.comp measurable_snd))
      exact h.measurable.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
    | succ k => exact hF
  | cons st tail ih =>
    have := hierarchyPathKernel_markov hw φ (st::tail) ha
    cases k with
    | zero =>
      let G : (A × P) × ForwardPath (ι → ℝ) S (st::tail).length → ℝ :=
        fun q => F (q.1.1,(q.1.2,q.2))
      have hG : Measurable G := by unfold G; fun_prop
      have h := hG.stronglyMeasurable.integral_kernel_prod_right'
        (κ := (hierarchyPathKernel w φ (st::tail)).comap (fun q : A × P => x q.2)
          (hx.comp measurable_snd))
      exact h.measurable.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
    | succ k =>
      let G : A × ((P × (ι → ℝ)) × ForwardPath (ι → ℝ) S tail.length) → ℝ :=
        fun q => F (q.1,(q.2.1.1,(q.2.1.2,q.2.2)))
      have hG : Measurable G := by unfold G; fun_prop
      have hh := ih ha.2.2.2 (fun q : P × (ι → ℝ) => x q.1+q.2)
        ((hx.comp measurable_fst).add measurable_snd) k hG
      exact hh.comp (show Measurable (fun q : A × (P × ForwardPath (ι → ℝ) S (st::tail).length) =>
        (q.1,((q.2.1,q.2.2.1),q.2.2.2))) from by fun_prop)

end SKFluctuations.Hierarchy

end

end OAI
