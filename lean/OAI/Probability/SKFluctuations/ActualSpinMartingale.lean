import Mathlib
import OAI.Probability.SKFluctuations.ActualConditionalHierarchy

namespace OAI

/-! Actual Spin Martingale. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Hierarchy
open scoped Topology NNReal ENNReal BigOperators

 
noncomputable def normalizedSpin (n : ℕ) (σ : Spin n) (i : Fin n) : ℝ :=
  spinValue (σ i)/Real.sqrt (n:ℝ)

noncomputable def actualSpinMean (n : ℕ) (tail : List (GaussianStep (FeatureIndex n)))
    (x : FeatureIndex n → ℝ) (i : Fin n) : ℝ :=
  gaussianHierarchyMean (uniformWeight n) (finiteFeature n)
    (fun σ => normalizedSpin n σ i) tail x

theorem actualSpinMean_measurable (n : ℕ) (tail : List (GaussianStep (FeatureIndex n)))
    {a : ℝ} (ha : OrderedSteps a tail) : Measurable (actualSpinMean n tail) := by
  apply Measurable.of_eval
  intro i
  exact (gaussianHierarchyMean_smooth (uniformWeight_pos n) (finiteFeature n)
    (fun σ => normalizedSpin n σ i) tail ha 0).continuous.measurable

theorem actualSpinMean_condExp {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (n : ℕ) (tail : List (GaussianStep (FeatureIndex n)))
    {a : ℝ} (ha : OrderedSteps a tail) (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
    (i : Fin n) :
    (μ ⊗ₘ (hierarchyPathKernel (uniformWeight n) (finiteFeature n) tail).comap x hx)[
      (fun p : P × ForwardPath (FeatureIndex n → ℝ) (Spin n) tail.length =>
        normalizedSpin n (ForwardPath.spin tail.length p.2) i) |
          (inferInstance : MeasurableSpace P).comap Prod.fst] =ᵐ[
            μ ⊗ₘ (hierarchyPathKernel (uniformWeight n) (finiteFeature n) tail).comap x hx]
       fun p => actualSpinMean n tail (x p.1) i :=
  condExp_prefix_hierarchy_fixed (uniformWeight_pos n) (finiteFeature n) tail ha μ x hx
    (fun σ => normalizedSpin n σ i)

theorem actualSpinMean_abs_le (n : ℕ) (tail : List (GaussianStep (FeatureIndex n)))
    {a : ℝ} (ha : OrderedSteps a tail) (x : FeatureIndex n → ℝ) (i : Fin n) :
    |actualSpinMean n tail x i| ≤ 1/Real.sqrt (n:ℝ) := by
  apply gaussianHierarchyMean_abs_le (uniformWeight_pos n) (finiteFeature n) _ tail ha x
  intro σ
  simp only [normalizedSpin, abs_div, abs_spinValue, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact le_rfl

theorem projectionEuclideanNorm_le_of_coordinate_bound (n : ℕ) (V : Fin n → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hV : ∀ i, |V i| ≤ C/Real.sqrt (n:ℝ)) :
    projectionEuclideanNorm n V ≤ C := by
  by_cases hn : n = 0
  · subst n
    simpa only [projectionEuclideanNorm, Finset.univ_eq_empty, Finset.sum_empty, Real.sqrt_zero] using hC
  have hnp : 0 < (n:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hs := Real.sqrt_pos.mpr hnp
  apply (Real.sqrt_le_left hC).mpr
  calc
    (∑ i, (V i)^2) ≤ ∑ _i : Fin n, (C/Real.sqrt (n:ℝ))^2 := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hV i) 2
    _ = C^2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        div_pow, Real.sq_sqrt hnp.le]
      field_simp

theorem actualSpinMean_norm_le (n : ℕ) (tail : List (GaussianStep (FeatureIndex n)))
    {a : ℝ} (ha : OrderedSteps a tail) (x : FeatureIndex n → ℝ) :
    projectionEuclideanNorm n (actualSpinMean n tail x) ≤ 1 :=
  projectionEuclideanNorm_le_of_coordinate_bound n _ zero_le_one (actualSpinMean_abs_le n tail ha x)

 

theorem actualSpinMean_sub_norm_le (n : ℕ)
    (tail₁ tail₂ : List (GaussianStep (FeatureIndex n))) {a₁ a₂ : ℝ}
    (ha₁ : OrderedSteps a₁ tail₁) (ha₂ : OrderedSteps a₂ tail₂)
    (x₁ x₂ : FeatureIndex n → ℝ) :
    projectionEuclideanNorm n (actualSpinMean n tail₁ x₁ - actualSpinMean n tail₂ x₂) ≤ 2 := by
  apply projectionEuclideanNorm_le_of_coordinate_bound n _ (by norm_num)
  intro i
  have hh := (abs_sub _ _).trans (add_le_add
    (actualSpinMean_abs_le n tail₁ ha₁ x₁ i) (actualSpinMean_abs_le n tail₂ ha₂ x₂ i))
  exact hh.trans_eq (by ring)

theorem actualSpinMean_sub_moment_integrable {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (n k : ℕ)
    (tail₁ tail₂ : List (GaussianStep (FeatureIndex n))) {a₁ a₂ : ℝ}
    (ha₁ : OrderedSteps a₁ tail₁) (ha₂ : OrderedSteps a₂ tail₂)
    (x₁ x₂ : P → FeatureIndex n → ℝ) (hx₁ : Measurable x₁) (hx₂ : Measurable x₂) :
    Integrable (fun p => (projectionEuclideanNorm n
        (actualSpinMean n tail₁ (x₁ p)-actualSpinMean n tail₂ (x₂ p)))^(2*k+2)) μ := by
  have hV := ((actualSpinMean_measurable n tail₁ ha₁).comp hx₁).sub
    ((actualSpinMean_measurable n tail₂ ha₂).comp hx₂)
  apply (integrable_const ((2:ℝ)^(2*k+2))).mono'
    (((projectionEuclideanNorm_measurable n).comp hV).pow_const _).aestronglyMeasurable
  exact Eventually.of_forall fun p => by
    change |(projectionEuclideanNorm n (actualSpinMean n tail₁ (x₁ p)-actualSpinMean n tail₂ (x₂ p)))^(2*k+2)| ≤ _
    rw [abs_of_nonneg (pow_nonneg (show 0 ≤ projectionEuclideanNorm n _ from Real.sqrt_nonneg _) _)]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (actualSpinMean_sub_norm_le n tail₁ tail₂ ha₁ ha₂ (x₁ p) (x₂ p)) _

 

theorem spinProjection_actualSpinMean (n : ℕ) (V : Fin n → ℝ)
    (tail : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a tail)
    (x : FeatureIndex n → ℝ) :
    (∑ i, V i*actualSpinMean n tail x i) =
      gaussianHierarchyMean (uniformWeight n) (finiteFeature n) (spinProjection n V) tail x := by
  simp only [actualSpinMean,gaussianHierarchyMean_atoms (uniformWeight_pos n) (finiteFeature n) tail ha,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [normalizedSpin,spinProjection,Finset.sum_div,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

end SKFluctuations

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {𝒢 : Filtration ℕ (inferInstance : MeasurableSpace Ω)}

 

theorem martingale_finiteCoordinates {ι : Type} [Fintype ι]
    {X : ι → ℕ → Ω → ℝ} (hX : ∀ i, Martingale (X i) 𝒢 μ) :
    Martingale (fun k ω i => X i k ω) 𝒢 μ := by
  refine ⟨?_, ?_⟩
  · intro k
    let : MeasurableSpace Ω := 𝒢 k
    exact (Measurable.of_eval (fun i =>
      ((hX i).stronglyMeasurable k).measurable)).stronglyMeasurable
  intro j k hjk
  have hI : Integrable (fun ω i => X i k ω) μ :=
    integrable_pi_iff.mpr (fun i => (hX i).integrable k)
  have hc (i : ι) : (fun ω => ((μ[(fun ω i => X i k ω) | 𝒢 j]) ω) i) =ᵐ[μ] X i j := by
    exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i).comp_condExp_comm hI).trans
      ((hX i).condExp_ae_eq hjk)
  filter_upwards [ae_all_iff.mpr hc] with ω hω
  exact funext hω

 theorem martingale_continuousLinearMap {E F : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {X : ℕ → Ω → E}
    (hX : Martingale X 𝒢 μ) (T : E →L[ℝ] F) :
    Martingale (fun k ω => T (X k ω)) 𝒢 μ := by
  refine ⟨fun k => T.continuous.comp_stronglyMeasurable (hX.stronglyMeasurable k), ?_⟩
  intro i j hij
  filter_upwards [(T.comp_condExp_comm (m := 𝒢 i) (hX.integrable j)).symm,
    hX.condExp_ae_eq hij] with ω he he'
  exact he.trans (congrArg T he')

variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

 theorem hierarchyMeanPath_abs_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (A : S → ℝ) {C : ℝ} (hA : ∀ σ, |A σ| ≤ C)
    (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps)
    {P : Type} (x : P → ι → ℝ) (k : ℕ)
    (p : P × ForwardPath (ι → ℝ) S steps.length) :
    |hierarchyMeanPath w φ A steps x k p| ≤ C := by
  induction steps generalizing P a k with
  | nil =>
    cases k with
    | zero => exact gaussianHierarchyMean_abs_le hw φ hA [] ha (x p.1)
    | succ k => exact hA p.2
  | cons st tail ih =>
    cases k with
    | zero => exact gaussianHierarchyMean_abs_le hw φ hA (st::tail) ha (x p.1)
    | succ k => exact ih ha.2.2.2 _ k ((p.1,p.2.1),p.2.2)

end SKFluctuations.Hierarchy
namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 

def actualSpinPath (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {P : Type} (x : P → FeatureIndex n → ℝ) (k : ℕ)
    (p : P × ForwardPath (FeatureIndex n → ℝ) (Spin n) steps.length) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => hierarchyMeanPath (uniformWeight n) (finiteFeature n)
    (fun σ => normalizedSpin n σ i) steps x k p)

 theorem actualSpinPath_martingale (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {a : ℝ} (ha : OrderedSteps a steps) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (x : P → FeatureIndex n → ℝ) (hx : Measurable x) :
    Martingale (actualSpinPath n steps x)
      (forwardFiltration P (FeatureIndex n → ℝ) (Spin n) steps.length)
      (μ ⊗ₘ (hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps).comap x hx) := by
  exact martingale_continuousLinearMap (martingale_finiteCoordinates (fun i =>
    hierarchyMeanPath_martingale (uniformWeight_pos n) (finiteFeature n)
      (fun σ => normalizedSpin n σ i) steps ha μ x hx))
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.toContinuousLinearMap

 theorem actualSpinPath_norm_le (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {a : ℝ} (ha : OrderedSteps a steps) {P : Type} (x : P → FeatureIndex n → ℝ)
    (k : ℕ) (p : P × ForwardPath (FeatureIndex n → ℝ) (Spin n) steps.length) :
    ‖actualSpinPath n steps x k p‖ ≤ 1 := by
  rw [EuclideanSpace.norm_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  apply projectionEuclideanNorm_le_of_coordinate_bound n _ zero_le_one
  intro i
  apply hierarchyMeanPath_abs_le (uniformWeight_pos n) (finiteFeature n) _ _ steps ha x k p
  intro σ
  simp only [normalizedSpin, abs_div, abs_spinValue, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact le_rfl

end SKFluctuations

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators

 

def sampledFiltration {Ω : Type} [MeasurableSpace Ω]
    (𝒢 : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (τ : ℕ → ℕ) (hτ : Monotone τ) : Filtration ℕ (inferInstance : MeasurableSpace Ω) where
  seq := fun j => 𝒢 (τ j)
  mono' := fun _ _ h => 𝒢.mono (hτ h)
  le' := fun j => 𝒢.le (τ j)

theorem martingale_sampled {Ω E : Type} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure Ω}
    {𝒢 : Filtration ℕ (inferInstance : MeasurableSpace Ω)} {X : ℕ → Ω → E}
    (hX : Martingale X 𝒢 μ) (τ : ℕ → ℕ) (hτ : Monotone τ) :
    Martingale (fun j => X (τ j)) (sampledFiltration 𝒢 τ hτ) μ :=
  ⟨fun j => hX.stronglyMeasurable (τ j),
    fun _i _j hij => hX.condExp_ae_eq (hτ hij)⟩

end SKFluctuations.Hierarchy
namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 

def actualPathSquareSum (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {P : Type} [MeasurableSpace P] (μ : Measure P)
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
    (τ : ℕ → ℕ) (hτ : Monotone τ) (N : ℕ) :=
  conditionalSquareSum
    (μ ⊗ₘ (hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps).comap x hx)
    (sampledFiltration (forwardFiltration P (FeatureIndex n → ℝ) (Spin n) steps.length) τ hτ)
    (fun j => actualSpinPath n steps x (τ j)) N

 

theorem actualPathSquareSum_moment (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {a : ℝ} (ha : OrderedSteps a steps) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
    (τ : ℕ → ℕ) (hτ : Monotone τ) {p : ℕ} (hp : 0 < p) (N : ℕ) :
    (∫ q, actualPathSquareSum n steps μ x hx τ hτ N q^p
      ∂(μ ⊗ₘ (hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps).comap x hx)) ≤
      (p:ℝ)^p*∫ q, ‖actualSpinPath n steps x (τ N) q‖^(2*p)
        ∂(μ ⊗ₘ (hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps).comap x hx) := by
  have := hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) steps ha
  exact boundedMartingale_conditionalSquareSum_moment
    (martingale_sampled (actualSpinPath_martingale n steps ha μ x hx) τ hτ)
    (fun j => Eventually.of_forall (actualSpinPath_norm_le n steps ha x (τ j))) hp N

theorem actualPathSquareSum_Lp (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {a : ℝ} (ha : OrderedSteps a steps) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
    (τ : ℕ → ℕ) (hτ : Monotone τ) {p : ℕ} (hp : 0 < p) (N : ℕ) :
    (∫ q, actualPathSquareSum n steps μ x hx τ hτ N q^p
      ∂(μ ⊗ₘ (hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps).comap x hx))^((p:ℝ)⁻¹) ≤
      (p:ℝ)*(∫ q, ‖actualSpinPath n steps x (τ N) q‖^(2*p)
        ∂(μ ⊗ₘ (hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps).comap x hx))^((p:ℝ)⁻¹) := by
  have := hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) steps ha
  exact boundedMartingale_conditionalSquareSum_Lp
    (martingale_sampled (actualSpinPath_martingale n steps ha μ x hx) τ hτ)
    (fun j => Eventually.of_forall (actualSpinPath_norm_le n steps ha x (τ j))) hp N

end SKFluctuations

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

 

def actualCutField (pre tail : List (GaussianStep ι)) (x : ι → ℝ) :
    ForwardPath (ι → ℝ) S (pre++tail).length → (ι → ℝ) :=
  match pre with
  | [] => fun _ => x
  | _::pre => fun p => actualCutField pre tail (x+p.1) p.2

variable [MeasurableSpace S] [StandardBorelSpace S]

omit [Fintype ι] [Fintype S] [Nonempty S] [StandardBorelSpace S] in
theorem actualCutField_measurable_joint (pre tail : List (GaussianStep ι)) :
    Measurable (fun p : (ι → ℝ) × ForwardPath (ι → ℝ) S (pre++tail).length =>
      actualCutField pre tail p.1 p.2) := by
  induction pre with
  | nil => exact measurable_fst
  | cons st pre ih =>
    exact ih.comp ((measurable_fst.add (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd))

omit [Fintype ι] [Fintype S] [Nonempty S] [StandardBorelSpace S] in
theorem actualCutField_measurable (pre tail : List (GaussianStep ι)) (x : ι → ℝ) :
    Measurable (actualCutField (S := S) pre tail x) :=
  (actualCutField_measurable_joint pre tail).comp (measurable_const.prodMk measurable_id)

omit [Nonempty S] [MeasurableSpace S] [StandardBorelSpace S] in
theorem hierarchyMeanPath_zero (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (A : S → ℝ) (steps : List (GaussianStep ι)) {P : Type} (x : P → ι → ℝ)
    (p : P × ForwardPath (ι → ℝ) S steps.length) :
    hierarchyMeanPath w φ A steps x 0 p = gaussianHierarchyMean w φ A steps (x p.1) := by
  cases steps <;> rfl

omit [Nonempty S] [MeasurableSpace S] [StandardBorelSpace S] in
 

theorem hierarchyMeanPath_at_cut (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (A : S → ℝ) (pre tail : List (GaussianStep ι)) {P : Type} (x : P → ι → ℝ)
    (p : P × ForwardPath (ι → ℝ) S (pre++tail).length) :
    hierarchyMeanPath w φ A (pre++tail) x pre.length p =
      gaussianHierarchyMean w φ A tail (actualCutField pre tail (x p.1) p.2) := by
  induction pre generalizing P with
  | nil => exact hierarchyMeanPath_zero w φ A tail x p
  | cons st pre ih =>
    exact ih (fun q : P × (ι → ℝ) => x q.1+q.2) ((p.1,p.2.1),p.2.2)

 theorem integrable_actualCutField_test {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (pre tail : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a (pre++tail)) {B : (ι → ℝ) → ℝ}
    (hB : BddSmooth 0 B) (x : ι → ℝ) :
    Integrable (fun p => B (actualCutField (S := S) pre tail x p))
      (hierarchyPathKernel w φ (pre++tail) x) := by
  have := hierarchyPathKernel_markov hw φ (pre++tail) ha
  obtain ⟨C,_hC,hbound⟩ := hB.bound
  exact (integrable_const C).mono'
    ((hB.continuous.measurable.comp (actualCutField_measurable pre tail x)).stronglyMeasurable.aestronglyMeasurable)
    (Eventually.of_forall fun p => hbound _)

 

theorem integral_actualCutField_test {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (pre tail : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a (pre++tail)) {B : (ι → ℝ) → ℝ}
    (hB : BddSmooth 0 B) (x : ι → ℝ) :
    (∫ p, B (actualCutField (S := S) pre tail x p)
      ∂hierarchyPathKernel w φ (pre++tail) x) =
      prefixTest pre (gaussianHierarchy w φ tail) B x := by
  induction pre generalizing a x with
  | nil =>
    have := hierarchyPathKernel_markov hw φ tail ha
    simp only [actualCutField, List.nil_append, prefixTest, integral_const,
      probReal_univ, one_smul]
  | cons st pre ih =>
    rcases st with ⟨m,q⟩
    have := plantedStepKernel_markov hw φ m q (pre++tail) ha
    have := hierarchyPathKernel_markov hw φ (pre++tail) ha.2.2.2
    have hf := integrable_actualCutField_test hw φ ((m,q)::pre) tail ha hB x
    change Integrable (fun p : (ι → ℝ) × ForwardPath (ι → ℝ) S (pre++tail).length =>
      B (actualCutField pre tail (x+p.1) p.2))
      ((plantedStepKernel w φ m q (pre++tail) ⊗ₖ
        (hierarchyPathKernel w φ (pre++tail)).comap (fun p => p.1+p.2)
          (measurable_fst.add measurable_snd)) x) at hf
    change (∫ p : (ι → ℝ) × ForwardPath (ι → ℝ) S (pre++tail).length,
      B (actualCutField pre tail (x+p.1) p.2) ∂
      ((plantedStepKernel w φ m q (pre++tail) ⊗ₖ
        (hierarchyPathKernel w φ (pre++tail)).comap (fun p => p.1+p.2)
          (measurable_fst.add measurable_snd)) x)) = _
    rw [ProbabilityTheory.integral_compProd hf]
    simp only [Kernel.comap_apply]
    simp_rw [ih ha.2.2.2]
    rw [plantedStepKernel_eq_tilted hw φ m q (pre++tail) ha x,
      integral_tiltedLaw (F := fun z => gaussianHierarchy w φ (pre++tail) (x+z))
        ((gaussianHierarchy_continuous hw φ (pre++tail) ha.2.2.2).comp
          (continuous_const.add continuous_id)).measurable
        (gaussianHierarchy_integrable hw φ (pre++tail) ha.2.2.2 m q x)]
    simp only [prefixTest, prefixContinuation_hierarchy, shiftedMean]

 

theorem hierarchyBlockVariance_eq_actualPath {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (pre tail : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a (pre++tail)) (x v : ι → ℝ) :
    hierarchyBlockVariance w φ pre tail x v =
      ∫ p, (gaussianHierarchyMean w φ (fun σ => φ σ v) tail
        (actualCutField (S := S) pre tail x p) -
        gaussianHierarchyMean w φ (fun σ => φ σ v) (pre++tail) x)^2
          ∂hierarchyPathKernel w φ (pre++tail) x := by
  let M := gaussianHierarchyMean w φ (fun σ => φ σ v) tail
  let c := gaussianHierarchyMean w φ (fun σ => φ σ v) (pre++tail) x
  have hM := gaussianHierarchyMean_smooth hw φ (fun σ => φ σ v) tail (ha.suffix pre tail) 0
  have hB : BddSmooth 0 (fun y => (M y-c)^2) := by
    simpa only [M,pow_two] using (hM.sub (BddSmooth.const 0 c)).mul (hM.sub (BddSmooth.const 0 c))
  rw [hierarchyBlockVariance_eq_integral hw φ pre tail ha x v,
    integral_segmentLaw_test hw φ hB tail pre ha,
    integral_actualCutField_test hw φ pre tail ha hB x]

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal ENNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

 

theorem gaussianHierarchyMean_even_jensen {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (Y : S → ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (c : ℝ) (k : ℕ) (x : ι → ℝ) :
    |gaussianHierarchyMean w φ Y steps x-c|^(2*k+2) ≤
      gaussianHierarchyMean w φ (fun s => |Y s-c|^(2*k+2)) steps x := by
  simp_rw [gaussianHierarchyMean_atoms hw φ steps ha]
  simpa only [mul_comm] using finite_even_jensen (fun s => hierarchyAtom w φ steps s x) Y
    (fun s => hierarchyAtom_nonneg hw φ steps ha s x) (hierarchyAtom_sum hw φ steps ha x) c k

 

theorem integral_segmentLaw_laterProjection_le {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (Y : S → ℝ) (tail mid : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a (mid++tail)) (k : ℕ) (x : ι → ℝ) :
    (∫ p, |gaussianHierarchyMean w φ Y tail
      (forwardEnd mid.length (hierarchyIncrements mid) x p)-gaussianHierarchyMean w φ Y (mid++tail) x|^(2*k+2)
      ∂segmentLaw w φ tail mid x) ≤ hierarchyCenteredEvenMoment w φ Y (mid++tail) k x := by
  have := segmentLaw_isProbability hw φ tail mid ha x
  have hb := ha.suffix mid tail
  let c := gaussianHierarchyMean w φ Y (mid++tail) x
  have hend : Measurable (forwardEnd mid.length (hierarchyIncrements mid) x) :=
    (measurable_forwardEnd _ (hierarchyIncrements_measurable mid)).comp
      (measurable_const.prodMk measurable_id)
  have hL := ((gaussianHierarchyMean_smooth hw φ Y tail hb 0).sub (BddSmooth.const 0 c)).abs_natPow_zero (2*k+2)
  have hR := gaussianHierarchyMean_smooth hw φ (fun s => |Y s-c|^(2*k+2)) tail hb 0
  calc
    _ ≤ ∫ p, gaussianHierarchyMean w φ (fun s => |Y s-c|^(2*k+2)) tail
        (forwardEnd mid.length (hierarchyIncrements mid) x p) ∂segmentLaw w φ tail mid x :=
      integral_mono (hL.integrable_comp_measurable hend) (hR.integrable_comp_measurable hend)
        (fun p => gaussianHierarchyMean_even_jensen hw φ Y tail hb c k _)
    _ = _ := by
      rw [integral_segmentLaw_mean hw φ _ tail mid ha,gaussianHierarchyMean_atoms hw φ (mid++tail) ha]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Hierarchy
open scoped Topology NNReal ENNReal BigOperators

 

theorem alignedFieldClock_of_physical (n : ℕ)
    (pre : List (GaussianStep (FeatureIndex n))) (d : Fin pre.length → ℝ)
    (hd : ∀ j, 0 ≤ d j) (D : ℝ) (hD : ∑ j, d j = D)
    (hc : ∀ j i, (hierarchyClocks pre j (Sum.inl i) : ℝ) = d j)
    (V : Fin n → ℝ) : AlignedFieldClock (fieldProjectionDirection n V) D pre := by
  refine ⟨d, hd, hD, ?_⟩
  intro j i hi
  rcases i with i | i
  · exact hc j i
  · exact (hi rfl).elim

 

theorem random_directional_increment_integrable {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (n k : ℕ)
    (tail₁ tail₂ : List (GaussianStep (FeatureIndex n))) {a₁ a₂ : ℝ}
    (ha₁ : OrderedSteps a₁ tail₁) (ha₂ : OrderedSteps a₂ tail₂)
    (V : P → Fin n → ℝ) (hV : Measurable V)
    (x₁ x₂ : P → FeatureIndex n → ℝ) (hx₁ : Measurable x₁) (hx₂ : Measurable x₂)
    (hI : Integrable (fun p => (projectionEuclideanNorm n (V p))^(2*k+2)) μ) :
    Integrable (fun p => |gaussianHierarchyMean (uniformWeight n) (finiteFeature n)
        (spinProjection n (V p)) tail₁ (x₁ p) -
      gaussianHierarchyMean (uniformWeight n) (finiteFeature n)
        (spinProjection n (V p)) tail₂ (x₂ p)|^(2*k+2)) μ := by
  have hm₁ := (gaussianHierarchyMean_measurable_joint (uniformWeight_pos n) (finiteFeature n) tail₁ ha₁).comp
    (((spinProjection_measurable n).comp hV).prodMk hx₁)
  have hm₂ := (gaussianHierarchyMean_measurable_joint (uniformWeight_pos n) (finiteFeature n) tail₂ ha₂).comp
    (((spinProjection_measurable n).comp hV).prodMk hx₂)
  apply (hI.const_mul ((2:ℝ)^(2*k+2))).mono' (((hm₁.sub hm₂).abs).pow_const _).aestronglyMeasurable
  exact Eventually.of_forall fun p => by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
    have h₁ := gaussianHierarchyMean_abs_le (uniformWeight_pos n) (finiteFeature n)
      (spinProjection_abs_le n (V p)) tail₁ ha₁ (x₁ p)
    have h₂ := gaussianHierarchyMean_abs_le (uniformWeight_pos n) (finiteFeature n)
      (spinProjection_abs_le n (V p)) tail₂ ha₂ (x₂ p)
    have hh := pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans (add_le_add h₁ h₂)) (2*k+2)
    exact hh.trans_eq (by rw [← two_mul, mul_pow])

 

noncomputable def actualTwoSegmentLaw {P : Type} [MeasurableSpace P]
    (μ : Measure P) (n : ℕ) (tail mid pre : List (GaussianStep (FeatureIndex n)))
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) :=
  (μ ⊗ₘ (segmentKernel (uniformWeight n) (finiteFeature n) (mid++tail) pre).comap x hx) ⊗ₘ
    (segmentKernel (uniformWeight n) (finiteFeature n) tail mid).comap
      (fun p : P × (Fin pre.length → FeatureIndex n → ℝ) =>
        forwardEnd pre.length (hierarchyIncrements pre) (x p.1) p.2)
      ((measurable_forwardEnd _ (hierarchyIncrements_measurable pre)).comp
        ((hx.comp measurable_fst).prodMk measurable_snd))

 

theorem eventually_actual_random_later_projection {P : Type} [MeasurableSpace P]
    (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (tail mid pre : List (GaussianStep (FeatureIndex n)))
      (a D : ℝ), 0 < a → 0 < D → D ≤ B → OrderedSteps a (pre++(mid++tail)) →
    ∀ (μ : Measure P) [IsFiniteMeasure μ] (V : P → Fin n → ℝ) (_hV : Measurable V)
      (x : P → FeatureIndex n → ℝ) (hx : Measurable x),
      Integrable (fun p => (projectionEuclideanNorm n (V p))^(2*k+2)) μ →
      (∀ p, AlignedFieldClock (fieldProjectionDirection n (V p)) D pre) →
    (∫ p : (P × (Fin pre.length → FeatureIndex n → ℝ)) × (Fin mid.length → FeatureIndex n → ℝ),
       |∑ i, V p.1.1 i *
          (actualSpinMean n tail (forwardEnd mid.length (hierarchyIncrements mid)
            (forwardEnd pre.length (hierarchyIncrements pre) (x p.1.1) p.1.2) p.2) i -
           actualSpinMean n (mid++tail)
            (forwardEnd pre.length (hierarchyIncrements pre) (x p.1.1) p.1.2) i)|^(2*k+2)
        ∂actualTwoSegmentLaw μ n tail mid pre x hx) ≤
      (projectionLpConstant k*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*D)))^(2*k+2)*
        ∫ p, (projectionEuclideanNorm n (V p))^(2*k+2) ∂μ := by
  filter_upwards [eventually_random_projection_moment (P := P) k B] with n hn
  intro tail mid pre a D ha0 hD hDB ha μ _ V hV x hx hI hc
  have hmid := ha.suffix pre (mid++tail)
  have htail := hmid.suffix mid tail
  have hmark₁ := segmentKernel_markov (uniformWeight_pos n) (finiteFeature n) (mid++tail) pre ha
  have hmark₂ := segmentKernel_markov (uniformWeight_pos n) (finiteFeature n) tail mid hmid
  let κ₁ := (segmentKernel (uniformWeight n) (finiteFeature n) (mid++tail) pre).comap x hx
  let x₁ : P × (Fin pre.length → FeatureIndex n → ℝ) → FeatureIndex n → ℝ :=
    fun p => forwardEnd pre.length (hierarchyIncrements pre) (x p.1) p.2
  have hx₁ : Measurable x₁ := (measurable_forwardEnd _ (hierarchyIncrements_measurable pre)).comp
    ((hx.comp measurable_fst).prodMk measurable_snd)
  let κ₂ := (segmentKernel (uniformWeight n) (finiteFeature n) tail mid).comap x₁ hx₁
  let μ₁ := μ ⊗ₘ κ₁
  let μ₂ := μ₁ ⊗ₘ κ₂
  have hp₁ : MeasurePreserving (Prod.fst : P × (Fin pre.length → FeatureIndex n → ℝ) → P) μ₁ μ :=
    ⟨measurable_fst, Measure.fst_compProd μ κ₁⟩
  have hp₂ : MeasurePreserving (Prod.fst : (P × (Fin pre.length → FeatureIndex n → ℝ)) ×
      (Fin mid.length → FeatureIndex n → ℝ) → P × (Fin pre.length → FeatureIndex n → ℝ)) μ₂ μ₁ :=
    ⟨measurable_fst, Measure.fst_compProd μ₁ κ₂⟩
  have hI₁ : Integrable (fun p : P × (Fin pre.length → FeatureIndex n → ℝ) =>
      (projectionEuclideanNorm n (V p.1))^(2*k+2)) μ₁ :=
    (hp₁.integrable_comp (((projectionEuclideanNorm_measurable n).comp hV).pow_const _).aestronglyMeasurable).mpr hI
  have hI₂ : Integrable (fun p : (P × (Fin pre.length → FeatureIndex n → ℝ)) ×
      (Fin mid.length → FeatureIndex n → ℝ) => (projectionEuclideanNorm n (V p.1.1))^(2*k+2)) μ₂ :=
    (hp₂.integrable_comp ((((projectionEuclideanNorm_measurable n).comp hV).comp measurable_fst).pow_const _).aestronglyMeasurable).mpr hI₁
  have hx₂ : Measurable (fun p : (P × (Fin pre.length → FeatureIndex n → ℝ)) ×
      (Fin mid.length → FeatureIndex n → ℝ) =>
        forwardEnd mid.length (hierarchyIncrements mid) (x₁ p.1) p.2) :=
    (measurable_forwardEnd _ (hierarchyIncrements_measurable mid)).comp
      ((hx₁.comp measurable_fst).prodMk measurable_snd)
  have hi := random_directional_increment_integrable μ₂ n k tail (mid++tail) htail hmid
    (fun p => V p.1.1) (hV.comp (measurable_fst.comp measurable_fst))
    (fun p => forwardEnd mid.length (hierarchyIncrements mid) (x₁ p.1) p.2)
    (fun p => x₁ p.1) hx₂ (hx₁.comp measurable_fst) hI₂
  simp_rw [mul_sub, Finset.sum_sub_distrib,spinProjection_actualSpinMean n _ tail htail,
    spinProjection_actualSpinMean n _ (mid++tail) hmid]
  change (∫ p, |gaussianHierarchyMean (uniformWeight n) (finiteFeature n) (spinProjection n (V p.1.1))
    tail (forwardEnd mid.length (hierarchyIncrements mid) (x₁ p.1) p.2) -
    gaussianHierarchyMean (uniformWeight n) (finiteFeature n) (spinProjection n (V p.1.1))
      (mid++tail) (x₁ p.1)|^(2*k+2) ∂μ₂) ≤ _
  rw [Measure.integral_compProd hi]
  have hcent := random_projection_moment_integrable μ n k (mid++tail) pre ha V hV x hx hI
  calc
    _ ≤ ∫ p, hierarchyCenteredEvenMoment (uniformWeight n) (finiteFeature n) (spinProjection n (V p.1))
        (mid++tail) k (x₁ p) ∂μ₁ := by
      apply integral_mono (hi.integral_compProd) hcent
      intro p
      change (∫ q, _ ∂segmentKernel (uniformWeight n) (finiteFeature n) tail mid (x₁ p)) ≤ _
      rw [segmentKernel_apply (uniformWeight_pos n) (finiteFeature n) tail mid hmid]
      exact integral_segmentLaw_laterProjection_le (uniformWeight_pos n) (finiteFeature n)
        (spinProjection n (V p.1)) tail mid hmid k (x₁ p)
    _ ≤ _ := hn (mid++tail) pre a D ha0 hD hDB ha μ V hV x hx hI hc

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Hierarchy
open scoped Topology NNReal ENNReal BigOperators

theorem eventually_uniform_random_projection_moment
    (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Type) [MeasurableSpace P], ∀ (tail pre : List (GaussianStep (FeatureIndex n)))
      (a D : ℝ), 0 < a → 0 < D → D ≤ B → OrderedSteps a (pre++tail) →
    ∀ (μ : Measure P) [IsFiniteMeasure μ] (V : P → Fin n → ℝ) (_hV : Measurable V)
      (x : P → FeatureIndex n → ℝ) (hx : Measurable x),
      Integrable (fun p => (projectionEuclideanNorm n (V p))^(2*k+2)) μ →
      (∀ p, AlignedFieldClock (fieldProjectionDirection n (V p)) D pre) →
      (∫ p : P × (Fin pre.length → FeatureIndex n → ℝ),
        hierarchyCenteredEvenMoment (uniformWeight n) (finiteFeature n) (spinProjection n (V p.1))
          tail k (forwardEnd pre.length (hierarchyIncrements pre) (x p.1) p.2)
        ∂(μ ⊗ₘ (segmentKernel (uniformWeight n) (finiteFeature n) tail pre).comap x hx)) ≤
      (projectionLpConstant k*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*D)))^(2*k+2)*
        ∫ p, (projectionEuclideanNorm n (V p))^(2*k+2) ∂μ := by
  filter_upwards [eventually_finiteSK_projection k B] with n hn
  intro P _ tail pre a D ha0 hD hDB ha μ _ V hV x hx hI hc
  have hmarkov := segmentKernel_markov (uniformWeight_pos n) (finiteFeature n) tail pre ha
  let κ := (segmentKernel (uniformWeight n) (finiteFeature n) tail pre).comap x hx
  let M : P → ℝ := fun p => ∫ z, hierarchyCenteredEvenMoment (uniformWeight n) (finiteFeature n)
    (spinProjection n (V p)) tail k (forwardEnd pre.length (hierarchyIncrements pre) (x p) z)
      ∂κ p
  have hi := random_projection_moment_integrable μ n k tail pre ha V hV x hx hI
  have hM : Integrable M μ := hi.integral_compProd
  have hb (p : P) : M p ≤
      (projectionLpConstant k*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*D)))^(2*k+2)*
        (projectionEuclideanNorm n (V p))^(2*k+2) := by
    have he : κ p = segmentLaw (uniformWeight n) (finiteFeature n) tail pre (x p) := by
      exact segmentKernel_apply (uniformWeight_pos n) (finiteFeature n) tail pre ha (x p)
    have h0 : 0 ≤ M p := integral_nonneg fun z =>
      hierarchyCenteredEvenMoment_nonneg (uniformWeight_pos n) (finiteFeature n) _ tail
        (ha.suffix pre tail) k _
    have hh := hn (V p) tail pre a D ha0 hD hDB ha (hc p) (x p)
    rw [← he] at hh
    change (M p)^((2*k+2:ℕ)⁻¹:ℝ) ≤ _ at hh
    have hp := pow_le_pow_left₀ (Real.rpow_nonneg h0 _) hh (2*k+2)
    rw [Real.rpow_inv_natCast_pow h0 (by omega : 2*k+2 ≠ 0)] at hp
    exact hp.trans_eq (by rw [← mul_pow]; congr 1; ring)
  rw [Measure.integral_compProd hi, ← integral_const_mul]
  exact integral_mono hM (hI.const_mul _) (fun p => hb p)

end SKFluctuations

end

end OAI
