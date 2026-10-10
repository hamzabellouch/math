import Mathlib
import OAI.Probability.SKFluctuations.ScalarSlopeInvariant

namespace OAI

/-! Actual Conditional Hierarchy. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ProbabilityTheory BigOperators

namespace SKFluctuations.Hierarchy

instance forwardPathNonempty {E S : Type} [Nonempty E] [Nonempty S] :
    (n : ℕ) → Nonempty (ForwardPath E S n)
  | 0 => inferInstanceAs (Nonempty S)
  | n+1 => @instNonemptyProd E (ForwardPath E S n) _ (forwardPathNonempty n)

instance forwardPathStandardBorel {E S : Type} [MeasurableSpace E] [MeasurableSpace S]
    [StandardBorelSpace E] [StandardBorelSpace S] :
    (n : ℕ) → StandardBorelSpace (ForwardPath E S n)
  | 0 => inferInstanceAs (StandardBorelSpace S)
  | n+1 => @StandardBorelSpace.prod E _ (ForwardPath E S n) _ _
      (forwardPathStandardBorel n)

variable {ι S P : Type} [Fintype ι] [Fintype S] [Nonempty S]
  [MeasurableSpace S] [StandardBorelSpace S] [MeasurableSpace P]

 

theorem condExp_prefix_hierarchy {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (μ : Measure P) [IsFiniteMeasure μ]
    (g : P → (ι → ℝ)) (hg : Measurable g) (A : P → S → ℝ)
    (hf : Integrable (fun p : P × ForwardPath (ι → ℝ) S steps.length =>
      A p.1 (ForwardPath.spin steps.length p.2))
      (μ ⊗ₘ (hierarchyPathKernel w φ steps).comap g hg)) :
    (μ ⊗ₘ (hierarchyPathKernel w φ steps).comap g hg)[(fun p : P × ForwardPath (ι → ℝ) S steps.length =>
        A p.1 (ForwardPath.spin steps.length p.2)) |
          (inferInstance : MeasurableSpace P).comap Prod.fst] =ᵐ[
            μ ⊗ₘ (hierarchyPathKernel w φ steps).comap g hg]
      fun p => gaussianHierarchyMean w φ (A p.1) steps (g p.1) := by
  have hmarkov := hierarchyPathKernel_markov hw φ steps ha
  exact (condExp_compProd_first μ ((hierarchyPathKernel w φ steps).comap g hg) _ hf).trans
    (Eventually.of_forall fun p => by
      simp only [Kernel.comap_apply]
      exact integral_hierarchyPathKernel hw φ (A p.1) steps ha (g p.1))

 

theorem condExp_prefix_hierarchy_fixed {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (μ : Measure P) [IsFiniteMeasure μ]
    (g : P → (ι → ℝ)) (hg : Measurable g) (A : S → ℝ) :
    (μ ⊗ₘ (hierarchyPathKernel w φ steps).comap g hg)[(fun p : P × ForwardPath (ι → ℝ) S steps.length =>
        A (ForwardPath.spin steps.length p.2)) |
          (inferInstance : MeasurableSpace P).comap Prod.fst] =ᵐ[
            μ ⊗ₘ (hierarchyPathKernel w φ steps).comap g hg]
      fun p => gaussianHierarchyMean w φ A steps (g p.1) := by
  classical
  have hmarkov := hierarchyPathKernel_markov hw φ steps ha
  apply condExp_prefix_hierarchy hw φ steps ha μ g hg (fun _ => A)
  apply (integrable_const (∑ s, |A s|)).mono'
    (((measurable_of_countable A).comp
      ((ForwardPath.spin_measurable steps.length).comp measurable_snd)).stronglyMeasurable.aestronglyMeasurable)
  exact Eventually.of_forall (fun p => by
    simpa only [Real.norm_eq_abs, Function.comp_apply] using Finset.single_le_sum
      (fun s _ => abs_nonneg (A s)) (Finset.mem_univ (ForwardPath.spin steps.length p.2)))

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set

 

@[instance_reducible] def forwardPrefixSpace (P E S : Type) [MeasurableSpace P] [MeasurableSpace E]
    [MeasurableSpace S] : (n : ℕ) → ℕ → MeasurableSpace (P × ForwardPath E S n)
  | 0, 0 => (inferInstance : MeasurableSpace P).comap Prod.fst
  | 0, _k+1 => inferInstance
  | _n+1, 0 => (inferInstance : MeasurableSpace P).comap Prod.fst
  | n+1, k+1 => (forwardPrefixSpace (P × E) E S n k).comap MeasurableEquiv.prodAssoc.symm

@[simp] theorem forwardPrefixSpace_zero (P E S : Type) [MeasurableSpace P]
    [MeasurableSpace E] [MeasurableSpace S] (n : ℕ) :
    forwardPrefixSpace P E S n 0 = (inferInstance : MeasurableSpace P).comap Prod.fst := by
  cases n <;> rfl

theorem forwardPrefixSpace_le (P E S : Type) [MeasurableSpace P]
    [MeasurableSpace E] [MeasurableSpace S] (n k : ℕ) :
    forwardPrefixSpace P E S n k ≤ (inferInstance : MeasurableSpace (P × ForwardPath E S n)) := by
  induction n generalizing P k with
  | zero =>
    cases k with
    | zero => exact measurable_fst.comap_le
    | succ k => exact le_rfl
  | succ n ih =>
    cases k with
    | zero => exact measurable_fst.comap_le
    | succ k =>
      exact (MeasurableSpace.comap_mono (ih (P × E) k)).trans
        MeasurableEquiv.prodAssoc.symm.measurable.comap_le

theorem forwardPrefixSpace_mono (P E S : Type) [MeasurableSpace P]
    [MeasurableSpace E] [MeasurableSpace S] (n : ℕ) :
    Monotone (forwardPrefixSpace P E S n) := by
  induction n generalizing P with
  | zero =>
    apply monotone_nat_of_le_succ
    intro k
    cases k with
    | zero => exact measurable_fst.comap_le
    | succ k => exact le_rfl
  | succ n ih =>
    apply monotone_nat_of_le_succ
    intro k
    cases k with
    | zero =>
      simp only [forwardPrefixSpace, forwardPrefixSpace_zero]
      rintro s ⟨t,ht,rfl⟩
      exact ⟨Prod.fst ⁻¹' (Prod.fst ⁻¹' t), ⟨Prod.fst ⁻¹' t,measurable_fst ht,rfl⟩,rfl⟩
    | succ k =>
      exact MeasurableSpace.comap_mono (ih (P × E) (Nat.le_succ k))

 

def forwardFiltration (P E S : Type) [MeasurableSpace P] [MeasurableSpace E]
    [MeasurableSpace S] (n : ℕ) : Filtration ℕ (inferInstance : MeasurableSpace (P × ForwardPath E S n)) where
  seq := forwardPrefixSpace P E S n
  mono' := forwardPrefixSpace_mono P E S n
  le' := forwardPrefixSpace_le P E S n

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

theorem kernel_compProd_comap {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D] (κ : Kernel A B) (η : Kernel (A × B) C)
    [IsSFiniteKernel κ] [IsSFiniteKernel η] (f : D → A) (hf : Measurable f) :
    (κ ⊗ₖ η).comap f hf = κ.comap f hf ⊗ₖ
      η.comap (fun p : D × B => (f p.1,p.2)) ((hf.comp measurable_fst).prodMk measurable_snd) := by
  ext x s hs
  simp only [Kernel.comap_apply,Kernel.compProd_apply hs]

variable {ι S P : Type} [Fintype ι] [Fintype S] [Nonempty S]
  [MeasurableSpace S] [StandardBorelSpace S] [MeasurableSpace P]

 

theorem hierarchyPathLaw_cons {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (m : ℝ) (q : ι → ℝ≥0)
    (tail : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a ((m,q)::tail))
    (μ : Measure P) [IsFiniteMeasure μ] (x : P → ι → ℝ) (hx : Measurable x) :
    (μ ⊗ₘ (hierarchyPathKernel w φ ((m,q)::tail)).comap x hx).map
      MeasurableEquiv.prodAssoc.symm =
      (μ ⊗ₘ (plantedStepKernel w φ m q tail).comap x hx) ⊗ₘ
        (hierarchyPathKernel w φ tail).comap (fun p : P × (ι → ℝ) => x p.1+p.2)
          ((hx.comp measurable_fst).add measurable_snd) := by
  have := plantedStepKernel_markov hw φ m q tail ha
  have := hierarchyPathKernel_markov hw φ tail ha.2.2.2
  change (μ ⊗ₘ ((plantedStepKernel w φ m q tail ⊗ₖ
    (hierarchyPathKernel w φ tail).comap (fun p => p.1+p.2)
      (measurable_fst.add measurable_snd)).comap x hx)).map MeasurableEquiv.prodAssoc.symm = _
  rw [kernel_compProd_comap, Measure.compProd_assoc]
  congr 1

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set

 

theorem condExp_measurableEquiv {A B F : Type*} (m : MeasurableSpace B)
    [mA : MeasurableSpace A] [mB : MeasurableSpace B]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (e : A ≃ᵐ B) (μ : Measure A) [IsFiniteMeasure μ]
    (hm : m ≤ mB) (f : B → F)
    (hf : Integrable f (μ.map e)) :
    μ[(fun a => f (e a)) | m.comap e] =ᵐ[μ]
      fun a => ((μ.map e)[f | m]) (e a) := by
  have hle : m.comap e ≤ mA :=
    (MeasurableSpace.comap_mono hm).trans e.measurable.comap_le
  have hi : Integrable (fun a => ((μ.map e)[f | m]) (e a)) μ :=
    e.measurableEmbedding.integrable_map_iff.mp integrable_condExp
  apply (ae_eq_condExp_of_forall_setIntegral_eq hle
    (e.measurableEmbedding.integrable_map_iff.mp hf) (fun s _ _ => hi.integrableOn) ?_ ?_).symm
  · rintro s ⟨t,ht,rfl⟩ _
    rw [← setIntegral_map_equiv e]
    exact (setIntegral_condExp hm hf ht).trans (setIntegral_map_equiv e f t)
  · exact (stronglyMeasurable_condExp.comp_measurable
      (show Measurable[m.comap e,m] e from comap_measurable e)).aestronglyMeasurable

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

def hierarchyMeanPath (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ) (A : S → ℝ) :
    (steps : List (GaussianStep ι)) → {P : Type} → (P → ι → ℝ) → ℕ →
      (P × ForwardPath (ι → ℝ) S steps.length) → ℝ
  | [], _, x, 0 => fun p => gaussianHierarchyMean w φ A [] (x p.1)
  | [], _, _x, _k+1 => fun p => A p.2
  | _st::tail, _, x, 0 => fun p => gaussianHierarchyMean w φ A (_st::tail) (x p.1)
  | _st::tail, _, x, k+1 => fun p =>
      hierarchyMeanPath w φ A tail (fun q => x q.1+q.2) k ((p.1,p.2.1),p.2.2)

variable [MeasurableSpace S] [StandardBorelSpace S]

 

theorem hierarchyMeanPath_measurable {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (A : S → ℝ)
    (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps)
    {P : Type} [MeasurableSpace P] (x : P → ι → ℝ) (hx : Measurable x) (k : ℕ) :
    Measurable[forwardPrefixSpace P (ι → ℝ) S steps.length k]
      (hierarchyMeanPath w φ A steps x k) := by
  induction steps generalizing P a k with
  | nil =>
    cases k with
    | zero =>
      exact ((gaussianHierarchyMean_smooth hw φ A [] ha 0).continuous.measurable.comp hx).comp
        (comap_measurable Prod.fst)
    | succ k => exact (measurable_of_countable A).comp measurable_snd
  | cons st tail ih =>
    cases k with
    | zero =>
      exact ((gaussianHierarchyMean_smooth hw φ A (st::tail) ha 0).continuous.measurable.comp hx).comp
        (comap_measurable Prod.fst)
    | succ k =>
      exact (ih ha.2.2.2 (fun q : P × (ι → ℝ) => x q.1+q.2)
        ((hx.comp measurable_fst).add measurable_snd) k).comp
        (comap_measurable MeasurableEquiv.prodAssoc.symm)

theorem integrable_terminal_hierarchyPathLaw {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (A : S → ℝ)
    (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P → ι → ℝ) (hx : Measurable x) :
    Integrable (fun p : P × ForwardPath (ι → ℝ) S steps.length =>
      A (ForwardPath.spin steps.length p.2))
      (μ ⊗ₘ (hierarchyPathKernel w φ steps).comap x hx) := by
  have := hierarchyPathKernel_markov hw φ steps ha
  apply (integrable_const (∑ s, |A s|)).mono'
    (((measurable_of_countable A).comp
      ((ForwardPath.spin_measurable steps.length).comp measurable_snd)).stronglyMeasurable.aestronglyMeasurable)
  exact Eventually.of_forall fun p =>
    Finset.single_le_sum (fun s _ => abs_nonneg (A s)) (Finset.mem_univ (ForwardPath.spin steps.length p.2))

 

theorem condExp_hierarchyMeanPath {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (A : S → ℝ)
    (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P → ι → ℝ) (hx : Measurable x) (k : ℕ) :
    (μ ⊗ₘ (hierarchyPathKernel w φ steps).comap x hx)[
      (fun p : P × ForwardPath (ι → ℝ) S steps.length => A (ForwardPath.spin steps.length p.2)) |
       forwardPrefixSpace P (ι → ℝ) S steps.length k] =ᵐ[
        μ ⊗ₘ (hierarchyPathKernel w φ steps).comap x hx]
      hierarchyMeanPath w φ A steps x k := by
  induction steps generalizing P a k with
  | nil =>
    cases k with
    | zero => exact condExp_prefix_hierarchy_fixed hw φ [] ha μ x hx A
    | succ k =>
      have := hierarchyPathKernel_markov hw φ [] ha
      exact Eventually.of_forall fun p => congrFun (condExp_of_stronglyMeasurable
        (forwardPrefixSpace_le P (ι → ℝ) S 0 (k+1))
        ((measurable_of_countable A).comp measurable_snd).stronglyMeasurable
        (integrable_terminal_hierarchyPathLaw hw φ A [] ha μ x hx)) p
  | cons st tail ih =>
    rcases st with ⟨m,q⟩
    cases k with
    | zero => exact condExp_prefix_hierarchy_fixed hw φ ((m,q)::tail) ha μ x hx A
    | succ k =>
      have := hierarchyPathKernel_markov hw φ ((m,q)::tail) ha
      have := plantedStepKernel_markov hw φ m q tail ha
      let ν := μ ⊗ₘ (hierarchyPathKernel w φ ((m,q)::tail)).comap x hx
      let μ' := μ ⊗ₘ (plantedStepKernel w φ m q tail).comap x hx
      let x' : P × (ι → ℝ) → ι → ℝ := fun p => x p.1+p.2
      have hx' : Measurable x' := (hx.comp measurable_fst).add measurable_snd
      let e : (P × ForwardPath (ι → ℝ) S (((m,q)::tail).length)) ≃ᵐ
          ((P × (ι → ℝ)) × ForwardPath (ι → ℝ) S tail.length) := MeasurableEquiv.prodAssoc.symm
      have hmap : ν.map e = μ' ⊗ₘ (hierarchyPathKernel w φ tail).comap x' hx' :=
        hierarchyPathLaw_cons hw φ m q tail ha μ x hx
      have hI : Integrable (fun p : (P × (ι → ℝ)) × ForwardPath (ι → ℝ) S tail.length =>
          A (ForwardPath.spin tail.length p.2)) (ν.map e) := by
        rw [hmap]
        exact integrable_terminal_hierarchyPathLaw hw φ A tail ha.2.2.2 μ' x' hx'
      have he := condExp_measurableEquiv (forwardPrefixSpace (P × (ι → ℝ)) (ι → ℝ) S tail.length k)
        e ν (forwardPrefixSpace_le _ _ _ _ _) _ hI
      have ht := ih ha.2.2.2 μ' x' hx' k
      rw [← hmap] at ht
      exact he.trans (ae_of_ae_map e.measurable.aemeasurable ht)

 

theorem hierarchyMeanPath_martingale {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (A : S → ℝ)
    (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P → ι → ℝ) (hx : Measurable x) :
    Martingale (hierarchyMeanPath w φ A steps x)
      (forwardFiltration P (ι → ℝ) S steps.length)
      (μ ⊗ₘ (hierarchyPathKernel w φ steps).comap x hx) := by
  have := hierarchyPathKernel_markov hw φ steps ha
  exact (martingale_condExp
    (fun p : P × ForwardPath (ι → ℝ) S steps.length => A (ForwardPath.spin steps.length p.2))
    (forwardFiltration P (ι → ℝ) S steps.length) _).congr
    (fun k => (hierarchyMeanPath_measurable hw φ A steps ha x hx k).stronglyMeasurable)
    (condExp_hierarchyMeanPath hw φ A steps ha μ x hx)

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal ENNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

noncomputable def segmentKernel (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (tail pre : List (GaussianStep ι)) : Kernel (ι → ℝ) (Fin pre.length → (ι → ℝ)) :=
  forwardKernel pre.length (fun _ => standardDrivers ι) (hierarchyIncrements pre)
    (segmentTransitions w φ tail pre)

theorem segmentKernel_apply {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (tail pre : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a (pre++tail)) (x : ι → ℝ) :
    segmentKernel w φ tail pre x = segmentLaw w φ tail pre x :=
  forwardKernel_apply _ _ (hierarchyIncrements_measurable pre)
    (segmentTransitions_measurable hw φ tail pre ha) x

theorem segmentKernel_markov {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (tail pre : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a (pre++tail)) :
    IsMarkovKernel (segmentKernel w φ tail pre) :=
  forwardKernel_isMarkov _ _ (hierarchyIncrements_measurable pre)
    (segmentTransitions_measurable hw φ tail pre ha)
    (segmentTransitions_normalized hw φ tail pre ha)

 

theorem hierarchyCenteredEvenMoment_measurable {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (k : ℕ) :
    Measurable (fun p : (S → ℝ) × (ι → ℝ) =>
      hierarchyCenteredEvenMoment w φ p.1 steps k p.2) := by
  classical
  have hm : Measurable (fun p : (S → ℝ) × (ι → ℝ) =>
      gaussianHierarchyMean w φ p.1 steps p.2) := by
    simp_rw [gaussianHierarchyMean_atoms hw φ steps ha]
    apply Finset.measurable_sum Finset.univ
    intro s _
    exact ((measurable_pi_apply s).comp measurable_fst).mul
      ((hierarchyAtom_smooth hw φ steps ha s 0).continuous.measurable.comp measurable_snd)
  apply Finset.measurable_sum Finset.univ
  intro s _
  exact ((hierarchyAtom_smooth hw φ steps ha s 0).continuous.measurable.comp
    measurable_snd).mul ((((measurable_pi_apply s).comp measurable_fst).sub hm).abs.pow_const _)

end SKFluctuations.Hierarchy

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Hierarchy
open scoped Topology NNReal ENNReal BigOperators

 theorem spinProjection_measurable (n : ℕ) : Measurable (fun V : Fin n → ℝ => spinProjection n V) := by
  apply Measurable.of_eval
  intro σ
  apply Measurable.div_const
  apply Finset.measurable_sum Finset.univ
  intro i _
  exact (measurable_pi_apply i).mul_const _

 theorem projectionEuclideanNorm_measurable (n : ℕ) : Measurable (projectionEuclideanNorm n) := by
  exact (Finset.measurable_sum Finset.univ fun i _ => (measurable_pi_apply i).pow_const 2).sqrt

 

theorem random_projection_moment_integrable {P : Type*} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (n k : ℕ)
    (tail pre : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a (pre++tail)) (V : P → Fin n → ℝ) (hV : Measurable V)
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
    (hI : Integrable (fun p => (projectionEuclideanNorm n (V p))^(2*k+2)) μ) :
    Integrable (fun p : P × (Fin pre.length → FeatureIndex n → ℝ) =>
      hierarchyCenteredEvenMoment (uniformWeight n) (finiteFeature n) (spinProjection n (V p.1))
        tail k (forwardEnd pre.length (hierarchyIncrements pre) (x p.1) p.2))
      (μ ⊗ₘ (segmentKernel (uniformWeight n) (finiteFeature n) tail pre).comap x hx) := by
  let κ := (segmentKernel (uniformWeight n) (finiteFeature n) tail pre).comap x hx
  have hmarkov := segmentKernel_markov (uniformWeight_pos n) (finiteFeature n) tail pre ha
  have hf : Measurable (fun p : P × (Fin pre.length → FeatureIndex n → ℝ) =>
      hierarchyCenteredEvenMoment (uniformWeight n) (finiteFeature n) (spinProjection n (V p.1))
        tail k (forwardEnd pre.length (hierarchyIncrements pre) (x p.1) p.2)) :=
    (hierarchyCenteredEvenMoment_measurable (uniformWeight_pos n) (finiteFeature n) tail
      (ha.suffix pre tail) k).comp
      (((spinProjection_measurable n).comp (hV.comp measurable_fst)).prodMk
        ((measurable_forwardEnd _ (hierarchyIncrements_measurable pre)).comp
          ((hx.comp measurable_fst).prodMk measurable_snd)))
  have hfst : MeasurePreserving (Prod.fst : P × (Fin pre.length → FeatureIndex n → ℝ) → P)
      (μ ⊗ₘ κ) μ := ⟨measurable_fst, Measure.fst_compProd μ κ⟩
  have hb : Integrable (fun p : P × (Fin pre.length → FeatureIndex n → ℝ) =>
      (2:ℝ)^(2*k+2)*(projectionEuclideanNorm n (V p.1))^(2*k+2)) (μ ⊗ₘ κ) :=
    (hfst.integrable_comp (((projectionEuclideanNorm_measurable n).comp hV |>.pow_const (2*k+2)).const_mul ((2:ℝ)^(2*k+2))).aestronglyMeasurable).mpr
      (hI.const_mul _)
  apply hb.mono' hf.aestronglyMeasurable
  exact Eventually.of_forall fun p => by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (hierarchyCenteredEvenMoment_nonneg (uniformWeight_pos n) (finiteFeature n) _ tail
        (ha.suffix pre tail) k _)]
    simpa only [mul_pow] using hierarchyCenteredEvenMoment_bound (uniformWeight_pos n)
      (finiteFeature n) (spinProjection n (V p.1)) (spinProjection_abs_le n (V p.1))
      tail (ha.suffix pre tail) k _

 

theorem eventually_random_projection_moment {P : Type*} [MeasurableSpace P]
    (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (tail pre : List (GaussianStep (FeatureIndex n)))
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
  intro tail pre a D ha0 hD hDB ha μ _ V hV x hx hI hc
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

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal ENNReal BigOperators
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S]

theorem integral_centered_hierarchyPathKernel {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (Y : S → ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (k : ℕ) (x : ι → ℝ) :
    (∫ p, |Y (ForwardPath.spin steps.length p) - gaussianHierarchyMean w φ Y steps x|^(2*k+2)
      ∂hierarchyPathKernel w φ steps x) = hierarchyCenteredEvenMoment w φ Y steps k x := by
  rw [integral_hierarchyPathKernel hw φ (fun s => |Y s-gaussianHierarchyMean w φ Y steps x|^(2*k+2)) steps ha x,
    gaussianHierarchyMean_atoms hw φ steps ha]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
 
theorem gaussianHierarchyMean_measurable_joint {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) :
    Measurable (fun p : (S → ℝ) × (ι → ℝ) => gaussianHierarchyMean w φ p.1 steps p.2) := by
  classical
  simp_rw [gaussianHierarchyMean_atoms hw φ steps ha]
  exact Finset.measurable_sum Finset.univ fun s _ =>
    ((measurable_pi_apply s).comp measurable_fst).mul
      ((hierarchyAtom_smooth hw φ steps ha s 0).continuous.measurable.comp measurable_snd)

end SKFluctuations.Hierarchy

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Hierarchy
open scoped Topology NNReal ENNReal BigOperators

 

theorem random_terminal_residual_integral {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (n k : ℕ)
    (tail : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a tail)
    (V : P → Fin n → ℝ) (hV : Measurable V)
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
    (hI : Integrable (fun p => (projectionEuclideanNorm n (V p))^(2*k+2)) μ) :
    (∫ p : P × ForwardPath (FeatureIndex n → ℝ) (Spin n) tail.length,
       |spinProjection n (V p.1) (ForwardPath.spin tail.length p.2) -
         gaussianHierarchyMean (uniformWeight n) (finiteFeature n) (spinProjection n (V p.1)) tail
           (x p.1)|^(2*k+2)
       ∂(μ ⊗ₘ (hierarchyPathKernel (uniformWeight n) (finiteFeature n) tail).comap x hx)) =
      ∫ p, hierarchyCenteredEvenMoment (uniformWeight n) (finiteFeature n)
        (spinProjection n (V p)) tail k (x p) ∂μ := by
  classical
  have hm := hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) tail ha
  let κ := (hierarchyPathKernel (uniformWeight n) (finiteFeature n) tail).comap x hx
  have hfst : MeasurePreserving (Prod.fst : P × ForwardPath (FeatureIndex n → ℝ) (Spin n) tail.length → P)
      (μ ⊗ₘ κ) μ := ⟨measurable_fst, Measure.fst_compProd μ κ⟩
  have hb : Integrable (fun p : P × ForwardPath (FeatureIndex n → ℝ) (Spin n) tail.length =>
      (2:ℝ)^(2*k+2)*(projectionEuclideanNorm n (V p.1))^(2*k+2)) (μ ⊗ₘ κ) :=
    (hfst.integrable_comp (((projectionEuclideanNorm_measurable n).comp hV |>.pow_const (2*k+2)).const_mul ((2:ℝ)^(2*k+2))).aestronglyMeasurable).mpr
      (hI.const_mul _)
  have hy : Measurable (fun p : P × ForwardPath (FeatureIndex n → ℝ) (Spin n) tail.length =>
      spinProjection n (V p.1) (ForwardPath.spin tail.length p.2)) :=
    (show Measurable (fun p : (Spin n → ℝ) × Spin n => p.1 p.2) from
      measurable_from_prod_countable_left fun σ => measurable_pi_apply σ).comp
        (((spinProjection_measurable n).comp (hV.comp measurable_fst)).prodMk
      ((ForwardPath.spin_measurable tail.length).comp measurable_snd))
  have hc : Measurable (fun p : P × ForwardPath (FeatureIndex n → ℝ) (Spin n) tail.length =>
      gaussianHierarchyMean (uniformWeight n) (finiteFeature n) (spinProjection n (V p.1)) tail (x p.1)) :=
    (gaussianHierarchyMean_measurable_joint (uniformWeight_pos n) (finiteFeature n) tail ha).comp
      (((spinProjection_measurable n).comp (hV.comp measurable_fst)).prodMk (hx.comp measurable_fst))
  have hi : Integrable (fun p : P × ForwardPath (FeatureIndex n → ℝ) (Spin n) tail.length =>
      |spinProjection n (V p.1) (ForwardPath.spin tail.length p.2) -
        gaussianHierarchyMean (uniformWeight n) (finiteFeature n) (spinProjection n (V p.1)) tail (x p.1)|^(2*k+2)) (μ ⊗ₘ κ) := by
    apply hb.mono' ((hy.sub hc).abs.pow_const _).aestronglyMeasurable
    exact Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
      have hm := gaussianHierarchyMean_abs_le (uniformWeight_pos n) (finiteFeature n)
        (spinProjection_abs_le n (V p.1)) tail ha (x p.1)
      have h := (abs_sub _ _).trans (add_le_add (spinProjection_abs_le n (V p.1) (ForwardPath.spin tail.length p.2)) hm)
      have hp := pow_le_pow_left₀ (abs_nonneg _) h (2*k+2)
      exact hp.trans_eq (by rw [← two_mul, mul_pow])
  rw [Measure.integral_compProd hi]
  apply integral_congr_ae
  exact Eventually.of_forall fun p => integral_centered_hierarchyPathKernel
    (uniformWeight_pos n) (finiteFeature n) (spinProjection n (V p)) tail ha k (x p)

 

noncomputable def actualSegmentTailLaw {P : Type} [MeasurableSpace P]
    (μ : Measure P) (n : ℕ) (tail pre : List (GaussianStep (FeatureIndex n)))
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) :=
  (μ ⊗ₘ (segmentKernel (uniformWeight n) (finiteFeature n) tail pre).comap x hx) ⊗ₘ
    (hierarchyPathKernel (uniformWeight n) (finiteFeature n) tail).comap
      (fun p : P × (Fin pre.length → FeatureIndex n → ℝ) =>
        forwardEnd pre.length (hierarchyIncrements pre) (x p.1) p.2)
      ((measurable_forwardEnd _ (hierarchyIncrements_measurable pre)).comp
        ((hx.comp measurable_fst).prodMk measurable_snd))

 

theorem eventually_actual_random_terminal_projection {P : Type} [MeasurableSpace P]
    (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (tail pre : List (GaussianStep (FeatureIndex n)))
      (a D : ℝ), 0 < a → 0 < D → D ≤ B → OrderedSteps a (pre++tail) →
    ∀ (μ : Measure P) [IsFiniteMeasure μ] (V : P → Fin n → ℝ) (_hV : Measurable V)
      (x : P → FeatureIndex n → ℝ) (hx : Measurable x),
      Integrable (fun p => (projectionEuclideanNorm n (V p))^(2*k+2)) μ →
      (∀ p, AlignedFieldClock (fieldProjectionDirection n (V p)) D pre) →
    (∫ p : (P × (Fin pre.length → FeatureIndex n → ℝ)) ×
        ForwardPath (FeatureIndex n → ℝ) (Spin n) tail.length,
      |spinProjection n (V p.1.1) (ForwardPath.spin tail.length p.2) -
        gaussianHierarchyMean (uniformWeight n) (finiteFeature n) (spinProjection n (V p.1.1))
          tail (forwardEnd pre.length (hierarchyIncrements pre) (x p.1.1) p.1.2)|^(2*k+2)
        ∂actualSegmentTailLaw μ n tail pre x hx) ≤
      (projectionLpConstant k*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*D)))^(2*k+2)*
        ∫ p, (projectionEuclideanNorm n (V p))^(2*k+2) ∂μ := by
  filter_upwards [eventually_random_projection_moment (P := P) k B] with n hn
  intro tail pre a D ha0 hD hDB ha μ _ V hV x hx hI hc
  have hmarkov := segmentKernel_markov (uniformWeight_pos n) (finiteFeature n) tail pre ha
  let κ := (segmentKernel (uniformWeight n) (finiteFeature n) tail pre).comap x hx
  have hfst : MeasurePreserving (Prod.fst : P × (Fin pre.length → FeatureIndex n → ℝ) → P)
      (μ ⊗ₘ κ) μ := ⟨measurable_fst, Measure.fst_compProd μ κ⟩
  have hI' : Integrable (fun p : P × (Fin pre.length → FeatureIndex n → ℝ) =>
      (projectionEuclideanNorm n (V p.1))^(2*k+2)) (μ ⊗ₘ κ) :=
    (hfst.integrable_comp (((projectionEuclideanNorm_measurable n).comp hV).pow_const _).aestronglyMeasurable).mpr hI
  erw [random_terminal_residual_integral (μ ⊗ₘ κ) n k tail (ha.suffix pre tail)
    (fun p => V p.1) (hV.comp measurable_fst)
    (fun p => forwardEnd pre.length (hierarchyIncrements pre) (x p.1) p.2)
    ((measurable_forwardEnd _ (hierarchyIncrements_measurable pre)).comp
      ((hx.comp measurable_fst).prodMk measurable_snd)) hI']
  exact hn tail pre a D ha0 hD hDB ha μ V hV x hx hI hc

end SKFluctuations

end

end OAI
