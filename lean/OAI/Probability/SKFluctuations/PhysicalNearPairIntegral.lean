import Mathlib
import OAI.Probability.SKFluctuations.PhysicalFarPair

namespace OAI

/-! Physical Near Pair Integral. -/

noncomputable section


namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators RealInnerProductSpace

 theorem physicalNearLayerSquare_nonneg (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {P : Type} (x : P → FeatureIndex n → ℝ) (i j : ℕ)
    (p : P × ForwardPath (FeatureIndex n → ℝ) (Spin n) steps.length) :
    0 ≤ physicalNearLayerSquare n steps x i j p :=
  conditionalPathAverage_nonneg _ _ _ _ _ (fun _ => sq_nonneg _) p

 theorem physicalBlockSquare_nonneg (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {P : Type} (x : P → FeatureIndex n → ℝ) (i j : ℕ)
    (p : P × ForwardPath (FeatureIndex n → ℝ) (Spin n) steps.length) :
    0 ≤ physicalBlockSquare n steps x i j p :=
  conditionalPathAverage_nonneg _ _ _ _ _ (fun _ => sq_nonneg _) p

 theorem physicalNearLayerSquare_measurable (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {a : ℝ} (ha : OrderedSteps a steps) {P : Type} [MeasurableSpace P]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (i j : ℕ) :
    Measurable (physicalNearLayerSquare n steps x i j) := by
  let Ω := P × ForwardPath (FeatureIndex n → ℝ) (Spin n) steps.length
  let d : Ω → EuclideanSpace ℝ (Fin n) := fun p =>
    actualSpinPath n steps x j p-actualSpinPath n steps x i p
  have hd : Measurable d := (actualSpinPath_measurable n steps ha x hx j).sub
    (actualSpinPath_measurable n steps ha x hx i)
  have hF : Measurable (fun p : Ω × Ω => (inner ℝ (d p.1) (d p.2))^2) :=
    ((hd.comp measurable_fst).inner (hd.comp measurable_snd)).pow_const 2
  have h : Measurable (fun p : Ω × Ω =>
      conditionalPathAverage (uniformWeight n) (finiteFeature n) steps x i
        (fun q => (inner ℝ (d p.1) (d q))^2) p.2) :=
    conditionalPathAverage_parameter_measurable (uniformWeight_pos n)
      (finiteFeature n) steps ha (P := P) (A := Ω) x hx i hF
  change Measurable (fun p : Ω =>
      conditionalPathAverage (uniformWeight n) (finiteFeature n) steps x i
        (fun q => (inner ℝ (d p) (d q))^2) p)
  have hdiag : Measurable (fun p : Ω => (p,p)) := measurable_id.prodMk measurable_id
  have hh := h.comp hdiag
  exact hh

 theorem physicalNearLayerSquare_le_runningMax (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps)
    {P : Type} [MeasurableSpace P] (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
    {i j N : ℕ} (hi : i ≤ N) (hj : j ≤ N)
    (p : P × ForwardPath (FeatureIndex n → ℝ) (Spin n) steps.length) :
    physicalNearLayerSquare n steps x i j p ≤
      4*runningMax (fun k => ‖actualSpinPath n steps x k p‖^2) N*
        physicalBlockSquare n steps x i j p := by
  have h0 := physicalBlockSquare_nonneg n steps x i j p
  have hi' := (runningMax_self_le (fun k => ‖actualSpinPath n steps x k p‖^2) i).trans
    (runningMax_monotone _ hi)
  have hj' := (runningMax_self_le (fun k => ‖actualSpinPath n steps x k p‖^2) j).trans
    (runningMax_monotone _ hj)
  apply (physicalNearLayerSquare_le n steps ha x hx i j p).trans
  apply mul_le_mul_of_nonneg_right _ h0
  have hs := norm_sub_le (actualSpinPath n steps x j p) (actualSpinPath n steps x i p)
  have hn := norm_nonneg (actualSpinPath n steps x j p-actualSpinPath n steps x i p)
  have hn1 := norm_nonneg (actualSpinPath n steps x j p)
  have hn2 := norm_nonneg (actualSpinPath n steps x i p)
  nlinarith [sq_nonneg (‖actualSpinPath n steps x j p‖-‖actualSpinPath n steps x i p‖)]

end SKFluctuations

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 theorem physicalBlockSquare_le_four (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {a : ℝ} (ha : OrderedSteps a steps) {P : Type} [MeasurableSpace P]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (i j : ℕ)
    (p : P × ForwardPath (FeatureIndex n → ℝ) (Spin n) steps.length) :
    physicalBlockSquare n steps x i j p ≤ 4 := by
  let d := fun q => actualSpinPath n steps x j q-actualSpinPath n steps x i q
  have hm : Measurable d := (actualSpinPath_measurable n steps ha x hx j).sub
    (actualSpinPath_measurable n steps ha x hx i)
  have hbound q : ‖d q‖^2 ≤ 4 := by
    have hn : ‖d q‖ ≤ 2 := (norm_sub_le _ _).trans (by
      linarith [actualSpinPath_norm_le n steps ha x j q,actualSpinPath_norm_le n steps ha x i q])
    nlinarith [norm_nonneg (d q)]
  have hh := conditionalPathAverage_mono_bounded (uniformWeight_pos n) (finiteFeature n)
    steps ha x i (hm.norm.pow_const 2) measurable_const (R := 4)
    (fun q => by rw [abs_of_nonneg (sq_nonneg _)]; exact hbound q)
    (fun _ => by norm_num) hbound p
  rw [conditionalPathAverage_const (uniformWeight_pos n) (finiteFeature n) steps ha] at hh
  exact hh

 theorem physicalBlockSquare_joint (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {a : ℝ} (ha : OrderedSteps a steps) {P Ξ : Type} [MeasurableSpace P] [MeasurableSpace Ξ]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
    {i j : Ξ → ℕ} (hi : Measurable i) (hj : Measurable j) :
    Measurable (fun q : Ξ × (P × ForwardPath (FeatureIndex n → ℝ) (Spin n) steps.length) =>
      physicalBlockSquare n steps x (i q.1) (j q.1) q.2) := by
  have hm : Measurable (fun q : (ℕ × ℕ) ×
      (P × ForwardPath (FeatureIndex n → ℝ) (Spin n) steps.length) =>
        physicalBlockSquare n steps x q.1.1 q.1.2 q.2) :=
    measurable_from_prod_countable_right fun k => physicalBlockSquare_measurable n steps ha x hx k.1 k.2
  exact hm.comp (((hi.prodMk hj).comp measurable_fst).prodMk measurable_snd)

 def physicalNearRadiusIntegral (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {P : Type} (x : P → FeatureIndex n → ℝ) (τ : ℝ → ℕ) (a b η : ℝ)
    (p : P × ForwardPath (FeatureIndex n → ℝ) (Spin n) steps.length) : ℝ :=
  ∫ s in a..b, physicalNearLayerSquare n steps x (τ s) (τ (s+η)) p

 theorem physicalNearRadiusIntegral_nonneg (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {P : Type} (x : P → FeatureIndex n → ℝ) (τ : ℝ → ℕ) {a b : ℝ} (hab : a ≤ b) (η : ℝ)
    (p : P × ForwardPath (FeatureIndex n → ℝ) (Spin n) steps.length) :
    0 ≤ physicalNearRadiusIntegral n steps x τ a b η p := by
  unfold physicalNearRadiusIntegral
  rw [intervalIntegral.integral_of_le hab]
  exact integral_nonneg fun s => physicalNearLayerSquare_nonneg n steps x _ _ p

 theorem physicalRadiusSquareIntegral_measurable (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {c : ℝ} (hc : OrderedSteps c steps) {P : Type} [MeasurableSpace P]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) {τ : ℝ → ℕ} (hτ : Monotone τ)
    (a b η : ℝ) : Measurable (physicalRadiusSquareIntegral n steps x τ a b η) := by
  have h := physicalBlockSquare_joint n steps hc x hx hτ.measurable
    (hτ.measurable.comp (measurable_id.add_const η))
  unfold physicalRadiusSquareIntegral intervalIntegral
  exact ((h.comp measurable_swap).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc a b))).measurable.sub
    ((h.comp measurable_swap).stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Ioc b a))).measurable

 theorem physicalRadiusSquareIntegral_bound (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {c : ℝ} (hc : OrderedSteps c steps) {P : Type} [MeasurableSpace P]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (τ : ℝ → ℕ) (a b η : ℝ)
    (p : P × ForwardPath (FeatureIndex n → ℝ) (Spin n) steps.length) :
    ‖physicalRadiusSquareIntegral n steps x τ a b η p‖ ≤ 4*|b-a| := by
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro s _
  rw [Real.norm_eq_abs,abs_of_nonneg (physicalBlockSquare_nonneg n steps x _ _ p)]
  exact physicalBlockSquare_le_four n steps hc x hx _ _ p

 theorem physicalNearRadiusIntegral_le (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {c : ℝ} (hc : OrderedSteps c steps) {P : Type} [MeasurableSpace P]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) {τ : ℝ → ℕ} (hτ : Monotone τ)
    {a b η : ℝ} (hab : a ≤ b) (hη : 0 ≤ η)
    (p : P × ForwardPath (FeatureIndex n → ℝ) (Spin n) steps.length) :
    physicalNearRadiusIntegral n steps x τ a b η p ≤
      4*runningMax (fun k => ‖actualSpinPath n steps x k p‖^2) (τ (b+η))*
        physicalRadiusSquareIntegral n steps x τ a b η p := by
  let M := runningMax (fun k => ‖actualSpinPath n steps x k p‖^2) (τ (b+η))
  have hM : 0 ≤ M := runningMax_nonneg (fun _ => sq_nonneg _) _
  have hq : Measurable (fun s => physicalBlockSquare n steps x (τ s) (τ (s+η)) p) := by
    have hh := physicalBlockSquare_joint n steps hc x hx hτ.measurable
      (hτ.measurable.comp (measurable_id.add_const η))
    exact hh.comp (measurable_id.prodMk measurable_const)
  have hqi : Integrable (fun s => physicalBlockSquare n steps x (τ s) (τ (s+η)) p)
      (volume.restrict (Ioc a b)) := by
    apply Integrable.of_bound hq.aestronglyMeasurable 4
    exact Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs,abs_of_nonneg (physicalBlockSquare_nonneg n steps x _ _ p)]
      exact physicalBlockSquare_le_four n steps hc x hx _ _ p
  unfold physicalNearRadiusIntegral physicalRadiusSquareIntegral
  rw [intervalIntegral.integral_of_le hab,intervalIntegral.integral_of_le hab,← integral_const_mul]
  apply integral_mono_of_nonneg (Eventually.of_forall fun s =>
    physicalNearLayerSquare_nonneg n steps x _ _ p) (hqi.const_mul (4*M))
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  exact physicalNearLayerSquare_le_runningMax n steps hc x hx
    (hτ (by linarith [hs.2])) (hτ (by linarith [hs.2])) p

 theorem physicalRadiusSquareIntegral_nonneg (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {P : Type} (x : P → FeatureIndex n → ℝ) (τ : ℝ → ℕ) {a b : ℝ} (hab : a ≤ b) (η : ℝ)
    (p : P × ForwardPath (FeatureIndex n → ℝ) (Spin n) steps.length) :
    0 ≤ physicalRadiusSquareIntegral n steps x τ a b η p := by
  unfold physicalRadiusSquareIntegral
  rw [intervalIntegral.integral_of_le hab]
  exact integral_nonneg fun s => physicalBlockSquare_nonneg n steps x _ _ p

 theorem physicalNearRadiusIntegral_Lp (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {c : ℝ} (hc : OrderedSteps c steps) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
    {τ : ℝ → ℕ} (hτ : Monotone τ) {a b η : ℝ} (hab : a ≤ b) (hη : 0 < η)
    {p : ℕ} (hp : 0 < p) :
    (∫ q, (physicalNearRadiusIntegral n steps x τ a b η q)^p
      ∂(μ ⊗ₘ (hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps).comap x hx))^((p:ℝ)⁻¹) ≤
      4*(nearPairMomentConstant p)^((p:ℝ)⁻¹)*η*
        (∫ q, ‖actualSpinPath n steps x (τ (b+η)) q‖^(4*p)
          ∂(μ ⊗ₘ (hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps).comap x hx))^((p:ℝ)⁻¹) := by
  have := hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) steps hc
  let ν := μ ⊗ₘ (hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps).comap x hx
  let M := fun q => runningMax (fun j => ‖actualSpinPath n steps x j q‖^2) (τ (b+η))
  let A := physicalRadiusSquareIntegral n steps x τ a b η
  let H := physicalNearRadiusIntegral n steps x τ a b η
  have hM0 q : 0 ≤ M q := runningMax_nonneg (fun _ => sq_nonneg _) _
  have hMb q : M q ≤ 1 := by
    apply runningMax_le
    intro j
    have hn := actualSpinPath_norm_le n steps hc x j q
    nlinarith [norm_nonneg (actualSpinPath n steps x j q)]
  have hMm : Measurable M := by
    have hs : ∀ N, Measurable (fun q => runningMax (fun j => ‖actualSpinPath n steps x j q‖^2) N) := by
      intro N
      induction N with
      | zero => exact (actualSpinPath_measurable n steps hc x hx 0).norm.pow_const 2
      | succ N ih => exact ih.max ((actualSpinPath_measurable n steps hc x hx (N+1)).norm.pow_const 2)
    exact hs _
  have hA0 q : 0 ≤ A q := physicalRadiusSquareIntegral_nonneg n steps x τ hab η q
  have hAm : Measurable A := physicalRadiusSquareIntegral_measurable n steps hc x hx hτ a b η
  have hI : Integrable (fun q => (M q*A q)^p) ν := by
    apply Integrable.of_bound ((hMm.mul hAm).pow_const p).aestronglyMeasurable ((4*|b-a|)^p)
    exact Eventually.of_forall fun q => by
      change ‖(M q*A q)^p‖ ≤ _
      rw [norm_pow,norm_mul]
      apply pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      rw [Real.norm_of_nonneg (hM0 q)]
      exact (mul_le_mul_of_nonneg_right (hMb q) (norm_nonneg _)).trans (by
        simpa only [one_mul] using physicalRadiusSquareIntegral_bound n steps hc x hx τ a b η q)
  have h0 : 0 ≤ ∫ q, H q^p ∂ν := integral_nonneg fun q =>
    pow_nonneg (physicalNearRadiusIntegral_nonneg n steps x τ hab η q) p
  have hP : (∫ q, H q^p ∂ν) ≤ 4^p*(∫ q, (M q*A q)^p ∂ν) := by
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg
      (Eventually.of_forall fun q => pow_nonneg (physicalNearRadiusIntegral_nonneg n steps x τ hab η q) p)
      (hI.const_mul (4^p))
    exact Eventually.of_forall fun q => by
      have hh := physicalNearRadiusIntegral_le n steps hc x hx hτ hab hη.le q
      have hpow := pow_le_pow_left₀ (physicalNearRadiusIntegral_nonneg n steps x τ hab η q) hh p
      simpa only [mul_pow,mul_assoc] using hpow
  have hJ0 : 0 ≤ ∫ q, (M q*A q)^p ∂ν := integral_nonneg fun q =>
    pow_nonneg (mul_nonneg (hM0 q) (hA0 q)) p
  have hh := Real.rpow_le_rpow h0 hP (inv_nonneg.mpr (Nat.cast_nonneg p))
  rw [Real.mul_rpow (by positivity : (0:ℝ) ≤ 4^p) hJ0,
    Real.pow_rpow_inv_natCast (by norm_num : (0:ℝ) ≤ 4) hp.ne'] at hh
  have ht := mul_le_mul_of_nonneg_left
    (physicalNearPairProduct_Lp n steps hc μ x hx hτ hab hη hp) (by norm_num : (0:ℝ) ≤ 4)
  exact hh.trans (by simpa only [mul_assoc] using ht)

end SKFluctuations

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

omit [Nonempty S] in
 theorem hierarchyMeanPath_comp [Nonempty S]
    (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ) (A : S → ℝ)
    (steps : List (GaussianStep ι)) {P Q : Type} (x : P → ι → ℝ) (f : Q → P)
    (k : ℕ) (q : Q × ForwardPath (ι → ℝ) S steps.length) :
    hierarchyMeanPath w φ A steps (x ∘ f) k q =
      hierarchyMeanPath w φ A steps x k (f q.1,q.2) := by
  induction steps generalizing P Q k with
  | nil => cases k <;> rfl
  | cons st tail ih =>
    cases k with
    | zero => rfl
    | succ k =>
      exact ih (fun p : P × (ι → ℝ) => x p.1+p.2)
        (fun p : Q × (ι → ℝ) => (f p.1,p.2)) k ((q.1,q.2.1),q.2.2)

end SKFluctuations.Hierarchy
namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 theorem actualSpinPath_comp (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {P Q : Type} (x : P → FeatureIndex n → ℝ) (f : Q → P) (k : ℕ)
    (q : Q × ForwardPath (FeatureIndex n → ℝ) (Spin n) steps.length) :
    actualSpinPath n steps (x ∘ f) k q = actualSpinPath n steps x k (f q.1,q.2) := by
  apply PiLp.ext
  intro i
  exact hierarchyMeanPath_comp _ _ _ steps x f k q

 theorem actualSpinPath_cons (n : ℕ) (st : GaussianStep (FeatureIndex n))
    (steps : List (GaussianStep (FeatureIndex n))) {P : Type}
    (x : P → FeatureIndex n → ℝ) (k : ℕ)
    (q : P × ForwardPath (FeatureIndex n → ℝ) (Spin n) (st::steps).length) :
    actualSpinPath n (st::steps) x (k+1) q =
      actualSpinPath n steps (fun p : P × (FeatureIndex n → ℝ) => x p.1+p.2) k
        ((q.1,q.2.1),q.2.2) := rfl

 theorem actualSpinPath_coordinate_measurable (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {a : ℝ} (ha : OrderedSteps a steps) {P : Type} [MeasurableSpace P]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (k : ℕ) (i : Fin n) :
    Measurable (fun p : PhysicalPathState P n steps => actualSpinPath n steps x k p i) :=
  (hierarchyMeanPath_measurable (uniformWeight_pos n) (finiteFeature n)
    (fun σ => normalizedSpin n σ i) steps ha x hx k).mono
      (forwardPrefixSpace_le _ _ _ _ _) le_rfl

end SKFluctuations

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
  [MeasurableSpace S] [StandardBorelSpace S]

 def continuationState (pre tail : List (GaussianStep ι)) (x : ι → ℝ) :
    ForwardPath (ι → ℝ) S (pre++tail).length →
      (ι → ℝ) × ForwardPath (ι → ℝ) S tail.length :=
  match pre with
  | [] => fun p => (x,p)
  | _::pre => fun p => continuationState pre tail (x+p.1) p.2

omit [Fintype ι] [Fintype S] [Nonempty S] [MeasurableSpace S] [StandardBorelSpace S] in
 theorem continuationState_fst [Fintype ι] [Fintype S] [Nonempty S]
    [MeasurableSpace S] [StandardBorelSpace S]
    (pre tail : List (GaussianStep ι)) (x : ι → ℝ)
    (p : ForwardPath (ι → ℝ) S (pre++tail).length) :
    (continuationState pre tail x p).1 = actualCutField pre tail x p := by
  induction pre generalizing x with
  | nil => rfl
  | cons st pre ih => exact ih _ p.2

omit [Fintype ι] [Fintype S] [Nonempty S] [StandardBorelSpace S] in
 theorem continuationState_measurable [Fintype ι] [Fintype S] [Nonempty S]
    [StandardBorelSpace S] (pre tail : List (GaussianStep ι)) :
    Measurable (fun p : (ι → ℝ) × ForwardPath (ι → ℝ) S (pre++tail).length =>
      continuationState pre tail p.1 p.2) := by
  induction pre with
  | nil => exact measurable_id
  | cons st pre ih =>
    exact ih.comp ((measurable_fst.add (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd))

omit [MeasurableSpace S] [StandardBorelSpace S] in
 theorem hierarchyMeanPath_after_prefix [MeasurableSpace S] [StandardBorelSpace S]
    (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (A : S → ℝ) (pre tail : List (GaussianStep ι)) {P : Type} (x : P → ι → ℝ)
    (k : ℕ) (p : P × ForwardPath (ι → ℝ) S (pre++tail).length) :
    hierarchyMeanPath w φ A (pre++tail) x (pre.length+k) p =
      hierarchyMeanPath w φ A tail id k (continuationState pre tail (x p.1) p.2) := by
  induction pre generalizing P with
  | nil => simpa only [List.nil_append,List.length_nil,zero_add,continuationState,
      Function.id_comp] using hierarchyMeanPath_comp w φ A tail id x k p
  | cons st pre ih =>
    simpa only [List.length_cons,Nat.succ_add,List.cons_append,hierarchyMeanPath,continuationState] using
      ih (fun q : P × (ι → ℝ) => x q.1+q.2) ((p.1,p.2.1),p.2.2)

omit [Nonempty S] [StandardBorelSpace S] in
 theorem conditionalPathAverage_continuation [Nonempty S] [StandardBorelSpace S]
    (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (pre tail : List (GaussianStep ι)) {P : Type} (x : P → ι → ℝ)
    (F : (ι → ℝ) × ForwardPath (ι → ℝ) S tail.length → ℝ)
    (p : P × ForwardPath (ι → ℝ) S (pre++tail).length) :
    conditionalPathAverage w φ (pre++tail) x pre.length
      (fun q => F (continuationState pre tail (x q.1) q.2)) p =
      ∫ q, F (actualCutField pre tail (x p.1) p.2,q)
        ∂hierarchyPathKernel w φ tail (actualCutField pre tail (x p.1) p.2) := by
  induction pre generalizing P with
  | nil => cases tail <;> rfl
  | cons st pre ih =>
    exact ih (fun q : P × (ι → ℝ) => x q.1+q.2) ((p.1,p.2.1),p.2.2)

end SKFluctuations.Hierarchy
namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 theorem actualSpinPath_after_prefix (n : ℕ) (pre tail : List (GaussianStep (FeatureIndex n)))
    {P : Type} (x : P → FeatureIndex n → ℝ) (k : ℕ)
    (p : PhysicalPathState P n (pre++tail)) :
    actualSpinPath n (pre++tail) x (pre.length+k) p =
      actualSpinPath n tail id k (continuationState pre tail (x p.1) p.2) := by
  apply PiLp.ext
  intro i
  exact hierarchyMeanPath_after_prefix _ _ _ pre tail x k p

 def physicalFuturePairIncrement (n : ℕ) (common tail mid pre : List (GaussianStep (FeatureIndex n)))
    {P : Type} (x : P → FeatureIndex n → ℝ)
    (q : PhysicalPathState P n (common++(pre++(mid++tail)))) : Fin n → ℝ :=
  physicalPairIncrement n tail mid pre id
    (continuationState common (pre++(mid++tail)) (x q.1) q.2)

 theorem physicalFuturePairIncrement_eq_spinPath (n : ℕ)
    (common tail mid pre : List (GaussianStep (FeatureIndex n)))
    {P : Type} (x : P → FeatureIndex n → ℝ)
    (q : PhysicalPathState P n (common++(pre++(mid++tail)))) :
    WithLp.toLp 2 (physicalFuturePairIncrement n common tail mid pre x q) =
      actualSpinPath n (common++(pre++(mid++tail))) x (common.length+(pre.length+mid.length)) q -
        actualSpinPath n (common++(pre++(mid++tail))) x (common.length+pre.length) q := by
  rw [actualSpinPath_after_prefix n common (pre++(mid++tail)) x (pre.length+mid.length),
    actualSpinPath_after_prefix n common (pre++(mid++tail)) x pre.length]
  exact physicalPairIncrement_eq_spinPath n tail mid pre id _

 theorem physicalFuturePairIncrement_measurable (n : ℕ)
    (common tail mid pre : List (GaussianStep (FeatureIndex n)))
    {a : ℝ} (ha : OrderedSteps a (pre++(mid++tail)))
    {P : Type} [MeasurableSpace P] (x : P → FeatureIndex n → ℝ) (hx : Measurable x) :
    Measurable (physicalFuturePairIncrement n common tail mid pre x) :=
  (physicalPairIncrement_measurable n tail mid pre ha measurable_id).comp
    ((continuationState_measurable common (pre++(mid++tail))).comp
      ((hx.comp measurable_fst).prodMk measurable_snd))

 theorem physicalFuturePairAverage (n : ℕ) (common tail mid pre : List (GaussianStep (FeatureIndex n)))
    {P : Type} (x : P → FeatureIndex n → ℝ) (V : Fin n → ℝ) (l : ℕ)
    (p : PhysicalPathState P n (common++(pre++(mid++tail)))) :
    conditionalPathAverage (uniformWeight n) (finiteFeature n) (common++(pre++(mid++tail)))
      x common.length (fun q => (∑ i, V i*physicalFuturePairIncrement n common tail mid pre x q i)^l) p =
    ∫ q, (∑ i, V i*physicalPairIncrement n tail mid pre id
      (actualCutField common (pre++(mid++tail)) (x p.1) p.2,q) i)^l
      ∂hierarchyPathKernel (uniformWeight n) (finiteFeature n) (pre++(mid++tail))
        (actualCutField common (pre++(mid++tail)) (x p.1) p.2) := by
  exact conditionalPathAverage_continuation _ _ common (pre++(mid++tail)) x
    (fun q => (∑ i, V i*physicalPairIncrement n tail mid pre id q i)^l) p

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 theorem eventually_common_cut_conditional_square_projection (k : ℕ) (B : ℝ) :
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
      (fun q => (∑ i, V p i * physicalFuturePairIncrement n common tail mid (skip++pre) x q i)^2) p)^(k+1)
      ∂physicalPathLaw μ n (common++((skip++pre)++(mid++tail))) x hx) ≤
      (projectionLpConstant k*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*D)))^(2*k+2)*
        ∫ p, (projectionEuclideanNorm n (V p))^(2*k+2)
          ∂physicalPathLaw μ n (common++((skip++pre)++(mid++tail))) x hx := by
  filter_upwards [eventually_physical_conditional_square_projection k B] with n hn
  intro P _ common tail mid pre skip a a₀ D ha hD hDB ho hs μ _ x hx V hV R hR hc
  let rest := (skip++pre)++(mid++tail)
  let Ω := PhysicalPathState P n (common++rest)
  let ν := physicalPathLaw μ n (common++rest) x hx
  have := physicalPathLaw_finite μ n (common++rest) hs x hx
  let xc : Ω → FeatureIndex n → ℝ := fun p => actualCutField common rest (x p.1) p.2
  have hxc : Measurable xc := (actualCutField_measurable_joint common rest).comp
    ((hx.comp measurable_fst).prodMk measurable_snd)
  have hh := hn Ω tail mid pre skip a a₀ D ha hD hDB ho (hs.suffix common rest)
    ν V hV xc hxc R hR hc
  simp_rw [physicalFuturePairAverage]
  exact hh

 theorem eventually_common_cut_projection_moment (k : ℕ) (B : ℝ) :
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
    (∫ p, conditionalPathAverage (uniformWeight n) (finiteFeature n)
      (common++((skip++pre)++(mid++tail))) x common.length
      (fun q => |∑ i, V p i * physicalFuturePairIncrement n common tail mid (skip++pre) x q i|^(2*k+2)) p
      ∂physicalPathLaw μ n (common++((skip++pre)++(mid++tail))) x hx) ≤
      (projectionLpConstant k*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*D)))^(2*k+2)*
        ∫ p, (projectionEuclideanNorm n (V p))^(2*k+2)
          ∂physicalPathLaw μ n (common++((skip++pre)++(mid++tail))) x hx := by
  filter_upwards [eventually_physical_suffix_random_projection k B] with n hn
  intro P _ common tail mid pre skip a a₀ D ha hD hDB ho hs μ _ x hx V hV R hR hc
  let rest := (skip++pre)++(mid++tail)
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
  have hh := hn Ω tail mid pre skip a a₀ D ha hD hDB ho hr ν V hV xc hxc hVI hc
  let F : PhysicalPathState Ω n rest → ℝ := fun p =>
    |∑ i, V p.1 i * physicalPairIncrement n tail mid (skip++pre) xc p i|^(2*k+2)
  have hF : Measurable F := by
    apply Measurable.pow_const
    apply Measurable.abs
    apply Finset.measurable_sum
    intro i _
    exact ((measurable_pi_apply i).comp (hV.comp measurable_fst)).mul
      ((measurable_pi_apply i).comp (physicalPairIncrement_measurable n tail mid (skip++pre) hr hxc))
  have hFI : Integrable F (physicalPathLaw ν n rest xc hxc) := by
    have := physicalPathLaw_finite ν n rest hr xc hxc
    apply Integrable.of_bound hF.aestronglyMeasurable ((2*R)^(2*k+2))
    exact Eventually.of_forall fun p => by
      dsimp only [F]
      rw [Real.norm_of_nonneg (pow_nonneg (abs_nonneg _) _)]
      apply pow_le_pow_left₀ (abs_nonneg _)
      exact (abs_dot_physicalPairIncrement_le n (V p.1) tail mid (skip++pre) hr xc p).trans
        (by linarith [hR p.1])
  have := hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) rest hr
  have he : (∫ p, F p ∂physicalPathLaw ν n rest xc hxc) =
      ∫ p, (∫ q, F (p,q) ∂hierarchyPathKernel (uniformWeight n) (finiteFeature n) rest (xc p)) ∂ν :=
    Measure.integral_compProd hFI
  change (∫ p, F p ∂physicalPathLaw ν n rest xc hxc) ≤ _ at hh
  rw [he] at hh
  have hp p := conditionalPathAverage_continuation (uniformWeight n) (finiteFeature n) common rest x
    (fun q => |∑ i, V p i*physicalPairIncrement n tail mid (skip++pre) id q i|^(2*k+2)) p
  have hrewrite : ∀ p : Ω,
    conditionalPathAverage (uniformWeight n) (finiteFeature n) (common++rest) x common.length
      (fun q => |∑ i, V p i*physicalFuturePairIncrement n common tail mid (skip++pre) x q i|^(2*k+2)) p =
      ∫ q, F (p,q) ∂hierarchyPathKernel (uniformWeight n) (finiteFeature n) rest (xc p)  := hp
  change (∫ p : Ω, _ ∂ν) ≤ _
  calc
    _ = ∫ p, (∫ q, F (p,q) ∂hierarchyPathKernel (uniformWeight n) (finiteFeature n) rest (xc p)) ∂ν :=
      integral_congr_ae (Eventually.of_forall hrewrite)
    _ ≤ _ := hh

end SKFluctuations

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 theorem bounded_integral_power_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {F : Ω → ℝ} (hF : Measurable F) {R : ℝ}
    (h0 : ∀ q, 0 ≤ F q) (hR : ∀ q, F q ≤ R) {l : ℕ} (hl : 0 < l) :
    (∫ q, F q ∂μ)^l ≤ ∫ q, F q^l ∂μ := by
  have hi : Integrable F μ := Integrable.of_bound hF.aestronglyMeasurable R
    (Eventually.of_forall fun q => by rw [Real.norm_of_nonneg (h0 q)]; exact hR q)
  have hip : Integrable (fun q => F q^l) μ :=
    Integrable.of_bound (hF.pow_const l).aestronglyMeasurable (R^l)
      (Eventually.of_forall fun q => by
        rw [Real.norm_of_nonneg (pow_nonneg (h0 q) l)]
        exact pow_le_pow_left₀ (h0 q) (hR q) l)
  simpa using integral_pow_le_mass μ (Eventually.of_forall h0) hi hl hip

variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
  [MeasurableSpace S] [StandardBorelSpace S]

 theorem conditionalPathAverage_abs_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) {P : Type} (x : P → ι → ℝ) (k : ℕ)
    {F : P × ForwardPath (ι → ℝ) S steps.length → ℝ} {R : ℝ}
    (hR : ∀ p, |F p| ≤ R) (p : P × ForwardPath (ι → ℝ) S steps.length) :
    |conditionalPathAverage w φ steps x k F p| ≤ R := by
  induction steps generalizing P a k with
  | nil =>
    have := hierarchyPathKernel_markov hw φ [] ha
    cases k with
    | zero =>
      have hh := norm_integral_le_of_norm_le_const
        (f := fun q => F (p.1,q)) (μ := hierarchyPathKernel w φ [] (x p.1))
        (Eventually.of_forall fun q => by simpa only [Real.norm_eq_abs] using hR (p.1,q))
      simpa only [Real.norm_eq_abs, conditionalPathAverage] using hh.trans_eq (by simp)
    | succ k => exact hR p
  | cons st tail ih =>
    have := hierarchyPathKernel_markov hw φ (st::tail) ha
    cases k with
    | zero =>
      have hh := norm_integral_le_of_norm_le_const
        (f := fun q => F (p.1,q)) (μ := hierarchyPathKernel w φ (st::tail) (x p.1))
        (Eventually.of_forall fun q => by simpa only [Real.norm_eq_abs] using hR (p.1,q))
      simpa only [Real.norm_eq_abs, conditionalPathAverage] using hh.trans_eq (by simp)
    | succ k =>
      exact ih ha.2.2.2 (fun q : P × (ι → ℝ) => x q.1+q.2) k
        (F := fun q => F (q.1.1,(q.1.2,q.2)))
        (fun q => hR (q.1.1,(q.1.2,q.2))) ((p.1,p.2.1),p.2.2)

 theorem conditionalPathAverage_power_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) {P : Type} [MeasurableSpace P]
    (x : P → ι → ℝ) (k : ℕ)
    {F : P × ForwardPath (ι → ℝ) S steps.length → ℝ} (hF : Measurable F) {R : ℝ}
    (h0 : ∀ p, 0 ≤ F p) (hR : ∀ p, F p ≤ R) {l : ℕ} (hl : 0 < l)
    (p : P × ForwardPath (ι → ℝ) S steps.length) :
    (conditionalPathAverage w φ steps x k F p)^l ≤
      conditionalPathAverage w φ steps x k (fun q => F q^l) p := by
  induction steps generalizing P a k with
  | nil =>
    have := hierarchyPathKernel_markov hw φ [] ha
    cases k with
    | zero =>
      exact bounded_integral_power_le (hierarchyPathKernel w φ [] (x p.1))
        (hF.comp measurable_prodMk_left) (fun q => h0 (p.1,q)) (fun q => hR (p.1,q)) hl
    | succ k => exact le_rfl
  | cons st tail ih =>
    have := hierarchyPathKernel_markov hw φ (st::tail) ha
    cases k with
    | zero =>
      exact bounded_integral_power_le (hierarchyPathKernel w φ (st::tail) (x p.1))
        (hF.comp measurable_prodMk_left) (fun q => h0 (p.1,q)) (fun q => hR (p.1,q)) hl
    | succ k =>
      exact ih ha.2.2.2 (fun q : P × (ι → ℝ) => x q.1+q.2) k
        (hF.comp MeasurableEquiv.prodAssoc.measurable)
        (fun q => h0 (q.1.1,(q.1.2,q.2))) (fun q => hR (q.1.1,(q.1.2,q.2)))
        ((p.1,p.2.1),p.2.2)

 def conditionalForkTest (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (steps : List (GaussianStep ι)) {P : Type} (x : P → ι → ℝ) (k : ℕ)
    (F : (P × ForwardPath (ι → ℝ) S steps.length) ×
      (P × ForwardPath (ι → ℝ) S steps.length) → ℝ)
    (p : P × ForwardPath (ι → ℝ) S steps.length) : ℝ :=
  conditionalPathAverage w φ steps x k (fun q => F (p,q)) p

 theorem conditionalForkTest_measurable {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) {P : Type} [MeasurableSpace P]
    (x : P → ι → ℝ) (hx : Measurable x) (k : ℕ)
    {F : (P × ForwardPath (ι → ℝ) S steps.length) ×
      (P × ForwardPath (ι → ℝ) S steps.length) → ℝ} (hF : Measurable F) :
    Measurable (conditionalForkTest w φ steps x k F) := by
  have h := conditionalPathAverage_parameter_measurable hw φ steps ha x hx k hF
  have hdiag : Measurable (fun p : P × ForwardPath (ι → ℝ) S steps.length => (p,p)) :=
    measurable_id.prodMk measurable_id
  have hh := h.comp hdiag
  exact hh

end SKFluctuations.Hierarchy

end

end OAI
