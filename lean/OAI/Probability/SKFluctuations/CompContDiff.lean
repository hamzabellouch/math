import Mathlib
import OAI.Probability.SKFluctuations.LineDerivativesSignEquivVolume

namespace OAI

/-! Comp Cont Diff. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 

theorem BddSmooth.comp_contDiff {n : ℕ} {A : E → ℝ} (hA : BddSmooth n A)
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) : BddSmooth n (fun x => f (A x)) := by
  induction n generalizing A f with
  | zero =>
    obtain ⟨B,hB,hb⟩ := hA.bound
    obtain ⟨C,hC⟩ := (isCompact_Icc : IsCompact (Icc (-B) B)).exists_bound_of_continuousOn
      hf.continuous.continuousOn
    refine ⟨hf.continuous.comp hA.continuous, max C 0, le_max_right _ _, fun x => ?_⟩
    exact (hC (A x) (abs_le.mp (hb x))).trans (le_max_left _ _)
  | succ n ih =>
    refine ⟨ih hA.down hf, fun v => ?_⟩
    obtain ⟨A₁,hA₁,hd⟩ := hA.2 v
    have hdf : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
    refine ⟨fun x => deriv f (A x)*A₁ x, (ih hA.down hdf).mul hA₁, fun x t => ?_⟩
    exact ((contDiff_infty_iff_deriv.mp hf).1 (A (x+t•v))).hasDerivAt.comp t (hd x t)

 
def smoothAbsPower (ε p : ℝ) (x : ℝ) : ℝ := (x^2+ε)^(p/2)

theorem contDiff_smoothAbsPower {ε : ℝ} (hε : 0 < ε) (p : ℝ) :
    ContDiff ℝ ∞ (smoothAbsPower ε p) := by
  exact ((contDiff_id.pow 2).add contDiff_const).rpow_const_of_ne
    (fun x => ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg x) hε))

theorem BddSmooth.smoothAbsPower {n : ℕ} {A : E → ℝ} (hA : BddSmooth n A)
    {ε : ℝ} (hε : 0 < ε) (p : ℝ) : BddSmooth n (fun x => smoothAbsPower ε p (A x)) :=
  hA.comp_contDiff (contDiff_smoothAbsPower hε p)

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

 

theorem potentialLaw_equiv {n : ℕ} (T : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (hT : MeasurePreserving T volume volume) {U V : (Fin n → ℝ) → ℝ}
    (hUV : ∀ x, V (T x) = U x) :
    MeasurePreserving T (potentialLaw U) (potentialLaw V) := by
  have hI : (∫ z, Real.exp (-V z)) = ∫ z, Real.exp (-U z) := by
    rw [← hT.integral_comp T.toHomeomorph.toMeasurableEquiv.measurableEmbedding]
    simp_rw [hUV]
  have hn (x : Fin n → ℝ) : normalizedPotential V (T x) = normalizedPotential U x := by
    simp only [normalizedPotential, hUV, hI]
  refine ⟨T.continuous.measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply T.continuous.measurable hs]
  unfold potentialLaw
  rw [withDensity_apply _ (T.continuous.measurable hs), withDensity_apply _ hs,
    ← lintegral_indicator (T.continuous.measurable hs), ← lintegral_indicator hs]
  rw [← hT.lintegral_comp_emb T.toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (s.indicator (fun x => ENNReal.ofReal (Real.exp (-normalizedPotential V x))))]
  apply lintegral_congr
  intro x
  by_cases hx : T x ∈ s
  · simp only [mem_preimage, hx, indicator_of_mem, hn]
  · simp only [mem_preimage, hx, not_false_eq_true, indicator_of_notMem]

theorem potentialLaw_joint_test_eq {n : ℕ} (T : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (hT : MeasurePreserving T volume volume) {U V A B J K : (Fin n → ℝ) → ℝ}
    (hUV : ∀ x, V (T x) = U x) (hAB : ∀ x, B (T x) = A x)
    (hJK : ∀ x, K (T x) = J x) (f : ℝ × ℝ → ℝ) :
    (∫ x, f (B x, K x) ∂potentialLaw V) =
      ∫ x, f (A x, J x) ∂potentialLaw U := by
  rw [← (potentialLaw_equiv T hT hUV).integral_comp
    T.toHomeomorph.toMeasurableEquiv.measurableEmbedding]
  simp_rw [hAB, hJK]

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology ContDiff
open SKFluctuations.PinnedVariance SKFluctuations.PreKopa

theorem BddSmooth.lineDeriv_comp_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : E → ℝ} (hA : BddSmooth 1 A) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (x v : E) :
    lineDeriv ℝ (fun y => f (A y)) x v = deriv f (A x)*lineDeriv ℝ A x v := by
  apply HasLineDerivAt.lineDeriv
  have h := (((contDiff_infty_iff_deriv.mp hf).1 (A (x+0•v))).hasDerivAt).comp 0
    (hA.hasDerivAt_line x v 0)
  simpa only [zero_smul, add_zero, HasLineDerivAt, Function.comp_def] using h

 

theorem variance_comp_le_BddSmooth_block {n : ℕ} {U A J : (Fin n → ℝ) → ℝ}
    {μ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ]
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-U x))))
    (hU : GaussianDominated (fun x => Real.exp (-U x))) (hUc : Continuous U)
    (DU : LineDerivatives U) (hA : BddSmooth 2 A) (hJ : BddSmooth 2 J)
    (hstrong : ∀ x v, ‖v‖^2 ≤ DU.second x v)
    (hblock : ∀ x v s, 0 ≤ DU.second x v - 2*s*lineDeriv ℝ A x v + s^2*J x)
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    variance (fun x => f (A x)) μ ≤ ∫ x, (deriv f (A x))^2 * J x ∂μ := by
  have hdf : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  have hg : BddSmooth 2 (fun x => deriv f (A x)) := hA.comp_contDiff hdf
  simp only [pow_two]
  apply variance_le_BddSmooth_block hμ hU hUc DU (hA.comp_contDiff hf)
    ((hg.mul hg).mul hJ) hstrong
  intro x v s
  rw [hA.down.lineDeriv_comp_contDiff hf x v]
  convert hblock x v (s*deriv f (A x)) using 1
  ring

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory
open scoped NNReal Topology
variable {ι S : Type*} [Fintype ι] [Fintype S]

theorem gaussianHierarchyMean_const_mul (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (A : S → ℝ) (steps : List (GaussianStep ι)) (c : ℝ) (x : ι → ℝ) :
    gaussianHierarchyMean w φ (fun s => c*A s) steps x =
      c*gaussianHierarchyMean w φ A steps x := by
  induction steps generalizing x with
  | nil =>
    simp only [gaussianHierarchyMean, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    ring
  | cons p tail ih =>
    obtain ⟨m,q⟩ := p
    simp only [gaussianHierarchyMean, funext ih]
    exact shiftedMean_const_mul c x

end SKFluctuations.Hierarchy

namespace SKFluctuations
open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology NNReal
open Hierarchy

 

abbrev FeatureIndex (n : ℕ) := Sum (Fin n) (CompletedIndex n)

def featureCoefficient (n : ℕ) (σ : Spin n) : FeatureIndex n → ℝ
  | Sum.inl i => spinValue (σ i)
  | Sum.inr j => liftedCoefficients 1 n σ j

def finiteFeature (n : ℕ) (σ : Spin n) : (FeatureIndex n → ℝ) →L[ℝ] ℝ :=
  ∑ i, featureCoefficient n σ i • ContinuousLinearMap.proj i

@[simp] theorem finiteFeature_apply (n : ℕ) (σ : Spin n) (x : FeatureIndex n → ℝ) :
    finiteFeature n σ x = ∑ i, featureCoefficient n σ i*x i := by
  simp [finiteFeature]

def uniformWeight (n : ℕ) (_ : Spin n) : ℝ := (2 : ℝ)^(-(n : ℤ))

theorem uniformWeight_pos (n : ℕ) (σ : Spin n) : 0 < uniformWeight n σ := by
  exact zpow_pos (by norm_num) _

def featureSigns {n : ℕ} (τ : Spin n) : FeatureIndex n → ℝ
  | Sum.inl i => spinValue (τ i)
  | Sum.inr none => 1
  | Sum.inr (some e) => spinValue (τ e.val.1)*spinValue (τ e.val.2)

theorem featureSigns_sq {n : ℕ} (τ : Spin n) (i : FeatureIndex n) :
    featureSigns τ i*featureSigns τ i = 1 := by
  rcases i with i | (_ | e)
  · exact spinValue_sq _
  · norm_num [featureSigns]
  · dsimp [featureSigns]
    calc
      _ = (spinValue (τ e.val.1)*spinValue (τ e.val.1))*
        (spinValue (τ e.val.2)*spinValue (τ e.val.2)) := by ring
      _ = 1 := by rw [spinValue_sq, spinValue_sq]; norm_num

def featureGauge {n : ℕ} (τ : Spin n) : (FeatureIndex n → ℝ) ≃L[ℝ] (FeatureIndex n → ℝ) :=
  signEquiv (featureSigns τ) (featureSigns_sq τ)

theorem featureCoefficient_gauge {n : ℕ} (τ σ : Spin n) (i : FeatureIndex n) :
    featureCoefficient n (spinGauge τ σ) i = featureSigns τ i*featureCoefficient n σ i := by
  rcases i with i | (_ | e)
  · simp [featureCoefficient, featureSigns, spinGauge]
  · simp [featureCoefficient, featureSigns, liftedCoefficients]
  · simp only [featureCoefficient, featureSigns, liftedCoefficients, spinGauge,
      Equiv.coe_fn_mk, spinValue_beq]
    ring

theorem finiteFeature_gauge {n : ℕ} (τ σ : Spin n) (x : FeatureIndex n → ℝ) :
    finiteFeature n (spinGauge τ σ) (featureGauge τ x) = finiteFeature n σ x := by
  simp only [finiteFeature_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [featureCoefficient_gauge]
  change (featureSigns τ i * featureCoefficient n σ i)*(featureSigns τ i*x i) = _
  calc
    _ = (featureSigns τ i*featureSigns τ i)*(featureCoefficient n σ i*x i) := by ring
    _ = _ := by rw [featureSigns_sq, one_mul]

theorem featureGauge_gaussian {n : ℕ} (τ : Spin n) (q : FeatureIndex n → ℝ≥0) :
    MeasurePreserving (featureGauge τ) (Measure.pi fun i => gaussianReal 0 (q i))
      (Measure.pi fun i => gaussianReal 0 (q i)) :=
  signEquiv_gaussian _ _ q

theorem featureGauge_volume {n : ℕ} (τ : Spin n) :
    MeasurePreserving (featureGauge τ) volume volume := signEquiv_volume _ _

 
def finiteSKHierarchy (n : ℕ) (steps : List (GaussianStep (FeatureIndex n))) :
    (FeatureIndex n → ℝ) → ℝ := gaussianHierarchy (uniformWeight n) (finiteFeature n) steps

theorem finiteSKHierarchy_gauge (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    (τ : Spin n) (x : FeatureIndex n → ℝ) :
    finiteSKHierarchy n steps (featureGauge τ x) = finiteSKHierarchy n steps x :=
  gaussianHierarchy_equiv (featureGauge τ) (spinGauge τ) (fun _ => rfl)
    (finiteFeature_gauge τ) steps (fun p _ => featureGauge_gaussian τ p.2) x

 
def spinSource (n : ℕ) (i : Fin n) : FeatureIndex n → ℝ :=
  Pi.single (Sum.inl i) (1 / Real.sqrt (n : ℝ))

theorem finiteFeature_source (n : ℕ) (σ : Spin n) (i : Fin n) :
    finiteFeature n σ (spinSource n i) = spinValue (σ i) / Real.sqrt (n : ℝ) := by
  classical
  simp [finiteFeature_apply, spinSource, Pi.single_apply, featureCoefficient, mul_ite, div_eq_mul_inv]

theorem spinSource_gauge {n : ℕ} (τ : Spin n) (i : Fin n) :
    featureGauge τ (spinSource n i) = spinValue (τ i) • spinSource n i := by
  classical
  ext j
  change featureSigns τ j * (Pi.single (Sum.inl i) (1 / Real.sqrt (n : ℝ)) : FeatureIndex n → ℝ) j =
    spinValue (τ i) * (Pi.single (Sum.inl i) (1 / Real.sqrt (n : ℝ)) : FeatureIndex n → ℝ) j
  by_cases hj : j = Sum.inl i
  · subst j; rfl
  · simp [hj]

 

def matrixEmbedding (β : ℝ) (n : ℕ) (x : StandardCompletedDisorder n) : FeatureIndex n → ℝ
  | Sum.inl _ => 0
  | Sum.inr i => β*x i

theorem finiteFeature_matrixEmbedding (β : ℝ) (n : ℕ) (σ : Spin n)
    (x : StandardCompletedDisorder n) :
    finiteFeature n σ (matrixEmbedding β n x) = liftedHamiltonian β n x σ := by
  rw [finiteFeature_apply, liftedHamiltonian_eq_sum, Fintype.sum_sum_type]
  simp only [matrixEmbedding, mul_zero, Finset.sum_const_zero, zero_add, featureCoefficient]
  apply Finset.sum_congr rfl
  intro i _
  cases i <;> simp only [liftedCoefficients] <;> ring

end SKFluctuations

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Hierarchy
open scoped NNReal Topology BigOperators

theorem spinMean_gauge (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    (τ : Spin n) (x : FeatureIndex n → ℝ) (i : Fin n) :
    gaussianHierarchyMean (uniformWeight n) (finiteFeature n)
      (fun s => finiteFeature n s (spinSource n i)) steps (featureGauge τ x) =
    spinValue (τ i) * gaussianHierarchyMean (uniformWeight n) (finiteFeature n)
      (fun s => finiteFeature n s (spinSource n i)) steps x := by
  rw [gaussianHierarchyMean_equiv (featureGauge τ) (spinGauge τ) (fun _ => rfl)
    (finiteFeature_gauge τ) steps (fun p _ => featureGauge_gaussian τ p.2)]
  have he : (fun s => finiteFeature n (spinGauge τ s) (spinSource n i)) =
      (fun s => spinValue (τ i)*finiteFeature n s (spinSource n i)) := by
    funext s
    simp only [finiteFeature_source, spinGauge, Equiv.coe_fn_mk, spinValue_beq]
    ring
  rw [he, gaussianHierarchyMean_const_mul]

 

theorem spinObservable_gauge (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    (τ σ : Spin n) (x : FeatureIndex n → ℝ) :
    driverObservable (uniformWeight n) (finiteFeature n) steps
      (ContinuousLinearMap.id ℝ _) (spinSource n) (spinGauge τ σ) (featureGauge τ x) =
    driverObservable (uniformWeight n) (finiteFeature n) steps
      (ContinuousLinearMap.id ℝ _) (spinSource n) σ x := by
  unfold driverObservable driverMean
  simp only [ContinuousLinearMap.id_apply]
  simp_rw [spinMean_gauge]
  simp only [finiteFeature_source, spinGauge, Equiv.coe_fn_mk, spinValue_beq]
  apply Finset.sum_congr rfl
  intro i _
  have hs := spinValue_sq (τ i)
  rcases mul_self_eq_one_iff.mp hs with hi | hi <;> rw [hi] <;> ring

end SKFluctuations

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Hierarchy
open scoped NNReal Topology BigOperators

theorem spinDriverSource_gauge (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    (τ σ : Spin n) (x : FeatureIndex n → ℝ) :
    driverSource (uniformWeight n) (finiteFeature n) steps
      (ContinuousLinearMap.id ℝ _) (spinSource n) (spinGauge τ σ) (featureGauge τ x) =
    featureGauge τ (driverSource (uniformWeight n) (finiteFeature n) steps
      (ContinuousLinearMap.id ℝ _) (spinSource n) σ x) := by
  unfold driverSource driverMean
  simp only [ContinuousLinearMap.id_apply, map_sum, map_smul, spinSource_gauge, smul_smul]
  simp_rw [spinMean_gauge]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  simp only [finiteFeature_source, spinGauge, Equiv.coe_fn_mk, spinValue_beq]
  ring

theorem spinEnergy_gauge (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {a : ℝ} (ha : OrderedSteps a steps) (τ σ : Spin n) (x : FeatureIndex n → ℝ) :
    driverEnergy (uniformWeight n) (finiteFeature n) steps
      (ContinuousLinearMap.id ℝ _) (spinSource n) (spinGauge τ σ) (featureGauge τ x) =
    driverEnergy (uniformWeight n) (finiteFeature n) steps
      (ContinuousLinearMap.id ℝ _) (spinSource n) σ x := by
  rw [driverEnergy_eq (uniformWeight_pos n) (finiteFeature n) steps ha,
    driverEnergy_eq (uniformWeight_pos n) (finiteFeature n) steps ha]
  simp only [ContinuousLinearMap.id_apply, spinDriverSource_gauge]
  exact gaussianHierarchyHessian_equiv (featureGauge τ) (spinGauge τ) (uniformWeight_pos n)
    (fun _ => rfl) (finiteFeature_gauge τ) steps ha
    (fun p _ => featureGauge_gaussian τ p.2) _ _ _

end SKFluctuations

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Hierarchy
open scoped NNReal Topology BigOperators

abbrev IncrementIndex (n L : ℕ) := Fin (L+1) × FeatureIndex n
abbrev DriverDimension (n L : ℕ) := Fintype.card (IncrementIndex n L)

 

def prefixDriver (n L : ℕ) (q : Fin (L+1) → FeatureIndex n → ℝ≥0)
    (cut : Fin (L+1)) : (Fin (DriverDimension n L) → ℝ) →L[ℝ] (FeatureIndex n → ℝ) :=
  ContinuousLinearMap.pi fun i => ∑ k ∈ Finset.univ.filter (· ≤ cut),
    Real.sqrt (q k i : ℝ) • ContinuousLinearMap.proj (Fintype.equivFin (IncrementIndex n L) (k,i))

@[simp] theorem prefixDriver_apply (n L : ℕ) (q : Fin (L+1) → FeatureIndex n → ℝ≥0)
    (cut : Fin (L+1)) (x : Fin (DriverDimension n L) → ℝ) (i : FeatureIndex n) :
    prefixDriver n L q cut x i = ∑ k ∈ Finset.univ.filter (· ≤ cut),
      Real.sqrt (q k i : ℝ)*x (Fintype.equivFin (IncrementIndex n L) (k,i)) := by
  simp [prefixDriver]

def driverSigns (n L : ℕ) (τ : Spin n) (j : Fin (DriverDimension n L)) : ℝ :=
  featureSigns τ ((Fintype.equivFin (IncrementIndex n L)).symm j).2

theorem driverSigns_sq (n L : ℕ) (τ : Spin n) (j : Fin (DriverDimension n L)) :
    driverSigns n L τ j*driverSigns n L τ j = 1 := featureSigns_sq τ _

def driverGauge (n L : ℕ) (τ : Spin n) :
    (Fin (DriverDimension n L) → ℝ) ≃L[ℝ] (Fin (DriverDimension n L) → ℝ) :=
  signEquiv (driverSigns n L τ) (driverSigns_sq n L τ)

theorem prefixDriver_gauge (n L : ℕ) (q : Fin (L+1) → FeatureIndex n → ℝ≥0)
    (cut : Fin (L+1)) (τ : Spin n) (x : Fin (DriverDimension n L) → ℝ) :
    prefixDriver n L q cut (driverGauge n L τ x) = featureGauge τ (prefixDriver n L q cut x) := by
  ext i
  simp only [prefixDriver_apply, driverGauge, signEquiv_apply, driverSigns,
    Equiv.symm_apply_apply, featureGauge]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

 

def skPinFrame (n L : ℕ) (q : Fin (L+1) → FeatureIndex n → ℝ≥0)
    (cut : Fin (L+1)) (steps : List (GaussianStep (FeatureIndex n)))
    (a : ℝ) (ha : OrderedSteps a steps) :
    PinFrame (FeatureIndex n) (Spin n) (Fin n) (DriverDimension n L) where
  weight := uniformWeight n
  weight_pos := uniformWeight_pos n
  feature := finiteFeature n
  steps := steps
  mass := a
  ordered := ha
  driver := prefixDriver n L q cut
  source := spinSource n

end SKFluctuations

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Hierarchy
open scoped NNReal Topology BigOperators
variable {n L : ℕ} (q : Fin (L+1) → FeatureIndex n → ℝ≥0)
  (cuts : Fin (L+1) → Fin (L+1))
  (steps : Fin (L+1) → List (GaussianStep (FeatureIndex n)))
  (a : Fin (L+1) → ℝ) (ha : ∀ j, OrderedSteps (a j) (steps j))

abbrev skPinFamily : Fin (L+1) → PinFrame (FeatureIndex n) (Spin n) (Fin n) (DriverDimension n L) :=
  fun j => skPinFrame n L q (cuts j) (steps j) (a j) (ha j)

 theorem skPinFrame_potential_gauge (j : Fin (L+1)) (τ : Spin n)
    (x : Fin (DriverDimension n L) → ℝ) :
    (skPinFamily q cuts steps a ha j).potential (driverGauge n L τ x) =
      (skPinFamily q cuts steps a ha j).potential x := by
  change finiteSKHierarchy n (steps j) (prefixDriver n L q (cuts j) (driverGauge n L τ x)) = _
  rw [prefixDriver_gauge, finiteSKHierarchy_gauge]
  rfl

 theorem skPinFrame_observable_gauge (j : Fin (L+1)) (τ σ : Spin n)
    (x : Fin (DriverDimension n L) → ℝ) :
    (skPinFamily q cuts steps a ha j).observable (spinGauge τ σ) (driverGauge n L τ x) =
      (skPinFamily q cuts steps a ha j).observable σ x := by
  change driverObservable (uniformWeight n) (finiteFeature n) (steps j)
      (ContinuousLinearMap.id ℝ _) (spinSource n) (spinGauge τ σ)
      (prefixDriver n L q (cuts j) (driverGauge n L τ x)) =
    driverObservable (uniformWeight n) (finiteFeature n) (steps j)
      (ContinuousLinearMap.id ℝ _) (spinSource n) σ (prefixDriver n L q (cuts j) x)
  rw [prefixDriver_gauge]
  exact spinObservable_gauge n (steps j) τ σ (prefixDriver n L q (cuts j) x)

 theorem skPinFrame_energy_gauge (j : Fin (L+1)) (τ σ : Spin n)
    (x : Fin (DriverDimension n L) → ℝ) :
    (skPinFamily q cuts steps a ha j).energy (spinGauge τ σ) (driverGauge n L τ x) =
      (skPinFamily q cuts steps a ha j).energy σ x := by
  change driverEnergy (uniformWeight n) (finiteFeature n) (steps j)
      (ContinuousLinearMap.id ℝ _) (spinSource n) (spinGauge τ σ)
      (prefixDriver n L q (cuts j) (driverGauge n L τ x)) =
    driverEnergy (uniformWeight n) (finiteFeature n) (steps j)
      (ContinuousLinearMap.id ℝ _) (spinSource n) σ (prefixDriver n L q (cuts j) x)
  rw [prefixDriver_gauge]
  exact spinEnergy_gauge n (steps j) (ha j) τ σ (prefixDriver n L q (cuts j) x)

 theorem driverQuadratic_gauge (τ : Spin n) (x : Fin (DriverDimension n L) → ℝ) :
    driverQuadratic (driverGauge n L τ x) = driverQuadratic x := by
  unfold driverQuadratic
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change (driverSigns n L τ i*x i)^2 = (x i)^2
  rw [mul_pow]
  have hi := driverSigns_sq n L τ i
  nlinarith [sq_nonneg (x i)]

 theorem skPinned_joint_test_gauge (α k : Fin (L+1) → ℝ) (τ σ : Spin n) (f : ℝ × ℝ → ℝ) :
    let P := skPinFamily q cuts steps a ha
    let U := fun σ => pinnedPotential P α ((finiteFeature n σ).comp (prefixDriver n L q (Fin.last L)))
    (∫ x, f (pinnedObservable P α k (spinGauge τ σ) x, pinnedEnergy P α k (spinGauge τ σ) x)
      ∂potentialLaw (U (spinGauge τ σ))) =
    ∫ x, f (pinnedObservable P α k σ x, pinnedEnergy P α k σ x) ∂potentialLaw (U σ) := by
  dsimp only
  apply potentialLaw_joint_test_eq (driverGauge n L τ) (signEquiv_volume _ _)
  · intro x
    unfold pinnedPotential
    rw [driverQuadratic_gauge]
    simp only [ContinuousLinearMap.comp_apply, prefixDriver_gauge, finiteFeature_gauge]
    simp_rw [skPinFrame_potential_gauge]
  · intro x
    unfold pinnedObservable
    simp_rw [skPinFrame_observable_gauge]
  · intro x
    unfold pinnedEnergy
    simp_rw [skPinFrame_energy_gauge]

end SKFluctuations

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ContDiff

 theorem deriv_smoothAbsPower {ε : ℝ} (hε : 0 < ε) (p x : ℝ) :
    deriv (smoothAbsPower ε p) x = p*x*(x^2+ε)^(p/2-1) := by
  have h : HasDerivAt (smoothAbsPower ε p)
      ((2*x)*(p/2)*(x^2+ε)^(p/2-1)) x := by
    change HasDerivAt (fun y : ℝ => (y^2+ε)^(p/2)) _ x
    simpa using (((hasDerivAt_id x).pow 2).add_const ε).rpow_const (p := p/2)
      (Or.inl (ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg x) hε)))
  rw [h.deriv]
  ring

 theorem deriv_smoothAbsPower_sq_le {ε p : ℝ} (hε : 0 < ε) (x : ℝ) :
    (deriv (smoothAbsPower ε p) x)^2 ≤ p^2*(x^2+ε)^(p-1) := by
  rw [deriv_smoothAbsPower hε]
  have hz : 0 < x^2+ε := add_pos_of_nonneg_of_pos (sq_nonneg _) hε
  have he : ((x^2+ε)^(p/2-1))^2 = (x^2+ε)^(p-2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hz.le]
    congr 1
    ring
  have he' : (x^2+ε)^(p-1) = (x^2+ε)*(x^2+ε)^(p-2) := by
    rw [show p-1 = 1+(p-2) by ring, Real.rpow_add hz, Real.rpow_one]
  rw [mul_pow, mul_pow, he, he']
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith)
    (Real.rpow_nonneg hz.le _)) (sq_nonneg p)

 theorem smoothAbsPower_sq {ε : ℝ} (hε : 0 ≤ ε) (p x : ℝ) :
    (smoothAbsPower ε p x)^2 = (x^2+ε)^p := by
  unfold smoothAbsPower
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  ring

 theorem smoothAbsPower_zero (p : ℝ) (x : ℝ) : smoothAbsPower 0 p x = |x|^p := by
  unfold smoothAbsPower
  rw [add_zero, ← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg x)]
  congr 1
  ring

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ContDiff

 def powerEps (k : ℕ) : ℝ := 1 / ((k : ℝ)+1)

 theorem powerEps_pos (k : ℕ) : 0 < powerEps k := by unfold powerEps; positivity
 theorem powerEps_le_one (k : ℕ) : powerEps k ≤ 1 := by
  unfold powerEps
  rw [div_le_one (by positivity)]
  linarith [Nat.cast_nonneg (α := ℝ) k]
 theorem powerEps_tendsto : Tendsto powerEps atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

 theorem integral_regularized_power_tendsto {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [IsFiniteMeasure μ] {A J : E → ℝ}
    (hA : BddSmooth 0 A) (hJ : BddSmooth 0 J) {p : ℝ} (hp : 0 ≤ p) :
    Tendsto (fun k => ∫ x, (A x^2+powerEps k)^p * J x ∂μ) atTop
      (𝓝 (∫ x, |A x|^(2*p)*J x ∂μ)) := by
  obtain ⟨B,hB,hAb⟩ := hA.bound
  obtain ⟨C,hC,hJb⟩ := hJ.bound
  apply tendsto_integral_of_dominated_convergence (fun _ => (B^2+1)^p*C)
  · intro k
    exact ((Real.continuous_rpow_const hp).comp
      ((hA.continuous.pow 2).add continuous_const) |>.mul hJ.continuous).aestronglyMeasurable
  · exact integrable_const _
  · intro k
    filter_upwards [] with x
    have hz : 0 ≤ A x^2+powerEps k := add_nonneg (sq_nonneg _) (powerEps_pos k).le
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hz _)]
    apply mul_le_mul _ (hJb x) (abs_nonneg _) (Real.rpow_nonneg (by positivity) _)
    apply Real.rpow_le_rpow hz _ hp
    have hab : A x^2 ≤ B^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr (hAb x)
    
    linarith [powerEps_le_one k]
  · filter_upwards [] with x
    have ht : Tendsto (fun k => A x^2+powerEps k) atTop (𝓝 (A x^2)) := by
      simpa using tendsto_const_nhds.add powerEps_tendsto (a := A x^2)
    have he : (A x^2)^p = |A x|^(2*p) := by
      rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
      norm_num
    simpa only [he, Function.comp_def] using ((Real.continuous_rpow_const hp).tendsto _ |>.comp ht).mul_const (J x)

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology ContDiff
open SKFluctuations.PinnedVariance SKFluctuations.PreKopa

 theorem BddSmooth.memLp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsFiniteMeasure μ]
    {r : ℕ} {A : E → ℝ} (hA : BddSmooth r A) (p : ENNReal) : MemLp A p μ := by
  obtain ⟨B,_,hB⟩ := hA.bound
  exact MemLp.of_bound hA.continuous.aestronglyMeasurable B (ae_of_all _ hB)

 theorem BddSmooth.integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsFiniteMeasure μ]
    {r : ℕ} {A : E → ℝ} (hA : BddSmooth r A) : Integrable A μ :=
  memLp_one_iff_integrable.mp (hA.memLp 1)

 theorem regularized_power_moment_le {n : ℕ} {U A J : (Fin n → ℝ) → ℝ}
    {μ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ]
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-U x))))
    (hU : GaussianDominated (fun x => Real.exp (-U x))) (hUc : Continuous U)
    (DU : LineDerivatives U) (hA : BddSmooth 2 A) (hJ : BddSmooth 2 J)
    (hJ0 : ∀ x, 0 ≤ J x)
    (hstrong : ∀ x v, ‖v‖^2 ≤ DU.second x v)
    (hblock : ∀ x v s, 0 ≤ DU.second x v - 2*s*lineDeriv ℝ A x v + s^2*J x)
    {ε : ℝ} (hε : 0 < ε) (p : ℝ) :
    (∫ x, (A x^2+ε)^(p/2) ∂μ) ≤
      (∫ x, (A x^2+ε)^(p/4) ∂μ)^2 +
        (p^2/4)*(∫ x, (A x^2+ε)^((p-2)/2)*J x ∂μ) := by
  let f := smoothAbsPower ε (p/2)
  have hf : ContDiff ℝ ∞ f := contDiff_smoothAbsPower hε _
  have hAf := hA.comp_contDiff hf
  have hdf := hA.comp_contDiff (contDiff_infty_iff_deriv.mp hf).2
  have hG : BddSmooth 2 (fun x => (A x^2+ε)^((p-2)/2)*J x) :=
    (hA.smoothAbsPower hε (p-2)).mul hJ
  have hv := variance_comp_le_BddSmooth_block hμ hU hUc DU hA hJ hstrong hblock hf
  rw [variance_eq_sub (hAf.memLp 2)] at hv
  have he : (∫ x, (deriv f (A x))^2*J x ∂μ) ≤
      (p^2/4)*(∫ x, (A x^2+ε)^((p-2)/2)*J x ∂μ) := by
    rw [← integral_const_mul]
    apply integral_mono
    · simpa only [pow_two] using ((hdf.mul hdf).mul hJ).integrable (μ := μ)
    · exact (hG.const_mul (p^2/4)).integrable
    · intro x
      have he := mul_le_mul_of_nonneg_right (deriv_smoothAbsPower_sq_le hε (p := p/2) (A x)) (hJ0 x)
      have hexp : p/2-1 = (p-2)/2 := by ring
      have hcoef : (p/2)^2 = p^2/4 := by ring
      simpa only [f, hexp, hcoef, mul_assoc] using he
  have hsq : (∫ x, ((fun x => f (A x))^2) x ∂μ) = ∫ x, (A x^2+ε)^(p/2) ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with x
    exact smoothAbsPower_sq hε.le _ _
  have hmean : (∫ x, f (A x) ∂μ) = ∫ x, (A x^2+ε)^(p/4) ∂μ := by
    congr 1
    funext x
    dsimp [f, smoothAbsPower]
    congr 1
    ring
  rw [hsq, hmean] at hv
  linarith

 theorem power_moment_le {n : ℕ} {U A J : (Fin n → ℝ) → ℝ}
    {μ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ]
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-U x))))
    (hU : GaussianDominated (fun x => Real.exp (-U x))) (hUc : Continuous U)
    (DU : LineDerivatives U) (hA : BddSmooth 2 A) (hJ : BddSmooth 2 J)
    (hJ0 : ∀ x, 0 ≤ J x)
    (hstrong : ∀ x v, ‖v‖^2 ≤ DU.second x v)
    (hblock : ∀ x v s, 0 ≤ DU.second x v - 2*s*lineDeriv ℝ A x v + s^2*J x)
    {p : ℝ} (hp : 2 < p) :
    (∫ x, |A x|^p ∂μ) ≤ (∫ x, |A x|^(p/2) ∂μ)^2 +
        (p^2/4)*(∫ x, |A x|^(p-2)*J x ∂μ) := by
  have h₁ := integral_regularized_power_tendsto (μ := μ) hA.down.down
    (BddSmooth.const 0 (1 : ℝ)) (p := p/2) (by linarith)
  have h₂ := integral_regularized_power_tendsto (μ := μ) hA.down.down
    (BddSmooth.const 0 (1 : ℝ)) (p := p/4) (by linarith)
  have h₃ := integral_regularized_power_tendsto (μ := μ) hA.down.down hJ.down.down
    (p := (p-2)/2) (by linarith)
  have he₁ : 2*(p/2) = p := by ring
  have he₂ : 2*(p/4) = p/2 := by ring
  have he₃ : 2*((p-2)/2) = p-2 := by ring
  simp only [mul_one, he₁, he₂, he₃] at h₁ h₂ h₃
  exact le_of_tendsto_of_tendsto h₁ ((h₂.pow 2).add (h₃.const_mul (p^2/4)))
    (Filter.Eventually.of_forall fun k => regularized_power_moment_le hμ hU hUc DU hA hJ hJ0 hstrong hblock
      (powerEps_pos k) p)

end SKFluctuations.Hierarchy

end

end OAI
