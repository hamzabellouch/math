import Mathlib
import OAI.Probability.SKFluctuations.MomentNorm

namespace OAI

/-! Rooted Increments. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

def rootedIncrements (q₀ : ι → ℝ≥0) (steps : List (GaussianStep ι)) :
    Fin (steps.length+1) → (ι → ℝ) → (ι → ℝ) :=
  Fin.cons (scaleDriver q₀) (hierarchyIncrements steps)

def rootedTransitions (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (steps : List (GaussianStep ι)) :
    Fin (steps.length+1) → (ι → ℝ) → (ι → ℝ) → ℝ≥0∞ :=
  Fin.cons (fun _ _ => 1) (hierarchyTransitions w φ steps)

 

def rootedJointDensity (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (q₀ : ι → ℝ≥0) (steps : List (GaussianStep ι))
    (p : Fin (steps.length+1) → (ι → ℝ)) (σ : S) : ℝ :=
  hierarchyJointDensity w φ steps (scaleDriver q₀ (p 0)) (Fin.tail p) σ

omit [Nonempty S] in
 theorem rootedJointDensity_factor (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (q₀ : ι → ℝ≥0) (steps : List (GaussianStep ι))
    (p : Fin (steps.length+1) → (ι → ℝ)) (σ : S) :
    ENNReal.ofReal (rootedJointDensity w φ q₀ steps p σ) =
      forwardWeight (steps.length+1) (rootedIncrements q₀ steps) (rootedTransitions w φ steps) 0 p *
        ENNReal.ofReal (spinWeight w φ
          (forwardEnd (steps.length+1) (rootedIncrements q₀ steps) 0 p) σ) := by
  simp only [rootedJointDensity, hierarchyJointDensity, ENNReal.ofReal_mul (Real.exp_nonneg _),
    forwardWeight, forwardEnd, rootedIncrements, rootedTransitions, Fin.cons_zero, Fin.cons_succ,
    zero_add, one_mul, hierarchyPathWeight_eq]

 theorem rootedJointDensity_normalized {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (q₀ : ι → ℝ≥0) (steps : List (GaussianStep ι))
    (ha : OrderedSteps 0 steps) :
    (∑ σ, ∫⁻ p, ENNReal.ofReal (rootedJointDensity w φ q₀ steps p σ)
      ∂Measure.pi (fun _ : Fin (steps.length+1) => standardDrivers ι)) = 1 := by
  simp_rw [rootedJointDensity_factor]
  apply sum_lintegral_forward_terminal _ _
    (Fin.cases (scaleDriver q₀).measurable (hierarchyIncrements_measurable steps))
    (Fin.cases measurable_const (hierarchyTransitions_measurable hw φ steps ha))
    (Fin.cases (by intro x; simp [rootedTransitions]) (hierarchyTransitions_normalized hw φ steps ha))
    (fun x σ => ENNReal.ofReal (spinWeight w φ x σ))
  · intro σ
    exact (continuous_spinWeight hw φ σ).measurable.ennreal_ofReal
  · intro x
    rw [← ENNReal.ofReal_sum_of_nonneg (fun σ _ => spinWeight_nonneg hw φ x σ), sum_spinWeight hw φ]
    exact ENNReal.ofReal_one

 theorem rootedJointDensity_telescope {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (q₀ : ι → ℝ≥0) (steps : List (GaussianStep ι))
    (p : Fin (steps.length+1) → (ι → ℝ)) (σ : S) :
    rootedJointDensity w φ q₀ steps p σ = w σ * Real.exp
      (φ σ (forwardEnd (steps.length+1) (rootedIncrements q₀ steps) 0 p) -
        hierarchyPathCost w φ steps 0 (scaleDriver q₀ (p 0)) (Fin.tail p)) := by
  rw [rootedJointDensity, hierarchyJointDensity_eq hw φ steps 0]
  simp only [zero_mul, sub_zero, forwardEnd, rootedIncrements, Fin.cons_zero, Fin.cons_succ, zero_add]

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory
open scoped Topology NNReal BigOperators
variable {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]

 

def flattenDrivers (e : τ ≃ ι × κ) : (ι → κ → ℝ) ≃L[ℝ] (τ → ℝ) where
  toFun p j := p (e j).1 (e j).2
  invFun x i k := x (e.symm (i,k))
  left_inv p := by ext i k; simp
  right_inv x := by ext j; simp
  map_add' p q := by ext j; rfl
  map_smul' r p := by ext j; rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

omit [Fintype ι] [Fintype κ] [Fintype τ] in
@[simp] theorem flattenDrivers_apply (e : τ ≃ ι × κ) (p : ι → κ → ℝ) (j : τ) :
    flattenDrivers e p j = p (e j).1 (e j).2 := rfl

omit [Fintype ι] [Fintype κ] [Fintype τ] in
@[simp] theorem flattenDrivers_symm_apply (e : τ ≃ ι × κ) (x : τ → ℝ) (i : ι) (k : κ) :
    (flattenDrivers e).symm x i k = x (e.symm (i,k)) := rfl

 theorem flattenDrivers_measure (e : τ ≃ ι × κ) (μ : ι → κ → Measure ℝ)
    [∀ i k, SigmaFinite (μ i k)] :
    MeasurePreserving (flattenDrivers e) (Measure.pi (fun i => Measure.pi (μ i)))
      (Measure.pi fun j => μ (e j).1 (e j).2) := by
  refine ⟨(flattenDrivers e).continuous.measurable, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (flattenDrivers e).continuous.measurable (MeasurableSet.univ_pi hs)]
  have he : (flattenDrivers e) ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun i => Set.univ.pi (fun k => s (e.symm (i,k)))) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_univ_pi, flattenDrivers_apply]
    constructor
    · intro h i k
      simpa using h (e.symm (i,k))
    · intro h j
      have h' := h (e j).1 (e j).2
      rw [show e.symm ((e j).1, (e j).2) = j from e.symm_apply_apply j] at h'
      exact h'
  rw [he, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [← Fintype.prod_prod_type (f := fun ik : ι × κ => μ ik.1 ik.2 (s (e.symm ik)))]
  simpa only [Equiv.apply_symm_apply] using
    (e.symm.prod_comp (fun j => μ (e j).1 (e j).2 (s j)))

 theorem flattenDrivers_standard (e : τ ≃ ι × κ) :
    MeasurePreserving (flattenDrivers e) (Measure.pi fun _ : ι => standardDrivers κ)
      (standardDrivers τ) := by
  exact flattenDrivers_measure e (fun _ _ => gaussianReal 0 1)

 theorem flattenDrivers_volume (e : τ ≃ ι × κ) :
    MeasurePreserving (flattenDrivers e) volume volume := by
  exact flattenDrivers_measure e (fun _ _ => volume)

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory
open scoped Topology NNReal BigOperators
variable {ι S κ : Type*} [Fintype ι] [Fintype S] [Nonempty S] {n : ℕ}

 

def pathFrames (w : S → ℝ) (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (source : κ → ι → ℝ) :
    (steps : List (GaussianStep ι)) → (a : ℝ) → OrderedSteps a steps →
    ((Fin n → ℝ) →L[ℝ] (ι → ℝ)) →
    (Fin steps.length → (Fin n → ℝ) →L[ℝ] (ι → ℝ)) →
    Fin (steps.length+1) → PinFrame ι S κ n
  | [], a, ha, D, _ => fun _ => ⟨w,hw,φ,[],a,ha,D,source⟩
  | (m,q)::tail, a, ha, D, p => Fin.cons ⟨w,hw,φ,(m,q)::tail,a,ha,D,source⟩
      (pathFrames w hw φ source tail m ha.2.2.2 (D+(scaleDriver q).comp (p 0))
        (fun i => p i.succ))

def pathMassDifferences : (steps : List (GaussianStep ι)) → ℝ → Fin (steps.length+1) → ℝ
  | [], a => fun _ => 1-a
  | (m,_)::tail, a => Fin.cons (m-a) (pathMassDifferences tail m)

omit [Fintype ι] [Fintype S] [Nonempty S] in
 theorem pathMassDifferences_nonneg (steps : List (GaussianStep ι)) {a : ℝ}
    (ha : OrderedSteps a steps) : ∀ j, 0 ≤ pathMassDifferences steps a j := by
  induction steps generalizing a with
  | nil => intro j; exact sub_nonneg.mpr ha.2
  | cons step tail ih =>
    rcases step with ⟨m,q⟩
    exact Fin.cases (sub_nonneg.mpr ha.2.1) (ih ha.2.2.2)

omit [Fintype ι] [Fintype S] [Nonempty S] in
 theorem sum_pathMassDifferences (steps : List (GaussianStep ι)) (a : ℝ) :
    ∑ j, pathMassDifferences steps a j = 1-a := by
  induction steps generalizing a with
  | nil => simp [pathMassDifferences]
  | cons step tail ih =>
    rcases step with ⟨m,q⟩
    simp only [List.length_cons]
    rw [Fin.sum_univ_succ]
    simp only [pathMassDifferences, Fin.cons_zero, Fin.cons_succ]
    rw [ih m]
    ring

 theorem pathFrames_cost (w : S → ℝ) (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (source : κ → ι → ℝ)
    (steps : List (GaussianStep ι)) (a : ℝ) (ha : OrderedSteps a steps)
    (D : (Fin n → ℝ) →L[ℝ] (ι → ℝ))
    (p : Fin steps.length → (Fin n → ℝ) →L[ℝ] (ι → ℝ)) (x : Fin n → ℝ) :
    (∑ j, pathMassDifferences steps a j * (pathFrames w hw φ source steps a ha D p j).potential x) =
      hierarchyPathCost w φ steps a (D x) (fun j => p j x) := by
  induction steps generalizing a D with
  | nil => simp [pathMassDifferences, pathFrames, PinFrame.potential, hierarchyPathCost, gaussianHierarchy]
  | cons step tail ih =>
    rcases step with ⟨m,q⟩
    simp only [List.length_cons]
    rw [Fin.sum_univ_succ]
    simp only [pathMassDifferences, pathFrames, Fin.cons_zero, Fin.cons_succ]
    rw [ih m ha.2.2.2 (D+(scaleDriver q).comp (p 0)) (fun i => p i.succ)]
    rfl

def pathEndMap : (steps : List (GaussianStep ι)) →
    ((Fin n → ℝ) →L[ℝ] (ι → ℝ)) →
    (Fin steps.length → (Fin n → ℝ) →L[ℝ] (ι → ℝ)) → (Fin n → ℝ) →L[ℝ] (ι → ℝ)
  | [], D, _ => D
  | (_,q)::tail, D, p =>
      pathEndMap tail (D+(scaleDriver q).comp (p 0)) (fun i => p i.succ)

omit [Fintype ι] [Fintype S] [Nonempty S] in
 theorem pathEndMap_apply (steps : List (GaussianStep ι))
    (D : (Fin n → ℝ) →L[ℝ] (ι → ℝ))
    (p : Fin steps.length → (Fin n → ℝ) →L[ℝ] (ι → ℝ)) (x : Fin n → ℝ) :
    pathEndMap steps D p x =
      forwardEnd steps.length (hierarchyIncrements steps) (D x) (fun j => p j x) := by
  induction steps generalizing D with
  | nil => rfl
  | cons step tail ih =>
    rcases step with ⟨m,q⟩
    simp only [pathEndMap, List.length_cons, forwardEnd, hierarchyIncrements,
      Fin.cons_zero, Fin.cons_succ, ih]
    rfl

 theorem pathFrames_potential (w : S → ℝ) (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (source : κ → ι → ℝ)
    (steps : List (GaussianStep ι)) (a : ℝ) (ha : OrderedSteps a steps)
    (D : (Fin n → ℝ) →L[ℝ] (ι → ℝ))
    (p : Fin steps.length → (Fin n → ℝ) →L[ℝ] (ι → ℝ)) (σ : S) (x : Fin n → ℝ) :
    pinnedPotential (pathFrames w hw φ source steps a ha D p) (pathMassDifferences steps a)
      ((φ σ).comp (pathEndMap steps D p)) x =
      driverQuadratic x - φ σ (forwardEnd steps.length (hierarchyIncrements steps) (D x) (fun j => p j x)) +
        hierarchyPathCost w φ steps a (D x) (fun j => p j x) := by
  rw [pinnedPotential, pathFrames_cost, ContinuousLinearMap.comp_apply, pathEndMap_apply]

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
open SKFluctuations.PreKopa

 

theorem withDensity_equiv {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (T : E ≃ᵐ F) {μ : Measure E} {ν : Measure F} (hT : MeasurePreserving T μ ν)
    {f : E → ℝ≥0∞} {g : F → ℝ≥0∞} (hfg : ∀ x, g (T x) = f x) :
    MeasurePreserving T (μ.withDensity f) (ν.withDensity g) := by
  refine ⟨T.measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply T.measurable hs, withDensity_apply _ (T.measurable hs),
    withDensity_apply _ hs, ← lintegral_indicator (T.measurable hs), ← lintegral_indicator hs,
    ← hT.lintegral_comp_emb T.measurableEmbedding (s.indicator g)]
  apply lintegral_congr
  intro x
  by_cases hx : T x ∈ s
  · simp only [mem_preimage, hx, indicator_of_mem, hfg]
  · simp only [mem_preimage, hx, not_false_eq_true, indicator_of_notMem]

 
theorem gaussian_tilt_potentialLaw {n : ℕ} {G U : (Fin n → ℝ) → ℝ}
    (hG : Continuous G) (hU : GaussianDominated (fun x => Real.exp (-U x)))
    (hUG : ∀ x, U x = driverQuadratic x - G x) {w : ℝ} (hw : 0 ≤ w) :
    (standardDrivers (Fin n)).withDensity (fun x => ENNReal.ofReal (w*Real.exp (G x))) =
      ENNReal.ofReal (w * (Real.sqrt (2*Real.pi))⁻¹ ^ n * (∫ x, Real.exp (-U x))) • potentialLaw U := by
  have hc : 0 < (Real.sqrt (2*Real.pi))⁻¹ ^ n := by positivity
  have hZ := positive_integral_exp_neg hU
  have hpdf : Measurable (fun x : Fin n → ℝ => ENNReal.ofReal (standardGaussianPDF x)) := by
    apply Measurable.ennreal_ofReal
    apply Continuous.measurable
    change Continuous (fun x : Fin n → ℝ => standardGaussianPDF x)
    simp_rw [standardGaussianPDF_eq]
    fun_prop
  have hg : Measurable (fun x => ENNReal.ofReal (w*Real.exp (G x))) :=
    ((Real.continuous_exp.comp hG).const_mul w).measurable.ennreal_ofReal
  rw [standardDrivers, standardGaussian_pi_withDensity, ← withDensity_mul volume hpdf hg]
  have he (x : Fin n → ℝ) :
      ENNReal.ofReal (standardGaussianPDF x) * ENNReal.ofReal (w*Real.exp (G x)) =
      ENNReal.ofReal (w * (Real.sqrt (2*Real.pi))⁻¹ ^ n * (∫ z, Real.exp (-U z))) *
        ENNReal.ofReal (Real.exp (-normalizedPotential U x)) := by
    rw [← ENNReal.ofReal_mul (standardGaussianPDF_nonneg x),
      ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hw hc.le) hZ.le),
      exp_neg_normalizedPotential hU x, standardGaussianPDF_eq]
    congr 1
    rw [hUG x, Real.exp_neg, Real.exp_sub]
    unfold driverQuadratic
    simp only [Fintype.card_fin]
    rw [show -(1/2 : ℝ)*(∑ i, (x i)^2) = -(∑ i, (x i)^2)/2 by ring]
    rw [show -(∑ i, (x i)^2)/2 = -((∑ i, (x i)^2)/2) by ring, Real.exp_neg]
    field_simp
  change volume.withDensity (fun x => ENNReal.ofReal (standardGaussianPDF x) *
      ENNReal.ofReal (w*Real.exp (G x))) = _
  simp_rw [he]
  exact withDensity_smul' _ _ ENNReal.ofReal_ne_top

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
open SKFluctuations.PreKopa
variable {ι S κ : Type*} [Fintype ι] [Fintype S] [Nonempty S] {n : ℕ}

def flatLevelProjection {L : ℕ} (e : Fin n ≃ Fin (L+1) × ι) (j : Fin (L+1)) :
    (Fin n → ℝ) →L[ℝ] (ι → ℝ) :=
  (ContinuousLinearMap.proj j).comp (flattenDrivers e).symm.toContinuousLinearMap

omit [Fintype ι] [Fintype S] [Nonempty S] in
@[simp] theorem flatLevelProjection_apply {L : ℕ} (e : Fin n ≃ Fin (L+1) × ι)
    (j : Fin (L+1)) (x : Fin n → ℝ) :
    flatLevelProjection e j x = (flattenDrivers e).symm x j := rfl

def flatRootFrames (w : S → ℝ) (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (source : κ → ι → ℝ)
    (q₀ : ι → ℝ≥0) (steps : List (GaussianStep ι)) (ha : OrderedSteps 0 steps)
    (e : Fin n ≃ Fin (steps.length+1) × ι) : Fin (steps.length+1) → PinFrame ι S κ n :=
  pathFrames w hw φ source steps 0 ha ((scaleDriver q₀).comp (flatLevelProjection e 0))
    (fun j => flatLevelProjection e j.succ)

def flatTerminalFeature (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (q₀ : ι → ℝ≥0) (steps : List (GaussianStep ι))
    (e : Fin n ≃ Fin (steps.length+1) × ι) (σ : S) : (Fin n → ℝ) →L[ℝ] ℝ :=
  (φ σ).comp (pathEndMap steps ((scaleDriver q₀).comp (flatLevelProjection e 0))
    (fun j => flatLevelProjection e j.succ))

def flatPinPotential (w : S → ℝ) (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (source : κ → ι → ℝ)
    (q₀ : ι → ℝ≥0) (steps : List (GaussianStep ι)) (ha : OrderedSteps 0 steps)
    (e : Fin n ≃ Fin (steps.length+1) × ι) (σ : S) : (Fin n → ℝ) → ℝ :=
  pinnedPotential (flatRootFrames w hw φ source q₀ steps ha e) (pathMassDifferences steps 0)
    (flatTerminalFeature φ q₀ steps e σ)

 

noncomputable def flatPlantedPinLaw (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (q₀ : ι → ℝ≥0) (steps : List (GaussianStep ι))
    (e : Fin n ≃ Fin (steps.length+1) × ι) (σ : S) : Measure (Fin n → ℝ) :=
  (standardDrivers (Fin n)).withDensity
    (fun x => ENNReal.ofReal (rootedJointDensity w φ q₀ steps ((flattenDrivers e).symm x) σ))

 theorem flatPin_likelihood (w : S → ℝ) (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (source : κ → ι → ℝ)
    (q₀ : ι → ℝ≥0) (steps : List (GaussianStep ι)) (ha : OrderedSteps 0 steps)
    (e : Fin n ≃ Fin (steps.length+1) × ι) (σ : S) (x : Fin n → ℝ) :
    rootedJointDensity w φ q₀ steps ((flattenDrivers e).symm x) σ =
      w σ * Real.exp (driverQuadratic x - flatPinPotential w hw φ source q₀ steps ha e σ x) := by
  rw [rootedJointDensity_telescope hw, flatPinPotential]
  unfold flatRootFrames flatTerminalFeature
  rw [pathFrames_potential]
  simp only [forwardEnd, rootedIncrements, Fin.cons_zero, Fin.cons_succ, zero_add,
    ContinuousLinearMap.comp_apply, flatLevelProjection_apply]
  congr 2
  ring_nf
  rfl

 theorem flatPinLaw_eq (w : S → ℝ) (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (source : κ → ι → ℝ)
    (q₀ : ι → ℝ≥0) (steps : List (GaussianStep ι)) (ha : OrderedSteps 0 steps)
    (e : Fin n ≃ Fin (steps.length+1) × ι) (σ : S) :
    flatPlantedPinLaw w φ q₀ steps e σ =
      ENNReal.ofReal (w σ * (Real.sqrt (2*Real.pi))⁻¹ ^ n *
        (∫ x, Real.exp (-flatPinPotential w hw φ source q₀ steps ha e σ x))) •
      potentialLaw (flatPinPotential w hw φ source q₀ steps ha e σ) := by
  unfold flatPlantedPinLaw
  simp_rw [flatPin_likelihood w hw φ source q₀ steps ha e σ]
  apply gaussian_tilt_potentialLaw _
    (pinnedPotential_gaussianDominated _ _ _) (fun x => by dsimp only [flatPinPotential]; ring) (hw σ).le
  exact (show Continuous (driverQuadratic (n := n)) from by unfold driverQuadratic; fun_prop).sub
    (pinnedPotential_continuous _ _ _)

 theorem flatPinLaw_normalized (w : S → ℝ) (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (source : κ → ι → ℝ)
    (q₀ : ι → ℝ≥0) (steps : List (GaussianStep ι)) (ha : OrderedSteps 0 steps)
    (e : Fin n ≃ Fin (steps.length+1) × ι) (σ : S) :
    (flatPlantedPinLaw w φ q₀ steps e σ Set.univ)⁻¹ • flatPlantedPinLaw w φ q₀ steps e σ =
      potentialLaw (flatPinPotential w hw φ source q₀ steps ha e σ) := by
  let U := flatPinPotential w hw φ source q₀ steps ha e σ
  have hU : GaussianDominated (fun x => Real.exp (-U x)) := pinnedPotential_gaussianDominated _ _ _
  have : IsProbabilityMeasure (potentialLaw U) := potentialLaw_isProbability hU
  have hc : 0 < w σ * (Real.sqrt (2*Real.pi))⁻¹ ^ n * (∫ x, Real.exp (-U x)) :=
    mul_pos (mul_pos (hw σ) (by positivity)) (positive_integral_exp_neg hU)
  rw [flatPinLaw_eq w hw φ source q₀ steps ha e σ]
  change ((ENNReal.ofReal (w σ * (Real.sqrt (2*Real.pi))⁻¹ ^ n * (∫ x, Real.exp (-U x))) •
    potentialLaw U) Set.univ)⁻¹ •
    (ENNReal.ofReal (w σ * (Real.sqrt (2*Real.pi))⁻¹ ^ n * (∫ x, Real.exp (-U x))) • potentialLaw U) = _
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one, smul_smul,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr hc) ENNReal.ofReal_ne_top, one_smul]
  rfl

 theorem flatPlanted_total_mass (w : S → ℝ) (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (q₀ : ι → ℝ≥0) (steps : List (GaussianStep ι))
    (ha : OrderedSteps 0 steps) (e : Fin n ≃ Fin (steps.length+1) × ι) :
    (∑ σ, flatPlantedPinLaw w φ q₀ steps e σ Set.univ) = 1 := by
  have hσ (σ : S) : flatPlantedPinLaw w φ q₀ steps e σ Set.univ =
      ∫⁻ p, ENNReal.ofReal (rootedJointDensity w φ q₀ steps p σ)
        ∂Measure.pi (fun _ : Fin (steps.length+1) => standardDrivers ι) := by
    rw [flatPlantedPinLaw, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
    rw [← (flattenDrivers_standard e).lintegral_comp_emb
      (flattenDrivers e).toHomeomorph.toMeasurableEquiv.measurableEmbedding]
    simp only [ContinuousLinearEquiv.symm_apply_apply]
  simp_rw [hσ]
  exact rootedJointDensity_normalized hw φ q₀ steps ha

end SKFluctuations.Hierarchy

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Hierarchy
open scoped NNReal Topology BigOperators
variable {n d : ℕ}

def flatSKGauge {L : ℕ} (e : Fin d ≃ Fin (L+1) × FeatureIndex n) (τ : Spin n) :
    (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ) :=
  signEquiv (fun j => featureSigns τ (e j).2) (fun j => featureSigns_sq τ (e j).2)

 theorem scaleDriver_featureGauge (q : FeatureIndex n → ℝ≥0) (τ : Spin n)
    (x : FeatureIndex n → ℝ) :
    scaleDriver q (featureGauge τ x) = featureGauge τ (scaleDriver q x) := by
  ext i
  simp only [scaleDriver_apply, featureGauge, signEquiv_apply]
  ring

 theorem flatLevelProjection_gauge {L : ℕ} (e : Fin d ≃ Fin (L+1) × FeatureIndex n)
    (τ : Spin n) (j : Fin (L+1)) (x : Fin d → ℝ) :
    flatLevelProjection e j (flatSKGauge e τ x) = featureGauge τ (flatLevelProjection e j x) := by
  ext i
  simp only [flatLevelProjection_apply, flattenDrivers_symm_apply, flatSKGauge,
    signEquiv_apply, Equiv.apply_symm_apply, featureGauge]

 theorem pathEndMap_gauge (steps : List (GaussianStep (FeatureIndex n)))
    (D : (Fin d → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (p : Fin steps.length → (Fin d → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (τ : Spin n) (T : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ))
    (hD : ∀ x, D (T x) = featureGauge τ (D x))
    (hp : ∀ j x, p j (T x) = featureGauge τ (p j x)) (x : Fin d → ℝ) :
    pathEndMap steps D p (T x) = featureGauge τ (pathEndMap steps D p x) := by
  induction steps generalizing D with
  | nil => exact hD x
  | cons step tail ih =>
    rcases step with ⟨m,q⟩
    apply ih (D+(scaleDriver q).comp (p 0)) (fun j => p j.succ)
    · intro z
      simp only [add_apply, ContinuousLinearMap.comp_apply, hD, hp,
        scaleDriver_featureGauge, map_add]
    · intro j z
      exact hp j.succ z

 theorem pathFrames_gauge (steps : List (GaussianStep (FeatureIndex n)))
    (a : ℝ) (ha : OrderedSteps a steps)
    (D : (Fin d → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (p : Fin steps.length → (Fin d → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (τ σ : Spin n) (T : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ))
    (hD : ∀ x, D (T x) = featureGauge τ (D x))
    (hp : ∀ j x, p j (T x) = featureGauge τ (p j x)) :
    ∀ j x, let P := pathFrames (uniformWeight n) (uniformWeight_pos n) (finiteFeature n) (spinSource n) steps a ha D p j
      P.potential (T x) = P.potential x ∧
      P.observable (spinGauge τ σ) (T x) = P.observable σ x ∧
      P.energy (spinGauge τ σ) (T x) = P.energy σ x := by
  have hframe (ss : List (GaussianStep (FeatureIndex n))) (b : ℝ) (hb : OrderedSteps b ss)
      (DD : (Fin d → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
      (hDD : ∀ x, DD (T x) = featureGauge τ (DD x)) (x : Fin d → ℝ) :
      let P : PinFrame (FeatureIndex n) (Spin n) (Fin n) d :=
        ⟨uniformWeight n,uniformWeight_pos n,finiteFeature n,ss,b,hb,DD,spinSource n⟩
      P.potential (T x) = P.potential x ∧
      P.observable (spinGauge τ σ) (T x) = P.observable σ x ∧
      P.energy (spinGauge τ σ) (T x) = P.energy σ x := by
    refine ⟨?_, ?_, ?_⟩
    · change finiteSKHierarchy n ss (DD (T x)) = finiteSKHierarchy n ss (DD x)
      rw [hDD, finiteSKHierarchy_gauge]
    · change driverObservable (uniformWeight n) (finiteFeature n) ss
        (ContinuousLinearMap.id ℝ _) (spinSource n) (spinGauge τ σ) (DD (T x)) =
        driverObservable (uniformWeight n) (finiteFeature n) ss
        (ContinuousLinearMap.id ℝ _) (spinSource n) σ (DD x)
      rw [hDD, spinObservable_gauge]
    · change driverEnergy (uniformWeight n) (finiteFeature n) ss
        (ContinuousLinearMap.id ℝ _) (spinSource n) (spinGauge τ σ) (DD (T x)) =
        driverEnergy (uniformWeight n) (finiteFeature n) ss
        (ContinuousLinearMap.id ℝ _) (spinSource n) σ (DD x)
      rw [hDD, spinEnergy_gauge n ss hb]
  induction steps generalizing a D with
  | nil => intro j x; exact hframe [] a ha D hD x
  | cons step tail ih =>
    rcases step with ⟨m,q⟩
    intro j x
    refine Fin.cases (hframe ((m,q)::tail) a ha D hD x) (fun k => ?_) j
    apply ih m ha.2.2.2 (D+(scaleDriver q).comp (p 0)) (fun k => p k.succ) _ _ k x
    · intro z
      simp only [add_apply, ContinuousLinearMap.comp_apply, hD, hp,
        scaleDriver_featureGauge, map_add]
    · intro k z
      exact hp k.succ z

 theorem flatRootFrames_gauge (q₀ : FeatureIndex n → ℝ≥0)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (e : Fin d ≃ Fin (steps.length+1) × FeatureIndex n) (τ σ : Spin n) :
    ∀ j x, let P := flatRootFrames (uniformWeight n) (uniformWeight_pos n) (finiteFeature n) (spinSource n) q₀ steps ha e j
      P.potential (flatSKGauge e τ x) = P.potential x ∧
      P.observable (spinGauge τ σ) (flatSKGauge e τ x) = P.observable σ x ∧
      P.energy (spinGauge τ σ) (flatSKGauge e τ x) = P.energy σ x := by
  apply pathFrames_gauge
  · intro x
    simp only [ContinuousLinearMap.comp_apply, flatLevelProjection_gauge, scaleDriver_featureGauge]
  · intro j x
    exact flatLevelProjection_gauge e τ j.succ x

 theorem flatTerminalFeature_gauge (q₀ : FeatureIndex n → ℝ≥0)
    (steps : List (GaussianStep (FeatureIndex n)))
    (e : Fin d ≃ Fin (steps.length+1) × FeatureIndex n) (τ σ : Spin n) (x : Fin d → ℝ) :
    flatTerminalFeature (finiteFeature n) q₀ steps e (spinGauge τ σ) (flatSKGauge e τ x) =
      flatTerminalFeature (finiteFeature n) q₀ steps e σ x := by
  unfold flatTerminalFeature
  simp only [ContinuousLinearMap.comp_apply]
  rw [pathEndMap_gauge steps _ _ τ (flatSKGauge e τ) _ _, finiteFeature_gauge]
  · intro z
    simp only [ContinuousLinearMap.comp_apply, flatLevelProjection_gauge, scaleDriver_featureGauge]
  · intro j z
    exact flatLevelProjection_gauge e τ j.succ z

 theorem driverQuadratic_flatSKGauge {L : ℕ}
    (e : Fin d ≃ Fin (L+1) × FeatureIndex n) (τ : Spin n) (x : Fin d → ℝ) :
    driverQuadratic (flatSKGauge e τ x) = driverQuadratic x := by
  unfold driverQuadratic
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change (featureSigns τ (e i).2*x i)^2 = (x i)^2
  rw [mul_pow]
  have hi := featureSigns_sq τ (e i).2
  nlinarith [sq_nonneg (x i)]

 theorem flatPinPotential_gauge (q₀ : FeatureIndex n → ℝ≥0)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (e : Fin d ≃ Fin (steps.length+1) × FeatureIndex n) (τ σ : Spin n) (x : Fin d → ℝ) :
    flatPinPotential (uniformWeight n) (uniformWeight_pos n) (finiteFeature n)
      (spinSource n) q₀ steps ha e (spinGauge τ σ) (flatSKGauge e τ x) =
    flatPinPotential (uniformWeight n) (uniformWeight_pos n) (finiteFeature n)
      (spinSource n) q₀ steps ha e σ x := by
  unfold flatPinPotential pinnedPotential
  rw [driverQuadratic_flatSKGauge, flatTerminalFeature_gauge]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [(flatRootFrames_gauge q₀ steps ha e τ σ j x).1]

 theorem flatPinned_joint_test_gauge (q₀ : FeatureIndex n → ℝ≥0)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (e : Fin d ≃ Fin (steps.length+1) × FeatureIndex n) (α k : Fin (steps.length+1) → ℝ)
    (τ σ : Spin n) (f : ℝ × ℝ → ℝ) :
    let P := flatRootFrames (uniformWeight n) (uniformWeight_pos n) (finiteFeature n) (spinSource n) q₀ steps ha e
    let U := flatPinPotential (uniformWeight n) (uniformWeight_pos n) (finiteFeature n) (spinSource n) q₀ steps ha e
    (∫ x, f (pinnedObservable P α k (spinGauge τ σ) x, pinnedEnergy P α k (spinGauge τ σ) x)
      ∂potentialLaw (U (spinGauge τ σ))) =
    ∫ x, f (pinnedObservable P α k σ x, pinnedEnergy P α k σ x) ∂potentialLaw (U σ) := by
  dsimp only
  apply potentialLaw_joint_test_eq (flatSKGauge e τ) (signEquiv_volume _ _)
  · exact flatPinPotential_gauge q₀ steps ha e τ σ
  · intro x
    unfold pinnedObservable
    apply Finset.sum_congr rfl
    intro j _
    rw [(flatRootFrames_gauge q₀ steps ha e τ σ j x).2.1]
  · intro x
    unfold pinnedEnergy
    apply Finset.sum_congr rfl
    intro j _
    rw [(flatRootFrames_gauge q₀ steps ha e τ σ j x).2.2]

end SKFluctuations

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Hierarchy
open scoped NNReal ENNReal Topology BigOperators
variable {n d : ℕ}

abbrev actualPinFrames (q₀ : FeatureIndex n → ℝ≥0)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (e : Fin d ≃ Fin (steps.length+1) × FeatureIndex n) :=
  flatRootFrames (uniformWeight n) (uniformWeight_pos n) (finiteFeature n) (spinSource n) q₀ steps ha e

abbrev actualPinPotential (q₀ : FeatureIndex n → ℝ≥0)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (e : Fin d ≃ Fin (steps.length+1) × FeatureIndex n) :=
  flatPinPotential (uniformWeight n) (uniformWeight_pos n) (finiteFeature n) (spinSource n) q₀ steps ha e

 def actualPinnedPair (q₀ : FeatureIndex n → ℝ≥0)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (e : Fin d ≃ Fin (steps.length+1) × FeatureIndex n) (k : Fin (steps.length+1) → ℝ)
    (σ : Spin n) (x : Fin d → ℝ) : ℝ × ℝ :=
  (pinnedObservable (actualPinFrames q₀ steps ha e) (pathMassDifferences steps 0) k σ x,
    pinnedEnergy (actualPinFrames q₀ steps ha e) (pathMassDifferences steps 0) k σ x)

 theorem actualPinnedPair_continuous (q₀ : FeatureIndex n → ℝ≥0)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (e : Fin d ≃ Fin (steps.length+1) × FeatureIndex n) (k : Fin (steps.length+1) → ℝ)
    (σ : Spin n) : Continuous (actualPinnedPair q₀ steps ha e k σ) :=
  (pinnedObservable_smooth _ _ _ _ 0).continuous.prodMk (pinnedEnergy_smooth _ _ _ _ 0).continuous

 

noncomputable def actualPlantedPairLaw (q₀ : FeatureIndex n → ℝ≥0)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (e : Fin d ≃ Fin (steps.length+1) × FeatureIndex n) (k : Fin (steps.length+1) → ℝ) :
    Measure (ℝ × ℝ) :=
  ∑ σ, (flatPlantedPinLaw (uniformWeight n) (finiteFeature n) q₀ steps e σ).map
    (actualPinnedPair q₀ steps ha e k σ)

 theorem actualPinnedPair_map_eq (q₀ : FeatureIndex n → ℝ≥0)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (e : Fin d ≃ Fin (steps.length+1) × FeatureIndex n) (k : Fin (steps.length+1) → ℝ)
    (σ ρ : Spin n) :
    (potentialLaw (actualPinPotential q₀ steps ha e σ)).map (actualPinnedPair q₀ steps ha e k σ) =
    (potentialLaw (actualPinPotential q₀ steps ha e ρ)).map (actualPinnedPair q₀ steps ha e k ρ) := by
  obtain ⟨τ,hτ⟩ := spinGauge_transitive σ ρ
  have hT := potentialLaw_equiv (flatSKGauge e τ) (signEquiv_volume _ _)
    (flatPinPotential_gauge q₀ steps ha e τ σ)
  rw [← hτ, ← hT.map_eq, Measure.map_map (actualPinnedPair_continuous _ _ _ _ _ _).measurable
    (flatSKGauge e τ).continuous.measurable]
  congr 1
  funext x
  dsimp only [Function.comp_def, actualPinnedPair]
  apply Prod.ext
  · dsimp only
    unfold pinnedObservable
    apply Finset.sum_congr rfl
    intro j _
    rw [(flatRootFrames_gauge q₀ steps ha e τ σ j x).2.1]
  · dsimp only
    unfold pinnedEnergy
    apply Finset.sum_congr rfl
    intro j _
    rw [(flatRootFrames_gauge q₀ steps ha e τ σ j x).2.2]

 

 theorem actualPlantedPairLaw_eq_pin (q₀ : FeatureIndex n → ℝ≥0)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (e : Fin d ≃ Fin (steps.length+1) × FeatureIndex n) (k : Fin (steps.length+1) → ℝ)
    (σ : Spin n) :
    actualPlantedPairLaw q₀ steps ha e k =
      (potentialLaw (actualPinPotential q₀ steps ha e σ)).map (actualPinnedPair q₀ steps ha e k σ) := by
  let c (ρ : Spin n) := ENNReal.ofReal (uniformWeight n ρ * (Real.sqrt (2*Real.pi))⁻¹ ^ d *
    (∫ x, Real.exp (-actualPinPotential q₀ steps ha e ρ x)))
  have hm (ρ : Spin n) : flatPlantedPinLaw (uniformWeight n) (finiteFeature n) q₀ steps e ρ Set.univ = c ρ := by
    have : IsProbabilityMeasure (potentialLaw (actualPinPotential q₀ steps ha e ρ)) :=
      potentialLaw_isProbability (pinnedPotential_gaussianDominated _ _ _)
    rw [flatPinLaw_eq _ (uniformWeight_pos n) _ (spinSource n) _ _ ha e ρ]
    change (c ρ • potentialLaw (actualPinPotential q₀ steps ha e ρ)) Set.univ = c ρ
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  have hc : (∑ ρ, c ρ) = 1 := by
    simpa only [hm] using flatPlanted_total_mass (uniformWeight n) (uniformWeight_pos n)
      (finiteFeature n) q₀ steps ha e
  unfold actualPlantedPairLaw
  have hterm (ρ : Spin n) :
      (flatPlantedPinLaw (uniformWeight n) (finiteFeature n) q₀ steps e ρ).map
        (actualPinnedPair q₀ steps ha e k ρ) =
      c ρ • (potentialLaw (actualPinPotential q₀ steps ha e σ)).map (actualPinnedPair q₀ steps ha e k σ) := by
    rw [flatPinLaw_eq _ (uniformWeight_pos n) _ (spinSource n) _ _ ha e ρ,
      Measure.map_smul _ (actualPinnedPair_continuous _ _ _ _ _ _).measurable.aemeasurable]
    change c ρ • _ = _
    rw [actualPinnedPair_map_eq q₀ steps ha e k ρ σ]
  simp_rw [hterm]
  rw [← Finset.sum_smul, hc, one_smul]

 theorem actualPlantedPairLaw_probability (q₀ : FeatureIndex n → ℝ≥0)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (e : Fin d ≃ Fin (steps.length+1) × FeatureIndex n) (k : Fin (steps.length+1) → ℝ) :
    IsProbabilityMeasure (actualPlantedPairLaw q₀ steps ha e k) := by
  rw [actualPlantedPairLaw_eq_pin q₀ steps ha e k (fun _ => true)]
  have : IsProbabilityMeasure (potentialLaw (actualPinPotential q₀ steps ha e (fun _ => true))) :=
    potentialLaw_isProbability (pinnedPotential_gaussianDominated _ _ _)
  infer_instance

 

 theorem actual_planted_variance_le (q₀ : FeatureIndex n → ℝ≥0)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (e : Fin d ≃ Fin (steps.length+1) × FeatureIndex n) (k : Fin (steps.length+1) → ℝ) :
    variance Prod.fst (actualPlantedPairLaw q₀ steps ha e k) ≤
      ∫ x, x.2 ∂actualPlantedPairLaw q₀ steps ha e k := by
  rw [actualPlantedPairLaw_eq_pin q₀ steps ha e k (fun _ => true)]
  rw [variance_map measurable_fst.aemeasurable
      (actualPinnedPair_continuous _ _ _ _ _ _).measurable.aemeasurable,
    integral_map (actualPinnedPair_continuous _ _ _ _ _ _).measurable.aemeasurable
      continuous_snd.aestronglyMeasurable]
  exact pinned_variance_le (actualPinFrames q₀ steps ha e) (pathMassDifferences_nonneg steps ha)
    k (fun _ => true) (flatTerminalFeature (finiteFeature n) q₀ steps e (fun _ => true))

 
 theorem actual_planted_centered_moment_le (q₀ : FeatureIndex n → ℝ≥0)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (e : Fin d ≃ Fin (steps.length+1) × FeatureIndex n) (k : Fin (steps.length+1) → ℝ)
    {p : ℝ} (hp : 2 ≤ p) :
    let μ := actualPlantedPairLaw q₀ steps ha e k
    (momentNorm μ (fun x => x.1 - ∫ y, y.1 ∂μ) p)^2 ≤
      (1+p^2/3)*momentNorm μ Prod.snd (p/2) := by
  dsimp only
  rw [actualPlantedPairLaw_eq_pin q₀ steps ha e k (fun _ => true)]
  rw [integral_map (actualPinnedPair_continuous _ _ _ _ _ _).measurable.aemeasurable
      continuous_fst.aestronglyMeasurable]
  simp only [momentNorm]
  rw [eLpNorm_map_measure (g := fun x : ℝ × ℝ => x.1 -
      ∫ z, (actualPinnedPair q₀ steps ha e k (fun _ => true) z).1
        ∂potentialLaw (actualPinPotential q₀ steps ha e (fun _ => true)))
      (continuous_fst.sub continuous_const).aestronglyMeasurable
      (actualPinnedPair_continuous _ _ _ _ _ _).measurable.aemeasurable,
    eLpNorm_map_measure continuous_snd.aestronglyMeasurable
      (actualPinnedPair_continuous _ _ _ _ _ _).measurable.aemeasurable]
  exact pinned_centered_moment_le (actualPinFrames q₀ steps ha e) (pathMassDifferences_nonneg steps ha)
    k (fun _ => true) (flatTerminalFeature (finiteFeature n) q₀ steps e (fun _ => true)) hp

end SKFluctuations

end

end OAI
