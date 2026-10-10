import Mathlib
import OAI.Probability.SKFluctuations.ComparisonMinimumMassCenter

namespace OAI

/-! Physical Susceptibility. -/

noncomputable section


namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

omit [Nonempty S] in
 theorem hierarchyMeanPath_terminal [Nonempty S] (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (A : S → ℝ) (steps : List (GaussianStep ι)) {P : Type} (x : P → ι → ℝ)
    (p : P × ForwardPath (ι → ℝ) S steps.length) :
    hierarchyMeanPath w φ A steps x (steps.length+1) p =
      A (ForwardPath.spin steps.length p.2) := by
  induction steps generalizing P with
  | nil => rfl
  | cons st steps ih =>
    exact ih (fun q : P × (ι → ℝ) => x q.1+q.2) ((p.1,p.2.1),p.2.2)

 
def lastLayerCut : List (ℝ × ℕ) → ℕ → ℕ
  | [], j => j
  | (_,k)::cs, _ => lastLayerCut cs k

 
def cutIncrements {E : Type*} [Sub E] : List (ℝ × ℕ) → (ℕ → E) → ℕ → List E
  | [], _, _ => []
  | (_,k)::cs, X, j => (X k-X j)::cutIncrements cs X k

 theorem sum_cutIncrements {E : Type*} [AddCommGroup E] (cs : List (ℝ × ℕ))
    (X : ℕ → E) (j : ℕ) :
    (cutIncrements cs X j).sum = X (lastLayerCut cs j)-X j := by
  induction cs generalizing j with
  | nil => simp only [cutIncrements, lastLayerCut, List.sum_nil, sub_self]
  | cons c cs ih =>
    rcases c with ⟨μ,k⟩
    simp only [cutIncrements, lastLayerCut, List.sum_cons, ih]
    abel

 theorem length_cutIncrements {E : Type*} [Sub E] (cs : List (ℝ × ℕ))
    (X : ℕ → E) (j : ℕ) : (cutIncrements cs X j).length = cs.length := by
  induction cs generalizing j with
  | nil => rfl
  | cons c cs ih => exact congrArg Nat.succ (ih c.2)

 theorem lastLayerCut_shift (cs : List (ℝ × ℕ)) (d j : ℕ) :
    lastLayerCut (cs.map (fun c => (c.1,d+c.2))) (d+j) = d+lastLayerCut cs j := by
  induction cs generalizing j with
  | nil => rfl
  | cons c cs ih => exact ih c.2

omit [Fintype ι] in
 theorem lastLayerCut_schedule [Fintype ι] (bs : List (GaussianLayer ι)) :
    lastLayerCut (layerCutSchedule bs) 0 = (layerSteps bs).length+1 := by
  induction bs with
  | nil => rfl
  | cons B bs ih =>
    rcases B with ⟨μ,pre⟩
    change lastLayerCut ((layerCutSchedule bs).map (fun c => (c.1,pre.length+c.2)))
      (pre.length+0) = (pre++layerSteps bs).length+1
    rw [lastLayerCut_shift, ih, List.length_append]
    omega

omit [Fintype ι] in
 theorem length_layerCutSchedule [Fintype ι] (bs : List (GaussianLayer ι)) :
    (layerCutSchedule bs).length = bs.length+1 := by
  induction bs with
  | nil => rfl
  | cons B bs ih =>
    rcases B with ⟨μ,pre⟩
    simp only [layerCutSchedule, List.length_cons, List.length_map, ih]

end SKFluctuations.Hierarchy
namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Hierarchy
open scoped Topology NNReal BigOperators

 theorem spinProjection_actualSpinPath (n : ℕ) (V : Fin n → ℝ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps)
    {P : Type} (x : P → FeatureIndex n → ℝ) (k : ℕ)
    (p : PhysicalPathState P n steps) :
    (∑ i, V i * actualSpinPath n steps x k p i) =
      hierarchyMeanPath (uniformWeight n) (finiteFeature n) (spinProjection n V) steps x k p := by
  induction steps generalizing a P k with
  | nil =>
    cases k with
    | zero => exact spinProjection_actualSpinMean n V [] ha (x p.1)
    | succ k =>
      change (∑ i, V i * normalizedSpin n p.2 i) = spinProjection n V p.2
      simp only [normalizedSpin,spinProjection,Finset.sum_div,mul_div_assoc]
  | cons st steps ih =>
    cases k with
    | zero => exact spinProjection_actualSpinMean n V (st::steps) ha (x p.1)
    | succ k =>
      exact ih ha.2.2.2 (fun q : P × (FeatureIndex n → ℝ) => x q.1+q.2)
        k ((p.1,p.2.1),p.2.2)

 
def physicalSusceptibility (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    (x : FeatureIndex n → ℝ)
    (p : ForwardPath (FeatureIndex n → ℝ) (Spin n) steps.length) : ℝ :=
  let v := fun i => normalizedSpin n (ForwardPath.spin steps.length p) i-
    actualSpinMean n steps x i
  gaussianHierarchyHessian (uniformWeight n) (finiteFeature n) steps x
    (fieldProjectionDirection n v) (fieldProjectionDirection n v)

 theorem physicalLayerEnergy_projection (n : ℕ)
    (bs : List (GaussianLayer (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a (layerSteps bs))
    (x : FeatureIndex n → ℝ) (V : Fin n → ℝ)
    (p : ForwardPath (FeatureIndex n → ℝ) (Spin n) (layerSteps bs).length) :
    pathLayerEnergy (uniformWeight n) (finiteFeature n) bs x (fieldProjectionDirection n V) p =
      weightedPathIncrements (layerCutSchedule bs)
        (fun k => ∑ i, V i * actualSpinPath n (layerSteps bs) (fun _ : Unit => x) k ((),p) i) 0 := by
  rw [pathLayerEnergy_eq_weightedPathIncrements]
  simp_rw [finiteFeature_fieldProjectionDirection,
    spinProjection_actualSpinPath n V (layerSteps bs) ha]

 theorem actualSpinPath_zero (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {P : Type} (x : P → FeatureIndex n → ℝ) (p : PhysicalPathState P n steps) :
    actualSpinPath n steps x 0 p = WithLp.toLp 2 (actualSpinMean n steps (x p.1)) := by
  ext i
  exact hierarchyMeanPath_zero (uniformWeight n) (finiteFeature n) _ steps x p

 theorem actualSpinPath_terminal (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {P : Type} (x : P → FeatureIndex n → ℝ) (p : PhysicalPathState P n steps) :
    actualSpinPath n steps x (steps.length+1) p =
      WithLp.toLp 2 (normalizedSpin n (ForwardPath.spin steps.length p.2)) := by
  ext i
  exact hierarchyMeanPath_terminal (uniformWeight n) (finiteFeature n) _ steps x p

 

def fieldProjectionLinearMap (n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] (FeatureIndex n → ℝ) where
  toFun := fieldProjectionDirection n
  map_add' V U := by
    ext j
    cases j <;> simp [fieldProjectionDirection, add_div]
  map_smul' c V := by
    ext j
    cases j <;> simp [fieldProjectionDirection, mul_div_assoc]

def physicalLayerVectors (n : ℕ) (bs : List (GaussianLayer (FeatureIndex n)))
    (x : FeatureIndex n → ℝ)
    (p : ForwardPath (FeatureIndex n → ℝ) (Spin n) (layerSteps bs).length) : List (Fin n → ℝ) :=
  cutIncrements (layerCutSchedule bs)
    (fun k i => actualSpinPath n (layerSteps bs) (fun _ : Unit => x) k ((),p) i) 0

 theorem sum_physicalLayerVectors (n : ℕ) (bs : List (GaussianLayer (FeatureIndex n)))
    (x : FeatureIndex n → ℝ)
    (p : ForwardPath (FeatureIndex n → ℝ) (Spin n) (layerSteps bs).length) :
    (physicalLayerVectors n bs x p).sum =
      normalizedSpin n (ForwardPath.spin (layerSteps bs).length p)-actualSpinMean n (layerSteps bs) x := by
  unfold physicalLayerVectors
  rw [sum_cutIncrements, lastLayerCut_schedule]
  simp only [actualSpinPath_terminal, actualSpinPath_zero]

 theorem length_physicalLayerVectors (n : ℕ) (bs : List (GaussianLayer (FeatureIndex n)))
    (x : FeatureIndex n → ℝ)
    (p : ForwardPath (FeatureIndex n → ℝ) (Spin n) (layerSteps bs).length) :
    (physicalLayerVectors n bs x p).length = bs.length+1 := by
  rw [physicalLayerVectors, length_cutIncrements, length_layerCutSchedule]

 

 theorem physicalSusceptibility_le_fork_layers (n : ℕ)
    (bs : List (GaussianLayer (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a (layerSteps bs))
    (hm : ∀ B ∈ bs, ∀ st ∈ B.2, st.1 ≤ B.1) (x : FeatureIndex n → ℝ)
    (p : ForwardPath (FeatureIndex n → ℝ) (Spin n) (layerSteps bs).length) :
    physicalSusceptibility n (layerSteps bs) x p ≤
      (bs.length+1:ℕ) *
      ∑ i : Fin (physicalLayerVectors n bs x p).length,
        ∫ q, weightedPathIncrements (layerCutSchedule bs)
          (fun k => ∑ j, (physicalLayerVectors n bs x p).get i j *
            actualSpinPath n (layerSteps bs) (fun _ : Unit => x) k ((),q) j) 0
          ∂hierarchyPathKernel (uniformWeight n) (finiteFeature n) (layerSteps bs) x := by
  let vs := physicalLayerVectors n bs x p
  have hsum : (∑ i : Fin vs.length, fieldProjectionDirection n (vs.get i)) =
      fieldProjectionDirection n (normalizedSpin n (ForwardPath.spin (layerSteps bs).length p)-
        actualSpinMean n (layerSteps bs) x) := by
    change (∑ i : Fin vs.length, fieldProjectionLinearMap n (vs.get i)) = _
    rw [← map_sum, ← List.sum_ofFn, List.ofFn_get, sum_physicalLayerVectors]
    rfl
  have h := gaussianHierarchyHessian_fork_layer_bound (uniformWeight_pos n) (finiteFeature n)
    bs ha hm x Finset.univ (fun i : Fin vs.length => fieldProjectionDirection n (vs.get i))
  rw [hsum] at h
  simp only [Finset.card_univ, Fintype.card_fin] at h
  simp_rw [← integral_pathLayerEnergy (uniformWeight_pos n) (finiteFeature n) bs ha,
    physicalLayerEnergy_projection n bs ha] at h
  have hlen : vs.length = bs.length+1 := length_physicalLayerVectors n bs x p
  conv at h => rhs; lhs; rw [hlen]
  exact h

end SKFluctuations

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
  [MeasurableSpace S] [StandardBorelSpace S]

omit [Nonempty S] [MeasurableSpace S] [StandardBorelSpace S] in
 theorem pathTailTest_terminal_residual [Nonempty S] [MeasurableSpace S] [StandardBorelSpace S]
    (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (Y : S → ℝ) (pre tail : List (GaussianStep ι)) (k : ℕ) (x : ι → ℝ)
    (p : ForwardPath (ι → ℝ) S (pre++tail).length) :
    pathTailTest pre tail (fun y q =>
      |Y (ForwardPath.spin tail.length q)-gaussianHierarchyMean w φ Y tail y|^(2*k+2)) x p =
      |Y (ForwardPath.spin (pre++tail).length p)-gaussianHierarchyMean w φ Y tail
        (actualCutField pre tail x p)|^(2*k+2) := by
  induction pre generalizing x with
  | nil => rfl
  | cons st pre ih => exact ih (x+p.1) p.2

 

 theorem integral_physical_terminal_residual {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (Y : S → ℝ)
    (pre tail : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a (pre++tail))
    (k : ℕ) (x : ι → ℝ) :
    (∫ p, |Y (ForwardPath.spin (pre++tail).length p)-gaussianHierarchyMean w φ Y tail
      (actualCutField pre tail x p)|^(2*k+2) ∂hierarchyPathKernel w φ (pre++tail) x) =
      ∫ q, hierarchyCenteredEvenMoment w φ Y tail k
        (forwardEnd pre.length (hierarchyIncrements pre) x q) ∂segmentLaw w φ tail pre x := by
  have ht := ha.suffix pre tail
  let C := ∑ σ, |Y σ|
  have hb : ∀ σ, |Y σ| ≤ C := fun σ =>
    Finset.single_le_sum (fun τ _ => abs_nonneg (Y τ)) (Finset.mem_univ σ)
  have hF : Measurable (Function.uncurry (fun (y : ι → ℝ) (q : ForwardPath (ι → ℝ) S tail.length) =>
      |Y (ForwardPath.spin tail.length q)-gaussianHierarchyMean w φ Y tail y|^(2*k+2))) := by
    exact ((((measurable_of_countable Y).comp (ForwardPath.spin_measurable tail.length)).comp
      measurable_snd).sub ((gaussianHierarchyMean_smooth hw φ Y tail ht 0).continuous.measurable.comp
        measurable_fst)).abs.pow_const _
  have hC (y : ι → ℝ) (q : ForwardPath (ι → ℝ) S tail.length) :
      |(|Y (ForwardPath.spin tail.length q)-gaussianHierarchyMean w φ Y tail y|^(2*k+2))| ≤
        (2*C)^(2*k+2) := by
    rw [abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
    apply pow_le_pow_left₀ (abs_nonneg _)
    exact (abs_sub _ _).trans (by
      have := gaussianHierarchyMean_abs_le hw φ hb tail ht y
      have := hb (ForwardPath.spin tail.length q)
      linarith)
  have h := integral_pathTailTest hw φ pre tail ha hF hC
    (hierarchyCenteredEvenMoment_smooth_zero hw φ Y tail ht k)
    (fun y => integral_centered_hierarchyPathKernel hw φ Y tail ht k y) x
  simpa only [pathTailTest_terminal_residual, integral_segmentLaw_test hw φ
    (hierarchyCenteredEvenMoment_smooth_zero hw φ Y tail ht k) tail pre ha x] using h

end SKFluctuations.Hierarchy
namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Hierarchy
open scoped Topology NNReal BigOperators

 
def physicalTerminalIncrement {P : Type} (n : ℕ)
    (tail pre : List (GaussianStep (FeatureIndex n))) (x : P → FeatureIndex n → ℝ)
    (p : PhysicalPathState P n (pre++tail)) : Fin n → ℝ :=
  normalizedSpin n (ForwardPath.spin (pre++tail).length p.2)-
    actualSpinMean n tail (actualCutField pre tail (x p.1) p.2)

 theorem physicalTerminalIncrement_eq_spinPath {P : Type} (n : ℕ)
    (tail pre : List (GaussianStep (FeatureIndex n))) (x : P → FeatureIndex n → ℝ)
    (p : PhysicalPathState P n (pre++tail)) :
    WithLp.toLp 2 (physicalTerminalIncrement n tail pre x p) =
      actualSpinPath n (pre++tail) x ((pre++tail).length+1) p -
      actualSpinPath n (pre++tail) x pre.length p := by
  rw [actualSpinPath_terminal]
  ext i
  change normalizedSpin n (ForwardPath.spin (pre++tail).length p.2) i -
    actualSpinMean n tail (actualCutField pre tail (x p.1) p.2) i = _
  simp only [PiLp.sub_apply, actualSpinPath, hierarchyMeanPath_at_cut, actualSpinMean]

 theorem physicalTerminalIncrement_measurable {P : Type} [MeasurableSpace P] (n : ℕ)
    (tail pre : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a (pre++tail))
    {x : P → FeatureIndex n → ℝ} (hx : Measurable x) :
    Measurable (physicalTerminalIncrement n tail pre x) := by
  exact (((measurable_of_countable (normalizedSpin n)).comp
    (ForwardPath.spin_measurable (pre++tail).length)).comp measurable_snd).sub
      ((actualSpinMean_measurable n tail (ha.suffix pre tail)).comp
        ((actualCutField_measurable_joint pre tail).comp
          ((hx.comp measurable_fst).prodMk measurable_snd)))

 theorem dot_physicalTerminalIncrement {P : Type} (n : ℕ) (V : Fin n → ℝ)
    (tail pre : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a (pre++tail))
    (x : P → FeatureIndex n → ℝ) (p : PhysicalPathState P n (pre++tail)) :
    (∑ i, V i*physicalTerminalIncrement n tail pre x p i) =
      spinProjection n V (ForwardPath.spin (pre++tail).length p.2)-
      gaussianHierarchyMean (uniformWeight n) (finiteFeature n) (spinProjection n V) tail
        (actualCutField pre tail (x p.1) p.2) := by
  simp only [physicalTerminalIncrement, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib,
    spinProjection_actualSpinMean n V tail (ha.suffix pre tail)]
  congr 1
  simp only [normalizedSpin, spinProjection, Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by ring

 theorem physical_terminal_projection_integrable {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (n k : ℕ)
    (tail pre : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ho : OrderedSteps a (pre++tail)) (V : P → Fin n → ℝ) (hV : Measurable V)
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
    (hI : Integrable (fun p => (projectionEuclideanNorm n (V p))^(2*k+2)) μ) :
    Integrable (fun p => |∑ i, V p.1 i * physicalTerminalIncrement n tail pre x p i|^(2*k+2))
      (physicalPathLaw μ n (pre++tail) x hx) := by
  have := hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) (pre++tail) ho
  have hfst : MeasurePreserving (Prod.fst : PhysicalPathState P n (pre++tail) → P)
      (physicalPathLaw μ n (pre++tail) x hx) μ :=
    ⟨measurable_fst, Measure.fst_compProd μ _⟩
  have hb : Integrable (fun p : PhysicalPathState P n (pre++tail) =>
      (2:ℝ)^(2*k+2)*(projectionEuclideanNorm n (V p.1))^(2*k+2))
        (physicalPathLaw μ n (pre++tail) x hx) :=
    (hfst.integrable_comp (((projectionEuclideanNorm_measurable n).comp hV |>.pow_const
      (2*k+2)).const_mul ((2:ℝ)^(2*k+2))).aestronglyMeasurable).mpr (hI.const_mul _)
  have hm : Measurable (fun p : PhysicalPathState P n (pre++tail) =>
      ∑ i, V p.1 i * physicalTerminalIncrement n tail pre x p i) := by
    apply Finset.measurable_sum
    intro i _
    exact ((measurable_pi_apply i).comp (hV.comp measurable_fst)).mul
      ((measurable_pi_apply i).comp (physicalTerminalIncrement_measurable n tail pre ho hx))
  apply hb.mono' (hm.abs.pow_const _).aestronglyMeasurable
  exact Eventually.of_forall fun p => by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _),
      dot_physicalTerminalIncrement n (V p.1) tail pre ho x p]
    have ht := ho.suffix pre tail
    have hmean := gaussianHierarchyMean_abs_le (uniformWeight_pos n) (finiteFeature n)
      (spinProjection_abs_le n (V p.1)) tail ht (actualCutField pre tail (x p.1) p.2)
    have hspin := spinProjection_abs_le n (V p.1) (ForwardPath.spin (pre++tail).length p.2)
    have hp := pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans
      (add_le_add hspin hmean)) (2*k+2)
    exact hp.trans_eq (by rw [← two_mul, mul_pow])

 

 theorem eventually_physical_terminal_projection (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Type) [MeasurableSpace P]
      (tail pre : List (GaussianStep (FeatureIndex n)))
      (a D : ℝ), 0 < a → 0 < D → D ≤ B → OrderedSteps a (pre++tail) →
    ∀ (μ : Measure P) [IsFiniteMeasure μ] (V : P → Fin n → ℝ) (_hV : Measurable V)
      (x : P → FeatureIndex n → ℝ) (hx : Measurable x),
      Integrable (fun p => (projectionEuclideanNorm n (V p))^(2*k+2)) μ →
      (∀ p, AlignedFieldClock (fieldProjectionDirection n (V p)) D pre) →
    (∫ p, |∑ i, V p.1 i * physicalTerminalIncrement n tail pre x p i|^(2*k+2)
      ∂physicalPathLaw μ n (pre++tail) x hx) ≤
      (projectionLpConstant k*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*D)))^(2*k+2)*
        ∫ p, (projectionEuclideanNorm n (V p))^(2*k+2) ∂μ := by
  filter_upwards [eventually_finiteSK_projection k B] with n hn
  intro P _ tail pre a D ha hD hDB ho μ _ V hV x hx hI hc
  have := hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) (pre++tail) ho
  have hi := physical_terminal_projection_integrable μ n k tail pre ho V hV x hx hI
  let C := (projectionLpConstant k*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*D)))^(2*k+2)
  have hp (p : P) : (∫ q, |∑ i, V p i * physicalTerminalIncrement n tail pre x (p,q) i|^(2*k+2)
      ∂hierarchyPathKernel (uniformWeight n) (finiteFeature n) (pre++tail) (x p)) ≤
      C*(projectionEuclideanNorm n (V p))^(2*k+2) := by
    simp_rw [dot_physicalTerminalIncrement n (V p) tail pre ho x]
    rw [integral_physical_terminal_residual (uniformWeight_pos n) (finiteFeature n)
      (spinProjection n (V p)) pre tail ho k (x p)]
    have h0 : 0 ≤ ∫ q, hierarchyCenteredEvenMoment (uniformWeight n) (finiteFeature n)
        (spinProjection n (V p)) tail k
        (forwardEnd pre.length (hierarchyIncrements pre) (x p) q)
        ∂segmentLaw (uniformWeight n) (finiteFeature n) tail pre (x p) :=
      integral_nonneg fun q => hierarchyCenteredEvenMoment_nonneg (uniformWeight_pos n)
        (finiteFeature n) _ tail (ho.suffix pre tail) k _
    have hh := hn (V p) tail pre a D ha hD hDB ho (hc p) (x p)
    have hh' := pow_le_pow_left₀ (Real.rpow_nonneg h0 _) hh (2*k+2)
    rw [Real.rpow_inv_natCast_pow h0 (by omega : 2*k+2 ≠ 0)] at hh'
    exact hh'.trans_eq (by dsimp [C]; rw [← mul_pow]; congr 1; ring)
  change (∫ p, |∑ i, V p.1 i * physicalTerminalIncrement n tail pre x p i|^(2*k+2)
      ∂(μ ⊗ₘ (hierarchyPathKernel (uniformWeight n) (finiteFeature n) (pre++tail)).comap x hx)) ≤ _
  rw [Measure.integral_compProd hi, ← integral_const_mul]
  exact integral_mono hi.integral_compProd (hI.const_mul _) hp

 

theorem eventually_physical_suffix_terminal_projection (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Type) [MeasurableSpace P]
      (tail pre skip : List (GaussianStep (FeatureIndex n)))
      (a a₀ D : ℝ), 0 < a → 0 < D → D ≤ B →
      OrderedSteps a (pre++tail) →
      OrderedSteps a₀ ((skip++pre)++tail) →
    ∀ (μ : Measure P) [IsFiniteMeasure μ] (V : P → Fin n → ℝ) (_hV : Measurable V)
      (x : P → FeatureIndex n → ℝ) (hx : Measurable x),
      Integrable (fun p => (projectionEuclideanNorm n (V p))^(2*k+2)) μ →
      (∀ p, AlignedFieldClock (fieldProjectionDirection n (V p)) D pre) →
    (∫ p, |∑ i, V p.1 i * physicalTerminalIncrement n tail (skip++pre) x p i|^(2*k+2)
      ∂physicalPathLaw μ n ((skip++pre)++tail) x hx) ≤
      (projectionLpConstant k*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*D)))^(2*k+2)*
        ∫ p, (projectionEuclideanNorm n (V p))^(2*k+2) ∂μ := by
  filter_upwards [eventually_physical_terminal_projection k B] with n hn
  intro P _ tail pre skip a a₀ D ha hD hDB ho hs μ _ V hV x hx hI hc
  induction skip generalizing P a₀ with
  | nil => exact hn P tail pre a D ha hD hDB ho μ V hV x hx hI hc
  | cons st skip ih =>
    rcases st with ⟨m,q⟩
    let rest := (skip++pre)++tail
    have hstep : OrderedSteps a₀ ((m,q)::rest) := hs
    have := plantedStepKernel_markov (uniformWeight_pos n) (finiteFeature n) m q rest hstep
    let μ' := μ ⊗ₘ (plantedStepKernel (uniformWeight n) (finiteFeature n) m q rest).comap x hx
    let x' : P × (FeatureIndex n → ℝ) → FeatureIndex n → ℝ := fun p => x p.1+p.2
    have hx' : Measurable x' := (hx.comp measurable_fst).add measurable_snd
    let V' : P × (FeatureIndex n → ℝ) → Fin n → ℝ := fun p => V p.1
    have hV' : Measurable V' := hV.comp measurable_fst
    have hfst : MeasurePreserving (Prod.fst : P × (FeatureIndex n → ℝ) → P) μ' μ :=
      ⟨measurable_fst, Measure.fst_compProd μ _⟩
    have hI' : Integrable (fun p => (projectionEuclideanNorm n (V' p))^(2*k+2)) μ' := by
      exact (hfst.integrable_comp
        (((projectionEuclideanNorm_measurable n).comp hV).pow_const _).aestronglyMeasurable).mpr hI
    have hmoment : (∫ p, (projectionEuclideanNorm n (V' p))^(2*k+2) ∂μ') =
        ∫ p, (projectionEuclideanNorm n (V p))^(2*k+2) ∂μ := by
      change (∫ p, (projectionEuclideanNorm n (V p.1))^(2*k+2) ∂μ') = _
      have he := integral_map (μ := μ')
        (φ := (Prod.fst : P × (FeatureIndex n → ℝ) → P)) measurable_fst.aemeasurable
        (((projectionEuclideanNorm_measurable n).comp hV).pow_const (2*k+2)).aestronglyMeasurable
      rw [hfst.map_eq] at he
      exact he.symm
    have hh := ih (P × (FeatureIndex n → ℝ)) m hstep.2.2.2 μ' V' hV' x' hx' hI' (fun p => hc p.1)
    rw [hmoment] at hh
    let ν := physicalPathLaw μ n (((m,q)::skip++pre)++tail) x hx
    let e : PhysicalPathState P n (((m,q)::skip++pre)++tail) ≃ᵐ
        PhysicalPathState (P × (FeatureIndex n → ℝ)) n rest := MeasurableEquiv.prodAssoc.symm
    have hmap : ν.map e = physicalPathLaw μ' n rest x' hx' :=
      hierarchyPathLaw_cons (uniformWeight_pos n) (finiteFeature n) m q rest hstep μ x hx
    let F : PhysicalPathState (P × (FeatureIndex n → ℝ)) n rest → ℝ :=
      fun p => |∑ i, V' p.1 i * physicalTerminalIncrement n tail (skip++pre) x' p i|^(2*k+2)
    have hF : Measurable F := by
      apply Measurable.pow_const
      apply Measurable.abs
      apply Finset.measurable_sum
      intro i _
      exact ((measurable_pi_apply i).comp (hV'.comp measurable_fst)).mul
        ((measurable_pi_apply i).comp (physicalTerminalIncrement_measurable n tail
          (skip++pre) hstep.2.2.2 hx'))
    have heq : (∫ p, F (e p) ∂ν) = ∫ p, F p ∂physicalPathLaw μ' n rest x' hx' := by
      rw [← integral_map e.measurable.aemeasurable hF.aestronglyMeasurable, hmap]
    change (∫ p, F (e p) ∂ν) ≤ _
    rw [heq]
    exact hh

 theorem norm_physicalTerminalIncrement {P : Type} (n : ℕ)
    (tail pre : List (GaussianStep (FeatureIndex n))) (x : P → FeatureIndex n → ℝ)
    (p : PhysicalPathState P n (pre++tail)) :
    projectionEuclideanNorm n (physicalTerminalIncrement n tail pre x p) =
      ‖actualSpinPath n (pre++tail) x ((pre++tail).length+1) p -
        actualSpinPath n (pre++tail) x pre.length p‖ := by
  rw [← physicalTerminalIncrement_eq_spinPath, EuclideanSpace.norm_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  rfl

 theorem physicalTerminalIncrement_moment_integrable {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (n k : ℕ)
    (tail pre : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a (pre++tail)) (x : P → FeatureIndex n → ℝ) (hx : Measurable x) :
    Integrable (fun p => (projectionEuclideanNorm n (physicalTerminalIncrement n tail pre x p))^(2*k+2))
      (physicalPathLaw μ n (pre++tail) x hx) := by
  have := physicalPathLaw_finite μ n (pre++tail) ha x hx
  apply Integrable.of_bound
    (((projectionEuclideanNorm_measurable n).comp
      (physicalTerminalIncrement_measurable n tail pre ha hx)).pow_const _).aestronglyMeasurable
    ((2:ℝ)^(2*k+2))
  exact Eventually.of_forall fun p => by
    rw [Real.norm_eq_abs]
    change |(projectionEuclideanNorm n (physicalTerminalIncrement n tail pre x p))^(2*k+2)| ≤ _
    rw [abs_of_nonneg (pow_nonneg (show 0 ≤ projectionEuclideanNorm n
      (physicalTerminalIncrement n tail pre x p) from Real.sqrt_nonneg _) _),
      norm_physicalTerminalIncrement]
    apply pow_le_pow_left₀ (norm_nonneg _)
    have h₁ := actualSpinPath_norm_le n (pre++tail) ha x ((pre++tail).length+1) p
    have h₂ := actualSpinPath_norm_le n (pre++tail) ha x pre.length p
    exact (norm_sub_le _ _).trans (by linarith)

end SKFluctuations

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

 theorem bounded_kernel_power_le {P A : Type*} [MeasurableSpace P] [MeasurableSpace A]
    (μ : Measure P) [IsFiniteMeasure μ] (κ : Kernel P A) [IsMarkovKernel κ]
    {F : P × A → ℝ} (hF : Measurable F) {R : ℝ}
    (hF0 : ∀ z, 0 ≤ F z) (hFR : ∀ z, F z ≤ R) {p : ℕ} (hp : 0 < p) :
    (∫ z, (∫ a, F (z,a) ∂κ z)^p ∂μ) ≤ ∫ z, (F z)^p ∂μ ⊗ₘ κ := by
  have hFp : Measurable (fun z => (F z)^p) := hF.pow_const p
  have hi : Integrable (fun z => (F z)^p) (μ ⊗ₘ κ) :=
    Integrable.of_bound hFp.aestronglyMeasurable (R^p) (Eventually.of_forall fun z => by
      rw [Real.norm_of_nonneg (pow_nonneg (hF0 z) p)]
      exact pow_le_pow_left₀ (hF0 z) (hFR z) p)
  have houter : Integrable (fun z => (∫ a, F (z,a) ∂κ z)^p) μ := by
    apply Integrable.of_bound
      (hF.stronglyMeasurable.integral_kernel_prod_right'.pow p).aestronglyMeasurable (R^p)
    apply Eventually.of_forall
    intro z
    have hip : Integrable (fun a => F (z,a)) (κ z) :=
      Integrable.of_bound (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable R
        (Eventually.of_forall fun a => by rw [Real.norm_of_nonneg (hF0 _)]; exact hFR _)
    have h0 : 0 ≤ ∫ a, F (z,a) ∂κ z := integral_nonneg (fun a => hF0 _)
    have h1 : (∫ a, F (z,a) ∂κ z) ≤ R := by
      calc
        _ ≤ ∫ _ : A, R ∂κ z := integral_mono hip (integrable_const R) (fun a => hFR _)
        _ = R := by simp
    change ‖(∫ a, F (z,a) ∂κ z)^p‖ ≤ R^p
    rw [Real.norm_of_nonneg (pow_nonneg h0 p)]
    exact pow_le_pow_left₀ h0 h1 p
  rw [Measure.integral_compProd hi]
  have hjoint : Integrable (fun z => ∫ a, (F (z,a))^p ∂κ z) μ := by
    have hnorm := (Measure.integrable_compProd_iff hi.aestronglyMeasurable).mp hi |>.2
    simpa only [Real.norm_of_nonneg (pow_nonneg (hF0 _) p)] using hnorm
  apply integral_mono_ae houter hjoint
  apply Eventually.of_forall
  intro z
  have hip : Integrable (fun a => F (z,a)) (κ z) :=
    Integrable.of_bound (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable R
      (Eventually.of_forall fun a => by rw [Real.norm_of_nonneg (hF0 _)]; exact hFR _)
  have hipp : Integrable (fun a => (F (z,a))^p) (κ z) :=
    Integrable.of_bound (hFp.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable (R^p)
      (Eventually.of_forall fun a => by
        rw [Real.norm_of_nonneg (pow_nonneg (hF0 _) p)]
        exact pow_le_pow_left₀ (hF0 _) (hFR _) p)
  simpa using integral_pow_le_mass (κ z) (Eventually.of_forall fun a => hF0 _) hip hp hipp

end SKFluctuations.Hierarchy

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 

theorem eventually_physical_suffix_random_projection (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Type) [MeasurableSpace P]
      (tail mid pre skip : List (GaussianStep (FeatureIndex n)))
      (a a₀ D : ℝ), 0 < a → 0 < D → D ≤ B →
      OrderedSteps a (pre++(mid++tail)) →
      OrderedSteps a₀ ((skip++pre)++(mid++tail)) →
    ∀ (μ : Measure P) [IsFiniteMeasure μ] (V : P → Fin n → ℝ) (_hV : Measurable V)
      (x : P → FeatureIndex n → ℝ) (hx : Measurable x),
      Integrable (fun p => (projectionEuclideanNorm n (V p))^(2*k+2)) μ →
      (∀ p, AlignedFieldClock (fieldProjectionDirection n (V p)) D pre) →
    (∫ p, |∑ i, V p.1 i * physicalPairIncrement n tail mid (skip++pre) x p i|^(2*k+2)
      ∂physicalPathLaw μ n ((skip++pre)++(mid++tail)) x hx) ≤
      (projectionLpConstant k*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*D)))^(2*k+2)*
        ∫ p, (projectionEuclideanNorm n (V p))^(2*k+2) ∂μ := by
  filter_upwards [eventually_physical_random_projection k B] with n hn
  intro P _ tail mid pre skip a a₀ D ha hD hDB ho hs μ _ V hV x hx hI hc
  induction skip generalizing P a₀ with
  | nil => exact hn P tail mid pre a D ha hD hDB ho μ V hV x hx hI hc
  | cons st skip ih =>
    rcases st with ⟨m,q⟩
    let rest := (skip++pre)++(mid++tail)
    have hstep : OrderedSteps a₀ ((m,q)::rest) := hs
    have := plantedStepKernel_markov (uniformWeight_pos n) (finiteFeature n) m q rest hstep
    let μ' := μ ⊗ₘ (plantedStepKernel (uniformWeight n) (finiteFeature n) m q rest).comap x hx
    let x' : P × (FeatureIndex n → ℝ) → FeatureIndex n → ℝ := fun p => x p.1+p.2
    have hx' : Measurable x' := (hx.comp measurable_fst).add measurable_snd
    let V' : P × (FeatureIndex n → ℝ) → Fin n → ℝ := fun p => V p.1
    have hV' : Measurable V' := hV.comp measurable_fst
    have hfst : MeasurePreserving (Prod.fst : P × (FeatureIndex n → ℝ) → P) μ' μ :=
      ⟨measurable_fst, Measure.fst_compProd μ _⟩
    have hI' : Integrable (fun p => (projectionEuclideanNorm n (V' p))^(2*k+2)) μ' := by
      exact (hfst.integrable_comp
        (((projectionEuclideanNorm_measurable n).comp hV).pow_const _).aestronglyMeasurable).mpr hI
    have hmoment : (∫ p, (projectionEuclideanNorm n (V' p))^(2*k+2) ∂μ') =
        ∫ p, (projectionEuclideanNorm n (V p))^(2*k+2) ∂μ := by
      change (∫ p, (projectionEuclideanNorm n (V p.1))^(2*k+2) ∂μ') = _
      have he := integral_map (μ := μ')
        (φ := (Prod.fst : P × (FeatureIndex n → ℝ) → P)) measurable_fst.aemeasurable
        (((projectionEuclideanNorm_measurable n).comp hV).pow_const (2*k+2)).aestronglyMeasurable
      rw [hfst.map_eq] at he
      exact he.symm
    have hh := ih (P × (FeatureIndex n → ℝ)) m hstep.2.2.2 μ' V' hV' x' hx' hI' (fun p => hc p.1)
    rw [hmoment] at hh
    let ν := physicalPathLaw μ n (((m,q)::skip++pre)++(mid++tail)) x hx
    let e : PhysicalPathState P n (((m,q)::skip++pre)++(mid++tail)) ≃ᵐ
        PhysicalPathState (P × (FeatureIndex n → ℝ)) n rest := MeasurableEquiv.prodAssoc.symm
    have hmap : ν.map e = physicalPathLaw μ' n rest x' hx' :=
      hierarchyPathLaw_cons (uniformWeight_pos n) (finiteFeature n) m q rest hstep μ x hx
    let F : PhysicalPathState (P × (FeatureIndex n → ℝ)) n rest → ℝ :=
      fun p => |∑ i, V' p.1 i * physicalPairIncrement n tail mid (skip++pre) x' p i|^(2*k+2)
    have hF : Measurable F := by
      apply Measurable.pow_const
      apply Measurable.abs
      apply Finset.measurable_sum
      intro i _
      exact ((measurable_pi_apply i).comp (hV'.comp measurable_fst)).mul
        ((measurable_pi_apply i).comp (physicalPairIncrement_measurable n tail mid
          (skip++pre) hstep.2.2.2 hx'))
    have heq : (∫ p, F (e p) ∂ν) = ∫ p, F p ∂physicalPathLaw μ' n rest x' hx' := by
      rw [← integral_map e.measurable.aemeasurable hF.aestronglyMeasurable, hmap]
    change (∫ p, F (e p) ∂ν) ≤ _
    rw [heq]
    exact hh

end SKFluctuations

end

end OAI
