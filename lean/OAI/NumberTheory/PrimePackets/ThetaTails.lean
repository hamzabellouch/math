import Mathlib
import OAI.NumberTheory.PrimePackets.LatticeTheta

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

 

theorem thetaRemainder_uniform_exponential_bound (R : ℝ) (hR : 0 ≤ R) :
    ∃ a C : ℝ, 0 < a ∧ 0 ≤ C ∧
      ∀ (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d),
        ‖B.symm.toContinuousLinearMap‖ ≤ R → ∀ t : ℝ, 1 ≤ t →
          ‖thetaRemainder B t‖ ≤ C * Real.exp (-a*t) := by
  let c : ℝ := (R+1)⁻¹
  have hc : 0 < c := inv_pos.mpr (by linarith)
  let a : ℝ := c^2/2
  have ha : 0 < a := by dsimp [a]; positivity
  let v := fun z : NonzeroIntegerVector d => Real.exp (-a*‖euclideanInteger z.1‖^2)
  have hv : Summable v := by
    have H := (thetaRemainder_summable (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ d)) ha).norm
    simpa only [ContinuousLinearEquiv.refl_apply,gaussianTerm_norm] using H
  refine ⟨a,∑' z, v z,ha,tsum_nonneg (fun z => (Real.exp_pos _).le),fun B hB t ht => ?_⟩
  have hbound (z : NonzeroIntegerVector d) : c*‖euclideanInteger z.1‖ ≤ ‖B (euclideanInteger z.1)‖ := by
    have H := B.symm.toContinuousLinearMap.le_opNorm (B (euclideanInteger z.1))
    simp only [ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply] at H
    have HR : 0 < R+1 := by linarith
    rw [show c*‖euclideanInteger z.1‖ = ‖euclideanInteger z.1‖/(R+1) by dsimp [c]; ring,
      div_le_iff₀ HR]
    calc
      ‖euclideanInteger z.1‖ ≤ ‖B.symm.toContinuousLinearMap‖ * ‖B (euclideanInteger z.1)‖ := H
      _ ≤ ‖B (euclideanInteger z.1)‖*(R+1) := by nlinarith [norm_nonneg (B (euclideanInteger z.1))]
  have ht' : 0 < t := by linarith
  calc
    ‖thetaRemainder B t‖ ≤ ∑' z : NonzeroIntegerVector d,
        ‖Complex.exp (-(t:ℂ)*‖B (euclideanInteger z.1)‖^2)‖ :=
      norm_tsum_le_tsum_norm (thetaRemainder_summable B ht').norm
    _ ≤ ∑' z, v z * Real.exp (-a*t) := by
      apply (thetaRemainder_summable B ht').norm.tsum_le_tsum _ (hv.mul_right _)
      intro z
      rw [gaussianTerm_norm]
      dsimp only [v]
      rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hx := euclideanInteger_norm_one_le z
      have hy := hbound z
      have hx2 : 1 ≤ ‖euclideanInteger z.1‖^2 := by nlinarith
      have hcsq : c^2 * ‖euclideanInteger z.1‖^2 ≤ ‖B (euclideanInteger z.1)‖^2 := by
        have H := (sq_le_sq₀ (mul_nonneg hc.le (norm_nonneg _)) (norm_nonneg _)).mpr hy
        simpa only [mul_pow] using H
      have h1 := mul_nonneg (sub_nonneg.mpr ht) (mul_nonneg (sq_nonneg c)
        (sq_nonneg ‖euclideanInteger z.1‖))
      have h2 := mul_nonneg ht'.le (sub_nonneg.mpr hcsq)
      have h3 := mul_nonneg (sq_nonneg c) (sub_nonneg.mpr hx2)
      have h4 := mul_nonneg ht'.le h3
      dsimp only [a]
      nlinarith
    _ = _ := tsum_mul_right

end PrimeDegreePackets.ThetaConstruction


namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
variable (B : α → EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)

omit [IsFiniteMeasure μ] in
lemma normalizedThetaTail_joint_stronglyMeasurable
    (hB : ∀ z : d → ℤ, Measurable (fun x => B x (euclideanInteger z))) :
    StronglyMeasurable (fun p : α × ℝ => normalizedThetaTail (B p.1) p.2) := by
  have HH : Measurable (fun p : α × ℝ => thetaRemainder (B p.1) (Real.pi*max p.2 1)) := by
    unfold thetaRemainder
    apply Measurable.tsum
    intro z
    have HB : Measurable (fun p : α × ℝ => B p.1 (euclideanInteger z.1)) :=
      (hB z.1).comp measurable_fst
    fun_prop
  have HP : MeasurableSet {p : α × ℝ | 1 < p.2} :=
    measurableSet_lt measurable_const measurable_snd
  apply Measurable.stronglyMeasurable
  convert HH.indicator HP using 1
  ext p
  simp only [normalizedThetaTail,Set.indicator_apply]
  rfl

 
def averagedNormalizedThetaTail (t : ℝ) : ℂ := ∫ x, normalizedThetaTail (B x) t ∂μ

omit [IsFiniteMeasure μ] in
lemma averagedNormalizedThetaTail_eq_zero {t : ℝ} (ht : t ≤ 1) :
    averagedNormalizedThetaTail μ B t = 0 := by
  simp [averagedNormalizedThetaTail,normalizedThetaTail,not_lt.mpr ht]

lemma averagedNormalizedThetaTail_stronglyMeasurable
    (hB : StronglyMeasurable (fun p : α × ℝ => normalizedThetaTail (B p.1) p.2)) :
    StronglyMeasurable (averagedNormalizedThetaTail μ B) :=
  hB.integral_prod_left'

lemma averagedNormalizedThetaTail_bounds (R : ℝ) (hR : 0 ≤ R)
    (hB : ∀ x, ‖(B x).symm.toContinuousLinearMap‖ ≤ R) :
    ∃ a C : ℝ, 0 < a ∧ 0 ≤ C ∧
      (∀ t : ℝ, ‖averagedNormalizedThetaTail μ B t‖ ≤ C) ∧
      ∀ t : ℝ, 1 < t → ‖averagedNormalizedThetaTail μ B t‖ ≤ C * Real.exp (-a*t) := by
  obtain ⟨a,C,ha,hC,hbound⟩ := thetaRemainder_uniform_exponential_bound (d := d) R hR
  have Hb (t : ℝ) (ht : 1 < t) :
      ‖averagedNormalizedThetaTail μ B t‖ ≤ (C*μ.real Set.univ) * Real.exp (-(a*Real.pi)*t) := by
    have HP : 1 ≤ Real.pi*t := by nlinarith [Real.pi_gt_three]
    have HH := norm_integral_le_of_norm_le_const (μ := μ)
      (Filter.Eventually.of_forall (fun x => hbound (B x) (hB x) (Real.pi*t) HP))
    have HE : averagedNormalizedThetaTail μ B t = ∫ x, thetaRemainder (B x) (Real.pi*t) ∂μ := by
      simp only [averagedNormalizedThetaTail,normalizedThetaTail,
        Set.indicator_of_mem (show t ∈ Set.Ioi 1 from ht),max_eq_left ht.le]
    rw [HE]
    rw [show -a*(Real.pi*t) = -(a*Real.pi)*t by ring] at HH
    simpa only [mul_assoc,mul_left_comm,mul_comm] using HH
  refine ⟨a*Real.pi,C*μ.real Set.univ,mul_pos ha Real.pi_pos,
    mul_nonneg hC (measureReal_nonneg),?_,Hb⟩
  intro t
  by_cases ht : 1 < t
  · apply (Hb t ht).trans
    apply mul_le_of_le_one_right (mul_nonneg hC (measureReal_nonneg))
    rw [Real.exp_le_one_iff]
    have := mul_pos (mul_pos ha Real.pi_pos) (zero_lt_one.trans ht)
    nlinarith
  · rw [averagedNormalizedThetaTail_eq_zero μ B (not_lt.mp ht),norm_zero]
    positivity

lemma averagedNormalizedThetaTail_locallyIntegrable (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ x, ‖(B x).symm.toContinuousLinearMap‖ ≤ R)
    (hB : StronglyMeasurable (fun p : α × ℝ => normalizedThetaTail (B p.1) p.2)) :
    LocallyIntegrable (averagedNormalizedThetaTail μ B) := by
  obtain ⟨a,C,ha,hC,hall,_⟩ := averagedNormalizedThetaTail_bounds μ B R hR hbound
  rw [locallyIntegrable_iff]
  intro k hk
  have : IsFiniteMeasure (volume.restrict k) := isFiniteMeasure_restrict.mpr hk.measure_lt_top.ne
  exact (integrable_const C).mono'
    (averagedNormalizedThetaTail_stronglyMeasurable μ B hB).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun t => hall t))

omit [IsFiniteMeasure μ] in
lemma averagedNormalizedThetaTail_bigO_zero (b : ℝ) :
    averagedNormalizedThetaTail μ B =O[𝓝[>] 0] (fun t : ℝ => t^(-b)) := by
  apply IsBigO.of_bound 0
  have H : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds zero_lt_one)
  filter_upwards [H] with t ht
  simp [averagedNormalizedThetaTail_eq_zero μ B ht.le]

 

theorem averagedNormalizedThetaTail_mellin_differentiable (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ x, ‖(B x).symm.toContinuousLinearMap‖ ≤ R)
    (hB : StronglyMeasurable (fun p : α × ℝ => normalizedThetaTail (B p.1) p.2)) :
    Differentiable ℂ (mellin (averagedNormalizedThetaTail μ B)) := by
  obtain ⟨a,C,ha,_,_,hdecay⟩ := averagedNormalizedThetaTail_bounds μ B R hR hbound
  have Hdecay : averagedNormalizedThetaTail μ B =O[atTop] (fun t => Real.exp (-a*t)) := by
    apply IsBigO.of_bound C
    filter_upwards [eventually_gt_atTop (1:ℝ)] with t ht
    simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using hdecay t ht
  intro s
  exact mellin_differentiableAt_of_isBigO_rpow_exp ha
    ((averagedNormalizedThetaTail_locallyIntegrable μ B R hR hbound hB).locallyIntegrableOn (Set.Ioi 0))
    Hdecay (averagedNormalizedThetaTail_bigO_zero μ B (s.re-1)) (by linarith)

end PrimeDegreePackets.ThetaConstruction


namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

 
def logScaleLinearEquiv (u : d → ℝ) : EuclideanSpace ℝ d ≃ₗ[ℝ] EuclideanSpace ℝ d where
  toFun x := toLp 2 (fun i => Real.exp (u i)*x i)
  invFun x := toLp 2 (fun i => Real.exp (-u i)*x i)
  map_add' x y := by ext i; simp [mul_add]
  map_smul' a x := by ext i; simp [mul_left_comm]
  left_inv x := by
    ext i
    change Real.exp (-u i)*(Real.exp (u i)*x i) = x i
    rw [←mul_assoc,←Real.exp_add,neg_add_cancel,Real.exp_zero,one_mul]
  right_inv x := by
    ext i
    change Real.exp (u i)*(Real.exp (-u i)*x i) = x i
    rw [←mul_assoc,←Real.exp_add,add_neg_cancel,Real.exp_zero,one_mul]

def logScale (u : d → ℝ) : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d :=
  (logScaleLinearEquiv u).toContinuousLinearEquiv

@[simp] lemma logScale_apply (u : d → ℝ) (x : EuclideanSpace ℝ d) (i : d) :
    logScale u x i = Real.exp (u i)*x i := rfl

@[simp] lemma logScale_symm_apply (u : d → ℝ) (x : EuclideanSpace ℝ d) (i : d) :
    (logScale u).symm x i = Real.exp (-u i)*x i := rfl

lemma logScale_symm (u : d → ℝ) : (logScale u).symm = logScale (-u) := by
  ext x i
  rfl

lemma logScale_norm_le {u : d → ℝ} {R : ℝ} (hR : ∀ i, u i ≤ R)
    (x : EuclideanSpace ℝ d) : ‖logScale u x‖ ≤ Real.exp R*‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))).mp
  rw [mul_pow,EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [logScale_apply,mul_pow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact (sq_le_sq₀ (Real.exp_pos _).le (Real.exp_pos _).le).mpr (Real.exp_le_exp.mpr (hR i))

lemma logScale_opNorm_le {u : d → ℝ} {R : ℝ} (hR : ∀ i, u i ≤ R) :
    ‖(logScale u).toContinuousLinearMap‖ ≤ Real.exp R := by
  exact ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le (logScale_norm_le hR)

 
def logScaledLattice (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (u : d → ℝ) := B.trans (logScale u)

lemma logScaledLattice_inverse_bound (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    {u : d → ℝ} {R : ℝ} (hR : ∀ i, -u i ≤ R) :
    ‖(logScaledLattice B u).symm.toContinuousLinearMap‖ ≤
      ‖B.symm.toContinuousLinearMap‖*Real.exp R := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
  intro x
  change ‖B.symm ((logScale u).symm x)‖ ≤ _
  calc
    _ ≤ ‖B.symm.toContinuousLinearMap‖*‖(logScale u).symm x‖ :=
      B.symm.toContinuousLinearMap.le_opNorm _
    _ ≤ ‖B.symm.toContinuousLinearMap‖*(Real.exp R*‖x‖) := by
      gcongr
      rw [logScale_symm]
      exact logScale_norm_le hR x
    _ = _ := by ring

lemma logScaledLattice_measurable_apply {α : Type*} [MeasurableSpace α]
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) (u : α → d → ℝ)
    (hu : ∀ i, Measurable (fun a => u a i)) (x : EuclideanSpace ℝ d) :
    Measurable (fun a => logScaledLattice B (u a) x) := by
  change Measurable (fun a => toLp 2 (fun i => Real.exp (u a i)*(B x) i))
  exact (PiLp.continuous_toLp 2 (fun _ : d => ℝ)).measurable.comp (Measurable.of_eval (fun i =>
    ((hu i).exp).mul_const _))

 

theorem logScaledLattice_averaged_mellin_differentiable
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) (u : α → d → ℝ)
    (hu : ∀ i, Measurable (fun a => u a i)) {R : ℝ}
    (hR : ∀ a i, -u a i ≤ R) :
    Differentiable ℂ (mellin (averagedNormalizedThetaTail μ (fun a => logScaledLattice B (u a)))) := by
  let C : ℝ := ‖B.symm.toContinuousLinearMap‖*Real.exp R
  have HC : 0 ≤ C := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have HB : ∀ a : α, ‖(logScaledLattice B (u a)).symm.toContinuousLinearMap‖ ≤ C := by
    intro a
    exact logScaledLattice_inverse_bound B (u := u a) (R := R) (hR a)
  have HM : StronglyMeasurable (fun p : α × ℝ =>
      normalizedThetaTail (logScaledLattice B (u p.1)) p.2) := by
    exact normalizedThetaTail_joint_stronglyMeasurable
      (B := fun a => logScaledLattice B (u a))
      (fun z => logScaledLattice_measurable_apply B u hu (euclideanInteger z))
  exact averagedNormalizedThetaTail_mellin_differentiable μ (fun a => logScaledLattice B (u a)) C HC HB HM

end PrimeDegreePackets.ThetaConstruction


namespace PrimeDegreePackets
open ThetaConstruction

 
def restoredLogCoordinates {d : ℕ} (u : LogCoordinates d) : Fin (d+1) → ℝ :=
  Fin.snoc u (-∑ i, u i)

lemma restoredLogCoordinates_exp {d : ℕ} (u : LogCoordinates d) (i : Fin (d+1)) :
    Real.exp (restoredLogCoordinates u i) = logFlowWeights u i := by
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [restoredLogCoordinates,logFlowWeights]

lemma restoredLogCoordinates_continuous {d : ℕ} (i : Fin (d+1)) :
    Continuous (fun u : LogCoordinates d => restoredLogCoordinates u i) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [restoredLogCoordinates,Fin.snoc_last]
    fun_prop
  · simp only [restoredLogCoordinates,Fin.snoc_castSucc]
    exact continuous_apply j

lemma restoredLogCoordinates_bound_on_compact {d : ℕ} {S : Set (LogCoordinates d)}
    (hS : IsCompact S) : ∃ R : ℝ, ∀ u ∈ S, ∀ i, -restoredLogCoordinates u i ≤ R := by
  let f : LogCoordinates d → ℝ := fun u => ∑ i, |u i|
  have hf : Continuous f := by unfold f; fun_prop
  obtain ⟨R,hR⟩ := hS.bddAbove_image hf.continuousOn
  refine ⟨R,fun u hu i => ?_⟩
  have H : f u ≤ R := hR (Set.mem_image_of_mem f hu)
  apply le_trans _ H
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [restoredLogCoordinates,Fin.snoc_last,neg_neg]
    exact Finset.sum_le_sum (fun j _ => le_abs_self (u j))
  · simp only [restoredLogCoordinates,Fin.snoc_castSucc]
    exact (neg_le_abs (u j)).trans (Finset.single_le_sum (fun i _ => abs_nonneg (u i))
      (Finset.mem_univ j))

 
def arithmeticFlowThetaTail {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (u : LogCoordinates d) : ℝ → ℂ :=
  normalizedThetaTail (logScaledLattice (fullLatticeEuclideanBasis M σ hn)
    (restoredLogCoordinates u))

lemma arithmeticFlowTheta_vector {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (u : LogCoordinates d)
    (z : Fin (d+1) → ℤ) (i : Fin (d+1)) :
    logScaledLattice (fullLatticeEuclideanBasis M σ hn) (restoredLogCoordinates u)
      (euclideanInteger z) i = logFlowWeights u i *
        σ i (M.basis.equivFun.symm z : K) := by
  change Real.exp (restoredLogCoordinates u i) *
    (fullLatticeEuclideanBasis M σ hn (euclideanInteger z)) i = _
  rw [restoredLogCoordinates_exp,fullLatticeEuclideanBasis_apply]

 

theorem arithmeticFlowThetaTail_boundedAverage_entire {d : ℕ} {K : Type*}
    [Field K] [NumberField K] (M : FullLattice (d+1) K)
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    {S : Set (LogCoordinates d)} (hS : MeasurableSet S) (hbd : Bornology.IsBounded S) :
    Differentiable ℂ (mellin (fun t => ∫ u in S, arithmeticFlowThetaTail M σ hn u t)) := by
  let μ : Measure S := Measure.comap ((↑) : S → LogCoordinates d) volume
  have hμ : IsFiniteMeasure μ := ⟨by
    dsimp only [μ]
    rw [comap_subtype_coe_apply hS,Set.image_univ,Subtype.range_coe]
    exact hbd.measure_lt_top⟩
  let u : S → Fin (d+1) → ℝ := fun a => restoredLogCoordinates a.1
  have hu : ∀ i, Measurable (fun a => u a i) := fun i =>
    ((restoredLogCoordinates_continuous i).comp continuous_subtype_val).measurable
  obtain ⟨R,hR⟩ := restoredLogCoordinates_bound_on_compact hbd.isCompact_closure
  have H := logScaledLattice_averaged_mellin_differentiable μ
    (fullLatticeEuclideanBasis M σ hn) u hu (R := R) (fun a i => hR a.1 (subset_closure a.2) i)
  have HE : averagedNormalizedThetaTail μ
      (fun a => logScaledLattice (fullLatticeEuclideanBasis M σ hn) (u a)) =
      fun t => ∫ u in S, arithmeticFlowThetaTail M σ hn u t := by
    funext t
    exact integral_subtype_comap hS (fun u => arithmeticFlowThetaTail M σ hn u t)
  rw [HE] at H
  exact H

 

def orderedThetaLogDomain {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K) : Set (LogCoordinates d) :=
  ZSpan.fundamentalDomain (Module.Basis.ofZLatticeBasis ℝ (orderedLogSubgroup σ ⊤)
    (Module.Free.chooseBasis ℤ (orderedLogSubgroup σ ⊤)))

theorem orderedThetaLogDomain_fundamental {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K) :
    IsAddFundamentalDomain (orderedLogSubgroup σ ⊤) (orderedThetaLogDomain σ) volume :=
  ZLattice.isAddFundamentalDomain (Module.Free.chooseBasis ℤ (orderedLogSubgroup σ ⊤)) volume

theorem arithmeticFlowThetaTail_unitAverage_entire {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K)
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1) :
    Differentiable ℂ (mellin (fun t => ∫ u in orderedThetaLogDomain σ,
      arithmeticFlowThetaTail M σ hn u t)) :=
  arithmeticFlowThetaTail_boundedAverage_entire M σ hn
    (ZSpan.fundamentalDomain_measurableSet _) (ZSpan.fundamentalDomain_isBounded _)

theorem orderedThetaLogDomain_volume {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K) :
    volume (orderedThetaLogDomain σ) = ENNReal.ofReal (NumberField.Units.regulator K) :=
  orderedLogFundamentalDomain_volume σ (orderedThetaLogDomain_fundamental σ)

end PrimeDegreePackets


namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

def exponentialTail (a : ℝ) : ℝ → ℂ :=
  (Set.Ioi 1).indicator (fun t => (Real.exp (-a*t) : ℂ))

lemma exponentialTail_mellinConvergent {a : ℝ} (ha : 0 < a) (s : ℂ) :
    MellinConvergent (exponentialTail a) s := by
  have HL : LocallyIntegrable (exponentialTail a) :=
    (show Continuous (fun t : ℝ => (Real.exp (-a*t):ℂ)) by fun_prop).locallyIntegrable.indicator
      measurableSet_Ioi
  have HE : exponentialTail a =O[atTop] (fun t => Real.exp (-a*t)) := by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_gt_atTop (1:ℝ)] with t ht
    simp [exponentialTail,ht,Complex.norm_exp]
  have HZ : exponentialTail a =O[𝓝[>] 0] (fun t : ℝ => t^(-(s.re-1))) := by
    apply IsBigO.of_bound 0
    have H : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds zero_lt_one)
    filter_upwards [H] with t ht
    simp [exponentialTail,not_lt.mpr ht.le]
  exact mellinConvergent_of_isBigO_rpow_exp ha (HL.locallyIntegrableOn (Set.Ioi 0)) HE HZ (by linarith)

lemma normalizedThetaTail_uniform_majorant (R : ℝ) (hR : 0 ≤ R) :
    ∃ a C : ℝ, 0 < a ∧ 0 ≤ C ∧
      ∀ (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d),
        ‖B.symm.toContinuousLinearMap‖ ≤ R → ∀ t : ℝ,
          ‖normalizedThetaTail B t‖ ≤ C * ‖exponentialTail a t‖ := by
  obtain ⟨a,C,ha,hC,hbound⟩ := thetaRemainder_uniform_exponential_bound (d := d) R hR
  refine ⟨a*Real.pi,C,mul_pos ha Real.pi_pos,hC,fun B hB t => ?_⟩
  by_cases ht : 1 < t
  · have H := hbound B hB (Real.pi*t) (by nlinarith [Real.pi_gt_three])
    simpa [normalizedThetaTail,exponentialTail,ht,max_eq_left ht.le,
      Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),mul_assoc,Complex.norm_exp] using H
  · simp [normalizedThetaTail,exponentialTail,ht]

 
theorem normalizedThetaTail_mellin_integrableProd
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (B : α → EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (R : ℝ) (hR : 0 ≤ R) (hbound : ∀ x, ‖(B x).symm.toContinuousLinearMap‖ ≤ R)
    (hB : StronglyMeasurable (fun p : α × ℝ => normalizedThetaTail (B p.1) p.2)) (s : ℂ) :
    Integrable (fun p : α × ℝ => (p.2:ℂ)^(s-1) * normalizedThetaTail (B p.1) p.2)
      (μ.prod (volume.restrict (Set.Ioi 0))) := by
  let ν : Measure ℝ := volume.restrict (Set.Ioi 0)
  obtain ⟨a,C,ha,_,hmajorant⟩ := normalizedThetaTail_uniform_majorant (d := d) R hR
  let F : α × ℝ → ℂ := fun p => (p.2:ℂ)^(s-1) * normalizedThetaTail (B p.1) p.2
  let g : ℝ → ℂ := fun t => (t:ℂ)^(s-1) * exponentialTail a t
  have hg : Integrable g ν := exponentialTail_mellinConvergent ha s
  have hF : AEStronglyMeasurable F (μ.prod ν) := by
    apply StronglyMeasurable.aestronglyMeasurable
    exact ((Complex.measurable_ofReal.comp measurable_snd).pow_const (s-1)).stronglyMeasurable.mul hB
  have HF : Integrable F (μ.prod ν) := by
    apply ((integrable_const C).mul_prod hg.norm).mono' hF
    apply Filter.Eventually.of_forall
    intro p
    change ‖(p.2:ℂ)^(s-1) * normalizedThetaTail (B p.1) p.2‖ ≤
      C * ‖(p.2:ℂ)^(s-1) * exponentialTail a p.2‖
    simp only [norm_mul]
    calc
      _ ≤ ‖(p.2:ℂ)^(s-1)‖*(C*‖exponentialTail a p.2‖) :=
        mul_le_mul_of_nonneg_left (hmajorant (B p.1) (hbound p.1) p.2) (norm_nonneg _)
      _ = _ := by ring
  exact HF

lemma normalizedThetaTail_mellin_integrable
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (B : α → EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (R : ℝ) (hR : 0 ≤ R) (hbound : ∀ x, ‖(B x).symm.toContinuousLinearMap‖ ≤ R)
    (hB : StronglyMeasurable (fun p : α × ℝ => normalizedThetaTail (B p.1) p.2)) (s : ℂ) :
    Integrable (fun x => mellin (normalizedThetaTail (B x)) s) μ := by
  simpa only [mellin,smul_eq_mul] using
    (normalizedThetaTail_mellin_integrableProd μ B R hR hbound hB s).integral_prod_left

 

theorem averagedNormalizedThetaTail_mellin_eq_integral
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (B : α → EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (R : ℝ) (hR : 0 ≤ R) (hbound : ∀ x, ‖(B x).symm.toContinuousLinearMap‖ ≤ R)
    (hB : StronglyMeasurable (fun p : α × ℝ => normalizedThetaTail (B p.1) p.2)) (s : ℂ) :
    mellin (averagedNormalizedThetaTail μ B) s =
      ∫ x, mellin (normalizedThetaTail (B x)) s ∂μ := by
  let ν : Measure ℝ := volume.restrict (Set.Ioi 0)
  have HF := normalizedThetaTail_mellin_integrableProd μ B R hR hbound hB s
  calc
    mellin (averagedNormalizedThetaTail μ B) s =
        ∫ t, ∫ x, (t:ℂ)^(s-1) * normalizedThetaTail (B x) t ∂μ ∂ν := by
      unfold mellin averagedNormalizedThetaTail
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun t => (integral_const_mul _ _).symm)
    _ = ∫ x, ∫ t, (t:ℂ)^(s-1) * normalizedThetaTail (B x) t ∂ν ∂μ :=
      (integral_integral_swap HF).symm
    _ = _ := rfl

end PrimeDegreePackets.ThetaConstruction
end
end

end OAI
