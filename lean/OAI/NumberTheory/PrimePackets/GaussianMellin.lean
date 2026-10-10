import Mathlib
import OAI.NumberTheory.PrimePackets.IntegerEmbeddings

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
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
open scoped Matrix Topology Classical ENNReal
open scoped Topology ENNReal
open scoped Matrix Topology ENNReal ProbabilityTheory
open scoped Topology ENNReal CompactlySupported
open MeasureTheory Set Filter TopologicalSpace
open Module Set Matrix MeasureTheory Filter
open scoped NumberField
open CategoryTheory Module
open MeasureTheory Module Set Filter
open scoped BigOperators ENNReal RealInnerProductSpace
open Module Matrix
open scoped NumberField BigOperators
open Module MeasureTheory Set WithLp
open scoped NumberField BigOperators ENNReal
open IntermediateField Module
open Module IntermediateField
open scoped BigOperators NumberField Pointwise
open Module IntermediateField Set
open MeasureTheory Set Module Filter
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology ComplexConjugate
open Module
open MeasureTheory Module
open scoped BigOperators Matrix NumberField nonZeroDivisors
open scoped BigOperators NumberField nonZeroDivisors
namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]
local instance averagedPeriodicThetaDecidableEq : DecidableEq d := Classical.decEq d

lemma hasMellin_of_add_inversion {F P Q : ℝ → ℂ} (a c s : ℂ)
    (hP : MellinConvergent P s) (hQ : MellinConvergent Q (a-s))
    (hF : F =ᵐ[volume.restrict (Ioi 0)] (fun t => P t+c*(t:ℂ)^(-a)*Q t⁻¹)) :
    HasMellin F s (mellin P s+c*mellin Q (a-s)) := by
  let q := fun t : ℝ => c • ((t:ℂ)^(-a) • Q t⁻¹)
  have hQi : MellinConvergent (fun t => (t:ℂ)^(-a) • Q t⁻¹) s := by
    apply MellinConvergent.cpow_smul.mpr
    apply mellinConvergent_inv.mpr
    convert hQ using 1
    ring
  have hq : MellinConvergent q s := hQi.const_smul c
  have HF := hasMellin_add hP hq
  have hqeq : mellin q s = c*mellin Q (a-s) := by
    calc
      mellin q s = c • mellin (fun t => (t:ℂ)^(-a) • Q t⁻¹) s := mellin_const_smul _ s c
      _ = _ := by
        rw [mellin_cpow_smul,mellin_comp_inv,smul_eq_mul]
        congr 2
        ring
  have HE : F =ᵐ[volume.restrict (Ioi 0)] (fun t => P t+q t) := by
    simpa only [q,smul_eq_mul,mul_assoc] using hF
  have HI : (fun t : ℝ => (t:ℂ)^(s-1) • F t) =ᵐ[volume.restrict (Ioi 0)]
      (fun t : ℝ => (t:ℂ)^(s-1) • (P t+q t)) := by
    filter_upwards [HE] with t ht
    rw [ht]
  refine ⟨HF.1.congr HI.symm, ?_⟩
  exact (integral_congr_ae HI).trans (HF.2.trans (by rw [hqeq]))

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (B : α → EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)

def averagedNormalizedPeriodicTheta (N : ℕ) [NeZero N]
    (w : (d → Fin N) → ℂ) (t : ℝ) : ℂ := ∫ x, normalizedPeriodicTheta (B x) N w t ∂μ

 

theorem averagedNormalizedPeriodicTheta_mellin_entire (N : ℕ) [NeZero N]
    (w : (d → Fin N) → ℂ)
    (hzero : periodicPrimalWeight N w 0 = 0) (hsum : ∑ i, w i = 0)
    (R T : ℝ) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hB : ∀ x, ‖(B x).symm.toContinuousLinearMap‖ ≤ R)
    (hD : ∀ x, ‖(adjointEquiv (B x).symm).symm.toContinuousLinearMap‖ ≤ T)
    (hBm : ∀ z : d → ℤ, Measurable (fun x => B x (euclideanInteger z)))
    (hDm : ∀ z : d → ℤ, Measurable (fun x => adjointEquiv (B x).symm (euclideanInteger z)))
    (c : ℂ) (hc : ∀ x, ((|(LinearMap.det (B x).toLinearMap)⁻¹|:ℝ):ℂ) = c) :
    Differentiable ℂ (mellin (averagedNormalizedPeriodicTheta μ B N w)) := by
  let k : ℝ := Real.pi/(N:ℝ)^2
  have hk : 0 < k := div_pos Real.pi_pos
    (sq_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))))
  let D := fun x => adjointEquiv (B x).symm
  let P := averagedWeightedThetaTail μ B (periodicPrimalWeight N w) k
  let Q := averagedWeightedThetaTail μ D (periodicDualWeight N w) Real.pi
  let a : ℂ := (Fintype.card d:ℂ)/2
  have hwp : ∀ z, ‖periodicPrimalWeight N w z‖ ≤ ∑ i, ‖w i‖ :=
    fun z => congruenceWeight_bound N w ((integerCongruenceEquiv N z).1)
  have hwq : ∀ z, ‖periodicDualWeight N w z‖ ≤ ∑ i, ‖w i‖ :=
    congruenceThetaFourierWeight_bound (congruencePoint N) w
  have hPe : Differentiable ℂ (mellin P) :=
    averagedWeightedThetaTail_mellin_entire μ B _ k hk _ hwp R hR hB hBm
  have hQe : Differentiable ℂ (mellin Q) :=
    averagedWeightedThetaTail_mellin_entire μ D _ Real.pi Real.pi_pos _ hwq T hT hD hDm
  have hPc (s : ℂ) : MellinConvergent P s :=
    averagedWeightedThetaTail_mellin_convergent μ B _ k hk _ hwp R hR hB hBm s
  have hQc (s : ℂ) : MellinConvergent Q s :=
    averagedWeightedThetaTail_mellin_convergent μ D _ Real.pi Real.pi_pos _ hwq T hT hD hDm s
  have hPI (t : ℝ) : Integrable (fun x => periodicPrimalTail (B x) N w t) μ :=
    scaledWeightedThetaTail_integrable_average μ B _ k hk _ hwp R hR hB hBm t
  have hQI (t : ℝ) : Integrable (fun x => periodicDualTail (B x) N w t) μ :=
    scaledWeightedThetaTail_integrable_average μ D _ Real.pi Real.pi_pos _ hwq T hT hD hDm t
  have H (t : ℝ) (ht : 0 < t) (hne : t ≠ 1) :
      averagedNormalizedPeriodicTheta μ B N w t = P t+c*(t:ℂ)^(-a)*Q t⁻¹ := by
    unfold averagedNormalizedPeriodicTheta
    simp_rw [normalizedPeriodicTheta_decomposition _ N w hzero hsum ht hne, hc]
    rw [integral_add (hPI t) ((hQI t⁻¹).const_mul _), integral_const_mul]
    rfl
  have Hne : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioi 0)), t ≠ 1 := by
    apply ae_restrict_of_ae
    rw [ae_iff]
    simp
  have HE : averagedNormalizedPeriodicTheta μ B N w =ᵐ[volume.restrict (Ioi 0)]
      (fun t => P t+c*(t:ℂ)^(-a)*Q t⁻¹) := by
    filter_upwards [Hne,ae_restrict_mem measurableSet_Ioi] with t hne ht
    exact H t ht hne
  have HM : mellin (averagedNormalizedPeriodicTheta μ B N w) =
      (fun s => mellin P s+c*mellin Q (a-s)) := by
    funext s
    exact (hasMellin_of_add_inversion a c s (hPc s) (hQc (a-s)) HE).2
  rw [HM]
  exact hPe.add ((hQe.comp ((differentiable_const a).sub differentiable_id)).const_mul c)

end PrimeDegreePackets.ThetaConstruction


namespace PrimeDegreePackets
open ThetaConstruction
variable {d : ℕ} {K : Type*} [Field K] [NumberField K]

 
def complexFlowGaussian (σ : OrderedEmbeddings (d+1) K) (a : K)
    (t : ℝ) (u : LogCoordinates d) : ℂ :=
  Complex.exp (-((Real.pi*t : ℝ) : ℂ) *
    ((∑ i, (logFlowWeights u i * σ i a)^2 : ℝ) : ℂ))

lemma complexFlowGaussian_unit_translate [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (a : K) (z : (𝓞 K)ˣ)
    (t : ℝ) (u : LogCoordinates d) :
    complexFlowGaussian σ ((z : K)*a) t u =
      complexFlowGaussian σ a t (orderedUnitLog σ (Additive.ofMul z)+u) := by
  unfold complexFlowGaussian
  simp only [map_mul,logFlowWeights_add,logFlowWeights_orderedUnitLog]
  congr 3
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.mul_apply,mul_pow,sq_abs]
  ring

def residueCharacterFlowTheta (σ : OrderedEmbeddings (d+1) K) (N : ℕ)
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ)
    (u : LogCoordinates d) (t : ℝ) : ℂ :=
  ∑' a : 𝓞 K, χ (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) a) *
    complexFlowGaussian σ (a : K) t u

lemma residueCharacterFlowTheta_eq (b : Basis (Fin (d+1)) ℤ (𝓞 K))
    (σ : OrderedEmbeddings (d+1) K) (N : ℕ)
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ)
    (u : LogCoordinates d) :
    residueCharacterFlowTheta σ N χ u = integralOrderTheta
      (logScaledLattice (integerEuclideanBasis b σ) (restoredLogCoordinates u)) b N χ := by
  funext t
  unfold residueCharacterFlowTheta integralOrderTheta
  apply tsum_congr
  intro a
  congr 1
  unfold complexFlowGaussian
  congr 2
  rw [← Complex.ofReal_pow, EuclideanSpace.real_norm_sq_eq]
  simp only [logScaledLattice, ContinuousLinearEquiv.trans_apply,
    integerEuclideanBasis_apply, LinearEquiv.symm_apply_apply,
    logScale_apply, restoredLogCoordinates_exp]

lemma residueCharacterFlowTheta_unit_covariance [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (N : ℕ)
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ)
    (z : (𝓞 K)ˣ) (u : LogCoordinates d) (t : ℝ) :
    residueCharacterFlowTheta σ N χ u t =
      χ (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) (z : 𝓞 K)) *
      residueCharacterFlowTheta σ N χ (orderedUnitLog σ (Additive.ofMul z)+u) t := by
  unfold residueCharacterFlowTheta
  rw [← (Units.mulLeft z).tsum_eq]
  simp only [Units.mulLeft_apply, map_mul,
    complexFlowGaussian_unit_translate, mul_assoc]
  exact tsum_mul_left

lemma residueCharacterFlowTheta_congruence_periodic [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (N : ℕ)
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ)
    (z : (𝓞 K)ˣ) (hz : z ∈ rationalCongruenceUnits (𝓞 K) N)
    (u : LogCoordinates d) (t : ℝ) :
    residueCharacterFlowTheta σ N χ (orderedUnitLog σ (Additive.ofMul z)+u) t =
      residueCharacterFlowTheta σ N χ u t := by
  have H := residueCharacterFlowTheta_unit_covariance σ N χ z u t
  rw [(mem_rationalCongruenceUnits N z).mp hz, map_one, one_mul] at H
  exact H.symm

 

lemma residueCharacterFlowTheta_eq_zero_of_odd [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (N : ℕ)
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ)
    (hodd : χ (-1) = -1) (u : LogCoordinates d) (t : ℝ) :
    residueCharacterFlowTheta σ N χ u t = 0 := by
  have hneg : orderedUnitLog σ (Additive.ofMul (-1 : (𝓞 K)ˣ)) = 0 := by
    change Additive.ofMul (-1 : (𝓞 K)ˣ) ∈ (orderedUnitLog σ).ker
    rw [orderedUnitLog_ker]
    exact neg_one_mem_torsion
  have H := residueCharacterFlowTheta_unit_covariance σ N χ (-1) u t
  simp only [hneg, zero_add, Units.val_neg, Units.val_one, map_neg, map_one,
    hodd, neg_one_mul] at H
  exact CharZero.eq_neg_self_iff.mp H

 

theorem residueCharacterFlowTheta_mellin_entire (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (N : ℕ) [NeZero N]
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ) (hχ : χ ≠ 1)
    (u : LogCoordinates d) :
    Differentiable ℂ (mellin (residueCharacterFlowTheta σ N χ u)) := by
  rw [residueCharacterFlowTheta_eq (orderedIntegerBasis hn)]
  exact integralOrderTheta_mellin_entire _ _ N χ hχ

end PrimeDegreePackets


namespace PrimeDegreePackets
open ThetaConstruction

lemma periodicLogTheta_boundedAverage_entire {d : ℕ}
    (B : EuclideanSpace ℝ (Fin (d+1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (d+1)))
    (N : ℕ) [NeZero N] (w : (Fin (d+1) → Fin N) → ℂ)
    (hzero : periodicPrimalWeight N w 0 = 0) (hsum : ∑ i, w i = 0)
    {S : Set (LogCoordinates d)} (hS : MeasurableSet S) (hbd : Bornology.IsBounded S) :
    Differentiable ℂ (mellin (fun t => ∫ u in S,
      normalizedPeriodicTheta (logScaledLattice B (restoredLogCoordinates u)) N w t)) := by
  let μ : Measure S := Measure.comap ((↑) : S → LogCoordinates d) volume
  have hμ : IsFiniteMeasure μ := ⟨by
    dsimp only [μ]
    rw [comap_subtype_coe_apply hS,Set.image_univ,Subtype.range_coe]
    exact hbd.measure_lt_top⟩
  let u : S → Fin (d+1) → ℝ := fun x => restoredLogCoordinates x.1
  let F := fun x : S => logScaledLattice B (u x)
  have hu : ∀ i, Measurable (fun x => u x i) := fun i =>
    ((restoredLogCoordinates_continuous i).comp continuous_subtype_val).measurable
  obtain ⟨U,hU⟩ := restoredLogCoordinates_abs_bound_on_compact hbd.isCompact_closure
  let R := ‖B.symm.toContinuousLinearMap‖*Real.exp U
  let T := ‖(adjointEquiv B.symm).symm.toContinuousLinearMap‖*Real.exp U
  have hR : 0 ≤ R := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hT : 0 ≤ T := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have HB : ∀ x, ‖(F x).symm.toContinuousLinearMap‖ ≤ R := by
    intro x
    exact logScaledLattice_inverse_bound B (fun i =>
      (neg_le_abs _).trans (hU x.1 (subset_closure x.2) i))
  have HD : ∀ x, ‖(adjointEquiv (F x).symm).symm.toContinuousLinearMap‖ ≤ T := by
    intro x
    rw [show F x = logScaledLattice B (u x) from rfl,adjointEquiv_logScaledLattice]
    apply logScaledLattice_inverse_bound
    intro i
    simp only [Pi.neg_apply,neg_neg]
    exact (le_abs_self _).trans (hU x.1 (subset_closure x.2) i)
  have HM : ∀ z, Measurable (fun x => F x (euclideanInteger z)) :=
    fun z => logScaledLattice_measurable_apply B u hu (euclideanInteger z)
  have HN : ∀ z, Measurable (fun x => adjointEquiv (F x).symm (euclideanInteger z)) := by
    intro z
    simp_rw [show ∀ x, adjointEquiv (F x).symm =
      logScaledLattice (adjointEquiv B.symm) (-u x) from fun x => adjointEquiv_logScaledLattice B (u x)]
    exact logScaledLattice_measurable_apply _ _ (fun i => (hu i).neg) (euclideanInteger z)
  have HC : ∀ x, ((|(LinearMap.det (F x).toLinearMap)⁻¹|:ℝ):ℂ) =
      ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) := by
    intro x
    dsimp only [F,u]
    rw [logScaledLattice_det,restoredLogCoordinates_sum,Real.exp_zero,one_mul]
  have H := averagedNormalizedPeriodicTheta_mellin_entire μ F N w hzero (by
      convert hsum using 1
      apply Finset.sum_congr
      · ext r; simp
      · intro r _; rfl)
    R T hR hT HB HD HM HN _ HC
  have HE : averagedNormalizedPeriodicTheta μ F N w =
      (fun t => ∫ u in S, normalizedPeriodicTheta (logScaledLattice B (restoredLogCoordinates u)) N w t) := by
    funext t
    exact integral_subtype_comap hS
      (fun u => normalizedPeriodicTheta (logScaledLattice B (restoredLogCoordinates u)) N w t)
  rw [HE] at H
  exact H

lemma modulusScaledBasis_logScaledLattice {d : Type*} [Fintype d]
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) (N : ℕ) [NeZero N] (u : d → ℝ) :
    modulusScaledBasis (logScaledLattice B u) N = logScaledLattice (modulusScaledBasis B N) u := by
  ext x
  rfl

 

theorem residueCharacterFlowTheta_boundedAverage_entire {d : ℕ} {K : Type*}
    [Field K] [NumberField K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (N : ℕ) [NeZero N]
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ) (hχ : χ ≠ 1)
    {S : Set (LogCoordinates d)} (hS : MeasurableSet S) (hbd : Bornology.IsBounded S) :
    Differentiable ℂ (mellin (fun t => ∫ u in S, residueCharacterFlowTheta σ N χ u t)) := by
  let b := orderedIntegerBasis hn
  have HE : (fun t => ∫ u in S, residueCharacterFlowTheta σ N χ u t) =
      (fun t => ∫ u in S, normalizedPeriodicTheta
        (logScaledLattice (modulusScaledBasis (integerEuclideanBasis b σ) N)
          (restoredLogCoordinates u)) N (integralCharacterWeight b N χ) t) := by
    funext t
    apply integral_congr_ae
    filter_upwards [] with u
    rw [residueCharacterFlowTheta_eq b,integralOrderTheta_eq_periodic,
      modulusScaledBasis_logScaledLattice]
  rw [HE]
  exact periodicLogTheta_boundedAverage_entire _ N _
    (integralCharacterWeight_zero b N χ hχ) (by
      convert integralCharacterWeight_sum_zero b N χ hχ using 1
      apply Finset.sum_congr
      · ext r; simp
      · intro r _; rfl) hS hbd

end PrimeDegreePackets

open MeasureTheory Module WithLp Set
namespace PrimeDegreePackets.ThetaConstruction
variable {d R : Type*} [Fintype d] [CommRing R]
local instance gaussianMellinDecidableEq : DecidableEq d := Classical.decEq d

lemma moduleResidueEquiv_coordinates {M : Type*} [AddCommGroup M]
    (b : Basis d ℤ M) (N : ℕ) [NeZero N] (z : d → ℤ) :
    moduleResidueEquiv b N (integerCongruenceEquiv N z).1 =
      ModN.mkQ N (b.equivFun.symm z) := by
  have hz : (Equiv.piCongrRight fun _ : d => (ZMod.finEquiv N).toEquiv)
      (integerCongruenceEquiv N z).1 = fun i => (z i : ZMod N) := by
    funext i
    exact finEquiv_divMod N (z i)
  simp only [moduleResidueEquiv,Equiv.trans_apply,hz,LinearEquiv.coe_toEquiv,
    Basis.equivFun_symm_apply,_root_.map_sum,map_zsmul,ModN.basis_apply_eq_mkQ,
    Int.cast_smul_eq_zsmul]

lemma idealCharacterWeight_coordinates (I : Ideal R) (bI : Basis d ℤ I)
    (N : ℕ) [NeZero N] (χ : MulChar (R ⧸ rationalModulusIdeal R N) ℂ) (z : d → ℤ) :
    periodicPrimalWeight N (idealCharacterWeight I bI N χ) z =
      χ (Ideal.Quotient.mk (rationalModulusIdeal R N) (bI.equivFun.symm z : R)) := by
  simp only [periodicPrimalWeight,idealCharacterWeight,moduleResidueEquiv_coordinates,
    idealModNReduction_mk]

 
def idealCharacterTheta (I : Ideal R) (bI : Basis d ℤ I)
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) (N : ℕ)
    (χ : MulChar (R ⧸ rationalModulusIdeal R N) ℂ) (t : ℝ) : ℂ :=
  ∑' a : I, χ (Ideal.Quotient.mk (rationalModulusIdeal R N) (a:R)) *
    Complex.exp (-((Real.pi*t : ℝ):ℂ)*‖B (euclideanInteger (bI.equivFun a))‖^2)

lemma idealCharacterTheta_eq_periodic (I : Ideal R) (bI : Basis d ℤ I)
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) (N : ℕ) [NeZero N]
    (χ : MulChar (R ⧸ rationalModulusIdeal R N) ℂ) (t : ℝ) :
    idealCharacterTheta I bI B N χ t =
      normalizedPeriodicTheta (modulusScaledBasis B N) N (idealCharacterWeight I bI N χ) t := by
  unfold idealCharacterTheta normalizedPeriodicTheta periodicLatticeTheta
  rw [← bI.equivFun.symm.toEquiv.tsum_eq]
  apply tsum_congr
  intro z
  simp only [LinearEquiv.coe_toEquiv,LinearEquiv.apply_symm_apply,modulusScaledBasis_cancel]
  rw [← idealCharacterWeight_coordinates I bI N χ z]
  rfl

lemma idealCharacterTheta_mellin_entire (I : Ideal R) (bI : Basis d ℤ I) (bR : Basis d ℤ R)
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) (N : ℕ) [NeZero N]
    (hI : IsCoprime I (rationalModulusIdeal R N))
    (χ : MulChar (R ⧸ rationalModulusIdeal R N) ℂ) (hχ : χ ≠ 1) :
    Differentiable ℂ (mellin (idealCharacterTheta I bI B N χ)) := by
  have H : idealCharacterTheta I bI B N χ =
      normalizedPeriodicTheta (modulusScaledBasis B N) N (idealCharacterWeight I bI N χ) :=
    funext (idealCharacterTheta_eq_periodic I bI B N χ)
  rw [H]
  exact normalizedPeriodicTheta_mellin_entire _ N _
    (idealCharacterWeight_zero I bI N χ hχ) (idealCharacterWeight_sum_zero I bI bR N hI χ hχ)

end PrimeDegreePackets.ThetaConstruction


namespace PrimeDegreePackets
open ThetaConstruction

 

theorem idealCharacterTheta_boundedAverage_entire {d : ℕ} {R : Type*} [CommRing R]
    (I : Ideal R) (bI : Basis (Fin (d+1)) ℤ I) (bR : Basis (Fin (d+1)) ℤ R)
    (B : EuclideanSpace ℝ (Fin (d+1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (d+1)))
    (N : ℕ) [NeZero N] (hI : IsCoprime I (rationalModulusIdeal R N))
    (χ : MulChar (R ⧸ rationalModulusIdeal R N) ℂ) (hχ : χ ≠ 1)
    {S : Set (LogCoordinates d)} (hS : MeasurableSet S) (hbd : Bornology.IsBounded S) :
    Differentiable ℂ (mellin (fun t => ∫ u in S,
      idealCharacterTheta I bI (logScaledLattice B (restoredLogCoordinates u)) N χ t)) := by
  have H : (fun t => ∫ u in S,
      idealCharacterTheta I bI (logScaledLattice B (restoredLogCoordinates u)) N χ t) =
      (fun t => ∫ u in S, normalizedPeriodicTheta
        (logScaledLattice (modulusScaledBasis B N) (restoredLogCoordinates u))
          N (idealCharacterWeight I bI N χ) t) := by
    funext t
    apply integral_congr_ae
    filter_upwards [] with u
    rw [idealCharacterTheta_eq_periodic,modulusScaledBasis_logScaledLattice]
  rw [H]
  exact periodicLogTheta_boundedAverage_entire _ N _
    (idealCharacterWeight_zero I bI N χ hχ) (by
      convert idealCharacterWeight_sum_zero I bI bR N hI χ hχ using 1
      apply Finset.sum_congr
      · ext r; simp
      · intro r _; rfl) hS hbd

end PrimeDegreePackets


namespace PrimeDegreePackets
open ThetaConstruction
variable {n : ℕ} {K : Type*} [Field K] [NumberField K]

def integralIdealFractionalUnit (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 (I : FractionalIdeal (𝓞 K)⁰ K) (FractionalIdeal.coeIdeal_ne_zero.mpr hI)

def integralIdealFullEquiv (hn : finrank ℚ K = n) (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    I ≃ₗ[ℤ] (fractionalIdealFullLattice hn (integralIdealFractionalUnit I hI)).carrier := by
  let f : I →ₗ[ℤ] (fractionalIdealFullLattice hn (integralIdealFractionalUnit I hI)).carrier :=
    { toFun := fun a => ⟨((a:𝓞 K):K), FractionalIdeal.mem_coeIdeal_of_mem (𝓞 K)⁰ a.2⟩
      map_add' := by intros; apply Subtype.ext; simp
      map_smul' := by intros; apply Subtype.ext; simp }
  apply LinearEquiv.ofBijective f
  constructor
  · intro a b hab
    apply Subtype.ext
    apply NumberField.RingOfIntegers.coe_injective
    exact congrArg (fun x : (fractionalIdealFullLattice hn (integralIdealFractionalUnit I hI)).carrier =>
      (x:K)) hab
  · intro a
    obtain ⟨b,hb,he⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp a.2
    refine ⟨⟨b,hb⟩,Subtype.ext ?_⟩
    exact he

lemma integralIdealFullEquiv_coe (hn : finrank ℚ K = n) (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (a : I) : (integralIdealFullEquiv hn I hI a : K) = ((a:𝓞 K):K) := rfl

def orderedIdealBasis (hn : finrank ℚ K = n) (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    Basis (Fin n) ℤ I :=
  (fractionalIdealFullLattice hn (integralIdealFractionalUnit I hI)).basis.map
    (integralIdealFullEquiv hn I hI).symm

lemma orderedIdealBasis_coordinates (hn : finrank ℚ K = n) (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (a : I) :
    ((fractionalIdealFullLattice hn (integralIdealFractionalUnit I hI)).basis.equivFun.symm
      ((orderedIdealBasis hn I hI).equivFun a) : K) = ((a:𝓞 K):K) := by
  change ((fractionalIdealFullLattice hn (integralIdealFractionalUnit I hI)).basis.equivFun.symm
    ((orderedIdealBasis hn I hI).equivFun a) : K) =
      (integralIdealFullEquiv hn I hI a : K)
  congr 1
  apply (fractionalIdealFullLattice hn (integralIdealFractionalUnit I hI)).basis.equivFun.injective
  simp [orderedIdealBasis]

 

def idealResidueFlowTheta {d : ℕ} (σ : OrderedEmbeddings (d+1) K)
    (I : Ideal (𝓞 K)) (N : ℕ)
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ)
    (u : LogCoordinates d) (t : ℝ) : ℂ :=
  ∑' a : I, χ (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) (a:𝓞 K)) *
    Complex.exp (-((Real.pi*t : ℝ):ℂ) *
      ‖toLp 2 (fun j => logFlowWeights u j * σ j ((a:𝓞 K):K))‖^2)

lemma idealResidueFlowTheta_eq {d : ℕ} (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (N : ℕ)
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ)
    (u : LogCoordinates d) (t : ℝ) :
    idealResidueFlowTheta σ I N χ u t = idealCharacterTheta I (orderedIdealBasis hn I hI)
      (logScaledLattice
        (fullLatticeEuclideanBasis (fractionalIdealFullLattice hn (integralIdealFractionalUnit I hI)) σ hn)
          (restoredLogCoordinates u)) N χ t := by
  unfold idealResidueFlowTheta idealCharacterTheta
  apply tsum_congr
  intro a
  have HV : logScaledLattice
      (fullLatticeEuclideanBasis (fractionalIdealFullLattice hn (integralIdealFractionalUnit I hI)) σ hn)
        (restoredLogCoordinates u) (euclideanInteger ((orderedIdealBasis hn I hI).equivFun a)) =
        toLp 2 (fun j => logFlowWeights u j * σ j ((a:𝓞 K):K)) := by
    ext j
    rw [arithmeticFlowTheta_vector,orderedIdealBasis_coordinates]
  rw [HV]

 

theorem idealResidueFlowTheta_boundedAverage_entire {d : ℕ}
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (N : ℕ) [NeZero N]
    (hcop : IsCoprime I (rationalModulusIdeal (𝓞 K) N))
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ) (hχ : χ ≠ 1)
    {S : Set (LogCoordinates d)} (hS : MeasurableSet S) (hbd : Bornology.IsBounded S) :
    Differentiable ℂ (mellin (fun t => ∫ u in S, idealResidueFlowTheta σ I N χ u t)) := by
  have H : (fun t => ∫ u in S, idealResidueFlowTheta σ I N χ u t) =
      (fun t => ∫ u in S, idealCharacterTheta I (orderedIdealBasis hn I hI)
        (logScaledLattice (fullLatticeEuclideanBasis
          (fractionalIdealFullLattice hn (integralIdealFractionalUnit I hI)) σ hn)
            (restoredLogCoordinates u)) N χ t) := by
    funext t
    apply integral_congr_ae
    filter_upwards [] with u
    exact idealResidueFlowTheta_eq σ hn I hI N χ u t
  rw [H]
  exact idealCharacterTheta_boundedAverage_entire I (orderedIdealBasis hn I hI)
    (orderedIntegerBasis hn) _ N hcop χ hχ hS hbd

end PrimeDegreePackets
end
end

end OAI
