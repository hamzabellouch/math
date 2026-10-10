import Mathlib
import OAI.NumberTheory.PrimePackets.XiBoundary

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
namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

omit [Fintype d] in
lemma integerVector_closedEmbedding : IsClosedEmbedding (integerVector (d := d)) := by
  exact IsClosedEmbedding.piMap (fun _ => Int.isClosedEmbedding_coe_real)

lemma integerVector_tendsto : Tendsto (integerVector (d := d)) cofinite (cocompact _) := by
  simpa only [cocompact_eq_cofinite] using (integerVector_closedEmbedding (d := d)).tendsto_cocompact

def coordinateLattice : Submodule ℤ (d → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ d))

instance coordinateLattice_discrete : DiscreteTopology (coordinateLattice (d := d)) :=
  ZSpan.discreteTopology_pi_basisFun

instance coordinateLattice_full : IsZLattice ℝ (coordinateLattice (d := d)) :=
  ⟨ZSpan.span_top (Pi.basisFun ℝ d)⟩

lemma integerVector_mem (z : d → ℤ) : integerVector z ∈ coordinateLattice := by
  apply ((Pi.basisFun ℝ d).mem_span_iff_repr_mem ℤ _).mpr
  intro i
  exact ⟨z i, by simp [integerVector]⟩

def integerVectorInLattice (z : d → ℤ) : coordinateLattice (d := d) :=
  ⟨integerVector z,integerVector_mem z⟩

lemma integerVectorInLattice_injective : Function.Injective (integerVectorInLattice (d := d)) := by
  intro z w h
  have hv := congrArg Subtype.val h
  ext i
  exact Int.cast_injective (congrFun hv i)

lemma coordinateLattice_rank : Module.finrank ℤ (coordinateLattice (d := d)) = Fintype.card d := by
  rw [ZLattice.rank ℝ (coordinateLattice (d := d))]
  simp

lemma summable_integerVector_rpow {r : ℝ} (hr : r < -(Fintype.card d : ℝ)) :
    Summable (fun z : d → ℤ => ‖integerVector z‖ ^ r) := by
  have hr' : r < -(Module.finrank ℤ (coordinateLattice (d := d)) : ℝ) := by
    simpa only [coordinateLattice_rank] using hr
  have H := ZLattice.summable_norm_rpow (coordinateLattice (d := d)) r hr'
  exact H.comp_injective (i := integerVectorInLattice (d := d))
    (integerVectorInLattice_injective (d := d))

lemma schwartz_locallyNormal (f : 𝓢(d → ℝ,ℂ)) : LocallyNormal f.toContinuousMap := by
  intro K
  obtain ⟨R,hR⟩ := K.isCompact.isBounded.subset_closedBall 0
  let p := Fintype.card d + 1
  obtain ⟨C,hC,hdecay⟩ := f.decay p 0
  simp only [norm_iteratedFDeriv_zero] at hdecay
  have hsum : Summable (fun z : d → ℤ => C * 2^p * ‖integerVector z‖ ^ (-(p:ℝ))) :=
    (summable_integerVector_rpow (by dsimp [p]; push_cast; linarith)).mul_left _
  apply Summable.of_norm_bounded_eventually hsum
  have hz : ∀ᶠ z : d → ℤ in cofinite, 2*|R|+1 < ‖integerVector z‖ := by
    exact ((tendsto_norm_cocompact_atTop (E := d → ℝ)).comp
      (integerVector_tendsto (d := d))).eventually (eventually_gt_atTop (2*|R|+1))
  filter_upwards [hz] with z hz
  rw [norm_norm]
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  rintro ⟨x,hx⟩
  change ‖f (x + integerVector z)‖ ≤ C * 2^p * ‖integerVector z‖ ^ (-(p:ℝ))
  have hxR : ‖x‖ ≤ R := by simpa using hR hx
  have hzpos : 0 < ‖integerVector z‖ := by linarith [abs_nonneg R]
  have htri := norm_sub_le (x + integerVector z) x
  have hzle : ‖integerVector z‖/2 ≤ ‖x + integerVector z‖ := by
    simp only [add_sub_cancel_left] at htri
    linarith [le_abs_self R]
  have hwpos : 0 < ‖x + integerVector z‖ := lt_of_lt_of_le (by positivity) hzle
  have hbound : (‖integerVector z‖/2)^p * ‖f (x+integerVector z)‖ ≤ C :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hzle _) (norm_nonneg _)).trans
      (hdecay _)
  rw [Real.rpow_neg (norm_nonneg _),Real.rpow_natCast]
  apply (le_mul_inv_iff₀ (pow_pos hzpos p)).mpr
  rw [div_pow] at hbound
  have H := (div_le_iff₀ (by positivity : 0 < (2:ℝ)^p)).mp
    (show ‖f (x+integerVector z)‖ * ‖integerVector z‖^p / 2^p ≤ C by
      simpa only [div_mul_eq_mul_div,mul_comm] using hbound)
  exact H

end PrimeDegreePackets.ThetaConstruction

open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

 

lemma locallyNormal_of_polynomial_decay (f : C(d → ℝ,ℂ)) (p : ℕ)
    (hp : Fintype.card d < p) (C : ℝ) (hC : 0 < C)
    (hdecay : ∀ x, ‖x‖^p * ‖f x‖ ≤ C) : LocallyNormal f := by
  intro K
  obtain ⟨R,hR⟩ := K.isCompact.isBounded.subset_closedBall 0
  have hsum : Summable (fun z : d → ℤ => C * 2^p * ‖integerVector z‖ ^ (-(p:ℝ))) :=
    (summable_integerVector_rpow (by apply neg_lt_neg; exact_mod_cast hp)).mul_left _
  apply Summable.of_norm_bounded_eventually hsum
  have hz : ∀ᶠ z : d → ℤ in cofinite, 2*|R|+1 < ‖integerVector z‖ := by
    exact ((tendsto_norm_cocompact_atTop (E := d → ℝ)).comp
      (integerVector_tendsto (d := d))).eventually (eventually_gt_atTop (2*|R|+1))
  filter_upwards [hz] with z hz
  rw [norm_norm]
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  rintro ⟨x,hx⟩
  change ‖f (x + integerVector z)‖ ≤ C * 2^p * ‖integerVector z‖ ^ (-(p:ℝ))
  have hxR : ‖x‖ ≤ R := by simpa using hR hx
  have hzpos : 0 < ‖integerVector z‖ := by linarith [abs_nonneg R]
  have htri := norm_sub_le (x + integerVector z) x
  have hzle : ‖integerVector z‖/2 ≤ ‖x + integerVector z‖ := by
    simp only [add_sub_cancel_left] at htri
    linarith [le_abs_self R]
  have hwpos : 0 < ‖x + integerVector z‖ := lt_of_lt_of_le (by positivity) hzle
  have hbound : (‖integerVector z‖/2)^p * ‖f (x+integerVector z)‖ ≤ C :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hzle _) (norm_nonneg _)).trans
      (hdecay _)
  rw [Real.rpow_neg (norm_nonneg _),Real.rpow_natCast]
  apply (le_mul_inv_iff₀ (pow_pos hzpos p)).mpr
  rw [div_pow] at hbound
  have H := (div_le_iff₀ (by positivity : 0 < (2:ℝ)^p)).mp
    (show ‖f (x+integerVector z)‖ * ‖integerVector z‖^p / 2^p ≤ C by
      simpa only [div_mul_eq_mul_div,mul_comm] using hbound)
  exact H

lemma gaussian_polynomial_bound (b : ℝ) (hb : 0 < b) (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, |t|^p * Real.exp (-b*t^2) ≤ C := by
  let h : C₀(ℝ,ℝ) := {
    toFun t := |t|^p * Real.exp (-b*t^2)
    continuous_toFun := by fun_prop
    zero_at_infty' := by
      simpa only [Real.rpow_natCast] using
        tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact hb (p:ℝ) }
  refine ⟨‖h.toBCF‖+1,by positivity,fun t => ?_⟩
  have H := BoundedContinuousFunction.norm_coe_le_norm h.toBCF t
  exact (le_abs_self (h t)).trans (H.trans (by linarith))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def coordinateGaussian (A : (d → ℝ) ≃L[ℝ] E) (b : ℝ) : C(d → ℝ,ℂ) where
  toFun x := Complex.exp (-(b:ℂ) * ‖A x‖^2)
  continuous_toFun := by fun_prop

lemma coordinateGaussian_decay (A : (d → ℝ) ≃L[ℝ] E) (b : ℝ) (hb : 0 < b) (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, ‖x‖^p * ‖coordinateGaussian A b x‖ ≤ C := by
  obtain ⟨C,hC,hbound⟩ := gaussian_polynomial_bound b hb p
  let B := ‖A.symm.toContinuousLinearMap‖ + 1
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B^p*C,by positivity,fun x => ?_⟩
  have hx : ‖x‖ ≤ B * ‖A x‖ := by
    have H := A.symm.toContinuousLinearMap.le_opNorm (A x)
    simp only [ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply] at H
    exact H.trans (by dsimp [B]; nlinarith [norm_nonneg (A x)])
  have hnorm : ‖coordinateGaussian A b x‖ = Real.exp (-b*‖A x‖^2) := by
    simp [coordinateGaussian,Complex.norm_exp,pow_two]
  rw [hnorm]
  calc
    _ ≤ (B*‖A x‖)^p * Real.exp (-b*‖A x‖^2) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hx _) (Real.exp_nonneg _)
    _ = B^p * (‖A x‖^p * Real.exp (-b*‖A x‖^2)) := by rw [mul_pow,mul_assoc]
    _ ≤ B^p*C := mul_le_mul_of_nonneg_left (by simpa only [abs_norm] using hbound ‖A x‖)
      (pow_nonneg hB.le _)

lemma coordinateGaussian_locallyNormal (A : (d → ℝ) ≃L[ℝ] E) (b : ℝ) (hb : 0 < b) :
    LocallyNormal (coordinateGaussian A b) := by
  obtain ⟨C,hC,hdecay⟩ := coordinateGaussian_decay A b hb (Fintype.card d + 1)
  exact locallyNormal_of_polynomial_decay _ _ (Nat.lt_succ_self _) C hC hdecay

end PrimeDegreePackets.ThetaConstruction

open scoped FourierTransform
namespace PrimeDegreePackets.ThetaConstruction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma integral_comp_linearEquiv (A : E ≃L[ℝ] E) (f : E → ℂ) :
    (∫ x, f (A x)) = |(LinearMap.det A.toLinearMap)⁻¹| • ∫ x, f x := by
  have H := A.toHomeomorph.measurableEmbedding.integral_map f (μ := (volume : Measure E))
  have hd : LinearMap.det A.toLinearMap ≠ 0 := A.toLinearEquiv.isUnit_det'.ne_zero
  have hm : Measure.map A.toHomeomorph volume = ENNReal.ofReal |(LinearMap.det A.toLinearMap)⁻¹| • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hd
  rw [hm,integral_smul_measure,ENNReal.toReal_ofReal (abs_nonneg _)] at H
  exact H.symm

lemma integrable_comp_linearEquiv_iff (A : E ≃L[ℝ] E) (f : E → ℂ) :
    Integrable (fun x => f (A x)) ↔ Integrable f := by
  have hd : LinearMap.det A.toLinearMap ≠ 0 := A.toLinearEquiv.isUnit_det'.ne_zero
  have hm : Measure.map A.toHomeomorph volume = ENNReal.ofReal |(LinearMap.det A.toLinearMap)⁻¹| • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hd
  change Integrable (f ∘ A.toHomeomorph) volume ↔ Integrable f volume
  rw [←A.toHomeomorph.measurableEmbedding.integrable_map_iff,hm]
  exact integrable_smul_measure (by simp [hd]) (by simp)

lemma fourier_comp_linearEquiv (A : E ≃L[ℝ] E) (f : E → ℂ) (w : E) :
    𝓕 (fun x => f (A x)) w = |(LinearMap.det A.toLinearMap)⁻¹| •
      𝓕 f (A.symm.toContinuousLinearMap.adjoint w) := by
  rw [Real.fourier_eq,Real.fourier_eq]
  have H := integral_comp_linearEquiv A
    (fun x => Real.fourierChar (-inner ℝ x (A.symm.toContinuousLinearMap.adjoint w)) • f x)
  convert H using 1
  apply integral_congr_ae
  filter_upwards [] with x
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp

end PrimeDegreePackets.ThetaConstruction

open scoped BigOperators SchwartzMap FourierTransform
namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

@[simp] lemma schwartzCM_apply (f : 𝓢(d → ℝ,ℂ)) (x : d → ℝ) :
    f.toContinuousMap x = f x := rfl

def euclideanSchwartz (f : 𝓢(d → ℝ,ℂ)) : 𝓢(EuclideanSpace ℝ d,ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (EuclideanSpace.equiv d ℝ) f

def coordinateFourier (f : 𝓢(d → ℝ,ℂ)) : 𝓢(d → ℝ,ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (EuclideanSpace.equiv d ℝ).symm
    (𝓕 (euclideanSchwartz f))

lemma fourierCharacter_eq (m : d → ℤ) (x : d → ℝ) :
    fourierCharacter m x = Real.fourierChar (-(∑ i, x i * (m i:ℝ))) := by
  classical
  simp only [fourierCharacter,ContinuousMap.comp_apply,ContinuousMap.coe_mk,
    UnitAddTorus.mFourier,torusProjection,Pi.neg_apply,
    fourier_coe_apply,Int.cast_neg,Real.fourierChar_apply]
  rw [←Complex.exp_sum]
  congr 1
  push_cast
  simp only [←Finset.sum_neg_distrib,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma coordinateFourier_apply (f : 𝓢(d → ℝ,ℂ)) (m : d → ℤ) :
    coordinateFourier f (integerVector m) = ∫ x, fourierCharacter m x * f x := by
  change (𝓕 (euclideanSchwartz f)) (toLp 2 (integerVector m)) = _
  rw [SchwartzMap.fourier_coe,Real.fourier_eq]
  have H := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp d).integral_comp
    (MeasurableEquiv.toLp 2 (d → ℝ)).symm.measurableEmbedding
    (fun x => fourierCharacter m x * f x)
  rw [←H]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [Circle.smul_def,smul_eq_mul,fourierCharacter_eq,PiLp.inner_apply]
  congr 1
  congr 1
  apply congrArg Real.fourierChar
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp [integerVector,mul_comm]

lemma summable_schwartz_integerVector (f : 𝓢(d → ℝ,ℂ)) :
    Summable (fun z : d → ℤ => f (integerVector z)) := by
  have H := ContinuousMap.summable_of_locally_summable_norm (schwartz_locallyNormal f)
  have H' := (ContinuousMap.evalCLM ℂ (x := (0:d→ℝ))).summable H
  simpa [translate] using H'

lemma schwartz_multivariate_poisson (f : 𝓢(d → ℝ,ℂ)) (x : d → ℝ) :
    (∑' z : d → ℤ, f (x + integerVector z)) =
      ∑' m : d → ℤ, coordinateFourier f (integerVector m) *
        UnitAddTorus.mFourier m (torusProjection x) := by
  have H := multivariate_poisson f.toContinuousMap (schwartz_locallyNormal f) f.integrable
    ((summable_schwartz_integerVector (coordinateFourier f)).congr
      (fun m => coordinateFourier_apply f m)) x
  simpa only [schwartzCM_apply,←coordinateFourier_apply] using H

end PrimeDegreePackets.ThetaConstruction

open scoped BigOperators FourierTransform
namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

 

def adjointEquiv (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) :
    EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d where
  toLinearMap := B.toContinuousLinearMap.adjoint.toLinearMap
  invFun := B.symm.toContinuousLinearMap.adjoint
  left_inv x := by
    have H : B.toContinuousLinearMap.comp B.symm.toContinuousLinearMap =
        ContinuousLinearMap.id ℝ _ := by ext y i; simp
    have J := congrArg ContinuousLinearMap.adjoint H
    rw [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_id] at J
    exact congrArg (fun T : EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d => T x) J
  right_inv x := by
    have H : B.symm.toContinuousLinearMap.comp B.toContinuousLinearMap =
        ContinuousLinearMap.id ℝ _ := by ext y i; simp
    have J := congrArg ContinuousLinearMap.adjoint H
    rw [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_id] at J
    exact congrArg (fun T : EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d => T x) J
  continuous_toFun := B.toContinuousLinearMap.adjoint.continuous
  continuous_invFun := B.symm.toContinuousLinearMap.adjoint.continuous

def euclideanInteger (z : d → ℤ) : EuclideanSpace ℝ d := toLp 2 (integerVector z)

def coordinateBasis (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) :
    (d → ℝ) ≃L[ℝ] EuclideanSpace ℝ d := (EuclideanSpace.equiv d ℝ).symm.trans B

def latticeTheta (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) (b : ℝ) : ℂ :=
  ∑' z : d → ℤ, Complex.exp (-(b:ℂ) * ‖B (euclideanInteger z)‖^2)

lemma summable_of_locallyNormal (f : C(d → ℝ,ℂ)) (hf : LocallyNormal f) :
    Summable (fun z : d → ℤ => f (integerVector z)) := by
  have H := ContinuousMap.summable_of_locally_summable_norm hf
  have H' := (ContinuousMap.evalCLM ℂ (x := (0:d→ℝ))).summable H
  simpa [translate] using H'

lemma latticeTheta_summable (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (b : ℝ) (hb : 0 < b) :
    Summable (fun z : d → ℤ => Complex.exp (-(b:ℂ) * ‖B (euclideanInteger z)‖^2)) := by
  exact summable_of_locallyNormal (coordinateGaussian (coordinateBasis B) b)
    (coordinateGaussian_locallyNormal _ b hb)

lemma coordinate_fourierIntegral (f : (d → ℝ) → ℂ) (m : d → ℤ) :
    𝓕 (fun x : EuclideanSpace ℝ d => f x.ofLp) (euclideanInteger m) =
      ∫ x, fourierCharacter m x * f x := by
  rw [Real.fourier_eq]
  have H := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp d).integral_comp
    (MeasurableEquiv.toLp 2 (d → ℝ)).symm.measurableEmbedding
    (fun x => fourierCharacter m x * f x)
  rw [←H]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [Circle.smul_def,smul_eq_mul,fourierCharacter_eq,PiLp.inner_apply]
  congr 1
  congr 1
  apply congrArg Real.fourierChar
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp [euclideanInteger,integerVector,mul_comm]

lemma coordinateGaussian_integrable (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (b : ℝ) (hb : 0 < b) : Integrable (coordinateGaussian (coordinateBasis B) b) := by
  have hI : Integrable (fun x : EuclideanSpace ℝ d => Complex.exp (-(b:ℂ)*‖x‖^2)) := by
    simpa using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (V := EuclideanSpace ℝ d) (b := (b:ℂ)) hb 0 0
  have H := (integrable_comp_linearEquiv_iff B _).mpr hI
  have J := (PiLp.volume_preserving_toLp d).integrable_comp_emb
    (MeasurableEquiv.toLp 2 (d → ℝ)).measurableEmbedding
    (g := fun x : EuclideanSpace ℝ d => Complex.exp (-(b:ℂ) * ‖B x‖^2))
  exact J.mpr H

lemma coordinateGaussian_fourier (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (b : ℝ) (hb : 0 < b) (m : d → ℤ) :
    (∫ x, fourierCharacter m x * coordinateGaussian (coordinateBasis B) b x) =
      ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) *
        (Real.pi / (b:ℂ)) ^ ((Fintype.card d:ℂ)/2) *
        Complex.exp (-((Real.pi^2/b:ℝ):ℂ) *
          ‖adjointEquiv B.symm (euclideanInteger m)‖^2) := by
  rw [←coordinate_fourierIntegral]
  change 𝓕 (fun x => Complex.exp (-(b:ℂ) * ‖B x‖^2)) (euclideanInteger m) = _
  rw [fourier_comp_linearEquiv B (fun x => Complex.exp (-(b:ℂ) * ‖x‖^2)),
    fourier_gaussian_innerProductSpace (by exact hb)]
  simp only [Complex.real_smul,finrank_euclideanSpace]
  rw [mul_assoc]
  congr 2
  congr 1
  change -((Real.pi:ℂ)^2) * (‖B.symm.toContinuousLinearMap.adjoint (euclideanInteger m)‖:ℂ)^2 / (b:ℂ) =
    -((Real.pi^2/b:ℝ):ℂ) * (‖B.symm.toContinuousLinearMap.adjoint (euclideanInteger m)‖:ℂ)^2
  push_cast
  ring

 

theorem latticeTheta_inversion (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (b : ℝ) (hb : 0 < b) :
    latticeTheta B b = ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) *
      (Real.pi / (b:ℂ)) ^ ((Fintype.card d:ℂ)/2) *
        latticeTheta (adjointEquiv B.symm) (Real.pi^2/b) := by
  have hb' : 0 < Real.pi^2/b := div_pos (sq_pos_of_pos Real.pi_pos) hb
  have hsum : Summable (fun m : d → ℤ =>
      ∫ x, fourierCharacter m x * coordinateGaussian (coordinateBasis B) b x) := by
    simp_rw [coordinateGaussian_fourier B b hb]
    exact (latticeTheta_summable (adjointEquiv B.symm) _ hb').mul_left _
  have H := multivariate_poisson (coordinateGaussian (coordinateBasis B) b)
    (coordinateGaussian_locallyNormal _ b hb) (coordinateGaussian_integrable B b hb) hsum 0
  have hm (m : d → ℤ) : UnitAddTorus.mFourier m (torusProjection (0:d→ℝ)) = 1 := by
    simp [UnitAddTorus.mFourier,torusProjection]
  simp only [zero_add,coordinateGaussian_fourier B b hb,hm,mul_one,tsum_mul_left] at H
  exact H

end PrimeDegreePackets.ThetaConstruction

open MeasureTheory Set Filter Topology Module WithLp Asymptotics
namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

abbrev NonzeroIntegerVector (d : Type*) := {z : d → ℤ // z ≠ 0}

def thetaRemainder (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) (t : ℝ) : ℂ :=
  ∑' z : NonzeroIntegerVector d, Complex.exp (-(t:ℂ) * ‖B (euclideanInteger z.1)‖^2)

lemma thetaRemainder_summable (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    {t : ℝ} (ht : 0 < t) : Summable (fun z : NonzeroIntegerVector d =>
      Complex.exp (-(t:ℂ) * ‖B (euclideanInteger z.1)‖^2)) :=
  (latticeTheta_summable B t ht).subtype _

lemma gaussianTerm_norm (t r : ℝ) :
    ‖Complex.exp (-(t:ℂ) * (r:ℂ)^2)‖ = Real.exp (-t*r^2) := by
  simp [Complex.norm_exp,pow_two]

lemma thetaRemainder_eq (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    {t : ℝ} (ht : 0 < t) : thetaRemainder B t = latticeTheta B t - 1 := by
  classical
  let f := fun z : d → ℤ => Complex.exp (-(t:ℂ)*‖B (euclideanInteger z)‖^2)
  have H := (latticeTheta_summable B t ht).tsum_eq_add_tsum_ite 0
  have Hz : euclideanInteger (0 : d → ℤ) = 0 := by ext i; simp [euclideanInteger,integerVector]
  have H0 : f 0 = 1 := by simp [f,Hz]
  change latticeTheta B t = f 0 + ∑' z, if z = 0 then 0 else f z at H
  rw [H0] at H
  have HE : thetaRemainder B t = ∑' z, if z = 0 then 0 else f z := by
    change (∑' z : {z : d → ℤ | z ≠ 0}, f z.1) = _
    rw [tsum_subtype {z : d → ℤ | z ≠ 0} f]
    apply tsum_congr
    intro z
    by_cases hz : z = 0 <;> simp [hz,f]
  rw [HE]
  exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans H.symm)

lemma thetaRemainder_continuousOn (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) :
    ContinuousOn (thetaRemainder B) (Set.Ioi 0) := by
  intro t ht
  change 0 < t at ht
  have hc : ContinuousOn (thetaRemainder B) (Set.Ioi (t/2)) := by
    apply continuousOn_tsum (u := fun z : NonzeroIntegerVector d =>
      ‖Complex.exp (-((t/2:ℝ):ℂ)*‖B (euclideanInteger z.1)‖^2)‖)
    · intro z; fun_prop
    · exact (thetaRemainder_summable B (by linarith)).norm
    · intro z x hx
      change t/2 < x at hx
      rw [gaussianTerm_norm,gaussianTerm_norm]
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg ‖B (euclideanInteger z.1)‖]
  exact (hc.continuousAt (Ioi_mem_nhds (by linarith))).continuousWithinAt

lemma euclideanInteger_norm_one_le (z : NonzeroIntegerVector d) :
    1 ≤ ‖euclideanInteger z.1‖ := by
  obtain ⟨i,hi⟩ : ∃ i, z.1 i ≠ 0 := by
    by_contra! H
    exact z.2 (funext H)
  have H : (1:ℝ) ≤ |(z.1 i:ℝ)| := by exact_mod_cast Int.one_le_abs hi
  exact H.trans (by simpa [euclideanInteger,integerVector,Real.norm_eq_abs] using
    PiLp.norm_apply_le (euclideanInteger z.1) i)

lemma theta_lattice_lower_bound (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ z : NonzeroIntegerVector d, c ≤ ‖B (euclideanInteger z.1)‖ := by
  let R := ‖B.symm.toContinuousLinearMap‖ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  refine ⟨R⁻¹,inv_pos.mpr hR,fun z => ?_⟩
  have H := B.symm.toContinuousLinearMap.le_opNorm (B (euclideanInteger z.1))
  simp only [ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply] at H
  rw [inv_eq_one_div]
  apply (div_le_iff₀ hR).mpr
  rw [mul_comm]
  calc
    1 ≤ ‖euclideanInteger z.1‖ := euclideanInteger_norm_one_le z
    _ ≤ ‖B.symm.toContinuousLinearMap‖ * ‖B (euclideanInteger z.1)‖ := H
    _ ≤ R * ‖B (euclideanInteger z.1)‖ := by dsimp [R]; nlinarith [norm_nonneg (B (euclideanInteger z.1))]

lemma thetaRemainder_exponential_bound (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) :
    ∃ a C : ℝ, 0 < a ∧ 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
      ‖thetaRemainder B t‖ ≤ C * Real.exp (-a*t) := by
  obtain ⟨c,hc,hbound⟩ := theta_lattice_lower_bound B
  let v := fun z : NonzeroIntegerVector d =>
    ‖Complex.exp (-((1/2:ℝ):ℂ) * ‖B (euclideanInteger z.1)‖^2)‖
  have hv : Summable v := (thetaRemainder_summable B (by norm_num : (0:ℝ)<1/2)).norm
  refine ⟨c^2/2,∑' z, v z,by positivity,tsum_nonneg (fun z => norm_nonneg _),fun t ht => ?_⟩
  have ht' : 0 < t := by linarith
  calc
    ‖thetaRemainder B t‖ ≤ ∑' z : NonzeroIntegerVector d,
        ‖Complex.exp (-(t:ℂ)*‖B (euclideanInteger z.1)‖^2)‖ :=
      norm_tsum_le_tsum_norm (thetaRemainder_summable B ht').norm
    _ ≤ ∑' z, v z * Real.exp (-(c^2/2)*t) := by
      apply (thetaRemainder_summable B ht').norm.tsum_le_tsum _ (hv.mul_right _)
      intro z
      dsimp [v]
      rw [gaussianTerm_norm,gaussianTerm_norm,←Real.exp_add]
      have hz := hbound z
      have hz2 : c^2 ≤ ‖B (euclideanInteger z.1)‖^2 := sq_le_sq₀ hc.le (norm_nonneg _) |>.mpr hz
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg ‖B (euclideanInteger z.1)‖),
        mul_nonneg ht'.le (sub_nonneg.mpr hz2)]
    _ = _ := tsum_mul_right

 

def thetaTail (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) : ℝ → ℂ :=
  (Set.Ioi 1).indicator (fun t => thetaRemainder B (max t 1))

lemma thetaTail_locallyIntegrable (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) :
    LocallyIntegrable (thetaTail B) := by
  have hc : Continuous (fun t : ℝ => thetaRemainder B (max t 1)) :=
    (thetaRemainder_continuousOn B).comp_continuous (continuous_id.max continuous_const)
      (fun t => lt_of_lt_of_le zero_lt_one (le_max_right t 1))
  exact hc.locallyIntegrable.indicator measurableSet_Ioi

lemma thetaTail_bigO_exp (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) :
    ∃ a : ℝ, 0 < a ∧ thetaTail B =O[atTop] (fun t => Real.exp (-a*t)) := by
  obtain ⟨a,C,ha,_,hbound⟩ := thetaRemainder_exponential_bound B
  refine ⟨a,ha,IsBigO.of_bound C ?_⟩
  filter_upwards [eventually_gt_atTop (1:ℝ)] with t ht
  simpa [thetaTail,ht,max_eq_left ht.le,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using
    hbound t ht.le

lemma thetaTail_mellin_differentiable (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) :
    Differentiable ℂ (mellin (thetaTail B)) := by
  obtain ⟨a,ha,hbound⟩ := thetaTail_bigO_exp B
  intro s
  apply mellin_differentiableAt_of_isBigO_rpow_exp ha
    ((thetaTail_locallyIntegrable B).locallyIntegrableOn (Set.Ioi 0)) hbound (b := s.re-1) _ (by linarith)
  apply IsBigO.of_bound 0
  have H : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds zero_lt_one)
  filter_upwards [H] with t ht
  simp [thetaTail,not_lt.mpr ht.le]

end PrimeDegreePackets.ThetaConstruction
end
end

end OAI
