import Mathlib
import OAI.Geometry.BallPacking.Fredholm.FrameFredholm

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion

section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance ptCRInst1 : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance ptCRInst2 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance ptCRInst3 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance ptCRInst4 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance ptCRInst5 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance ptCRInst6 : NormedSpace ℝ (HMap ℂ E) := inferInstance
variable {K : Set ℂ}
local instance ptCRInst7 : NormedAddCommGroup (markedModel (E := E) K) := inferInstance
local instance ptCRInst8 : NormedSpace ℝ (markedModel (E := E) K) := inferInstance
local instance ptCRInst9 : AddCommGroup (markedModel (E := E) K) := ptCRInst7.toAddCommGroup
local instance ptCRInst10 : Module ℝ (markedModel (E := E) K) := ptCRInst8.toModule
local instance ptCRInst11 : TopologicalSpace (markedModel (E := E) K) :=
  ptCRInst7.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

def markedDerivEval (z v : ℂ) : markedModel (E := E) K →L[ℝ] E :=
  ((BoundedContinuousFunction.evalCLM ℝ z).comp (valueCLM _)).comp
    ((jetDirection v).comp (markedModel (E := E) K).subtypeL)

omit [CompleteSpace E] in
@[simp] lemma markedDerivEval_value [CompleteSpace E] (z v : ℂ) (h : markedModel (E := E) K) :
    markedDerivEval (E := E) (K := K) z v h = cDeriv h.val z v := rfl

def markedVariation (z : ℂ) : markedModel (E := E) K →L[ℝ] E :=
  markedEval z - ((ContinuousLinearMap.lsmul ℝ ℂ (E := E)) z).comp (markedEval 1)

omit [CompleteSpace E] in
@[simp] lemma markedVariation_value [CompleteSpace E] (z : ℂ) (h : markedModel (E := E) K) :
    markedVariation (E := E) (K := K) z h = cValue h.val z - z • cValue h.val 1 := rfl

def markedDerivativeVariation (z v : ℂ) : markedModel (E := E) K →L[ℝ] E :=
  markedDerivEval z v - ((ContinuousLinearMap.lsmul ℝ ℂ (E := E)) v).comp (markedEval 1)

omit [CompleteSpace E] in
@[simp] lemma markedDerivativeVariation_value [CompleteSpace E] (z v : ℂ) (h : markedModel (E := E) K) :
    markedDerivativeVariation (E := E) (K := K) z v h = cDeriv h.val z v - v • cValue h.val 1 := rfl

omit [CompleteSpace E] in
lemma markedCurve_variation [CompleteSpace E] (p q : E) (u : COne ℂ E) (h : markedModel (E := E) K) (z : ℂ) :
    markedCurve p q (u+h.val) z = markedCurve p q u z + markedVariation (E := E) (K := K) z h := by
  simp only [markedCurve,markedSlope_add,cValue_add,markedVariation_value,smul_sub]
  abel

omit [CompleteSpace E] in
lemma markedCurve_derivative_variation [CompleteSpace E] (p q : E) (u : COne ℂ E)
    (h : markedModel (E := E) K) (z v : ℂ) :
    fderiv ℝ (markedCurve p q (u+h.val)) z v =
      fderiv ℝ (markedCurve p q u) z v + markedDerivativeVariation (E := E) (K := K) z v h := by
  have h₁ := congrArg (fun L : ℂ →L[ℝ] E => L v) (markedCurve_fderiv p q (u+h.val) z)
  have h₂ := congrArg (fun L : ℂ →L[ℝ] E => L v) (markedCurve_fderiv p q u z)
  calc
    _ = (complexSlope (markedSlope p q (u+h.val))+cDeriv (u+h.val) z) v := h₁
    _ = (complexSlope (markedSlope p q u)+cDeriv u z) v +
        markedDerivativeVariation (E := E) (K := K) z v h := by
      simp only [add_apply,complexSlope_apply,markedSlope_add,smul_sub,
        markedDerivativeVariation_value]
      change v • markedSlope p q u-v • cValue h.val 1 + (cDeriv u z v+cDeriv h.val z v) = _
      abel
    _ = _ := congrArg (fun w : E => w+markedDerivativeVariation (E := E) (K := K) z v h) h₂.symm

lemma markedCurve_model_hasFDerivAt (p q : E) (u : COne ℂ E) (z : ℂ) :
    HasFDerivAt (fun h : markedModel (E := E) K => markedCurve p q (u+h.val) z)
      (markedVariation z) 0 := by
  have hd := (hasFDerivAt_const (markedCurve p q u z) (0 : markedModel (E := E) K)).add
    (markedVariation (E := E) (K := K) z).hasFDerivAt
  have hd' : HasFDerivAt (fun h : markedModel (E := E) K =>
      markedCurve p q u z + markedVariation (E := E) (K := K) z h)
      (markedVariation (E := E) (K := K) z) 0 := by
    convert! hd using 1
    simp only [zero_add]
  apply hd'.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun h => markedCurve_variation p q u h z)

lemma markedCurve_derivative_model_hasFDerivAt (p q : E) (u : COne ℂ E) (z v : ℂ) :
    HasFDerivAt (fun h : markedModel (E := E) K => fderiv ℝ (markedCurve p q (u+h.val)) z v)
      (markedDerivativeVariation z v) 0 := by
  have hd := (hasFDerivAt_const (fderiv ℝ (markedCurve p q u) z v)
    (0 : markedModel (E := E) K)).add
    (markedDerivativeVariation (E := E) (K := K) z v).hasFDerivAt
  have hd' : HasFDerivAt (fun h : markedModel (E := E) K =>
      fderiv ℝ (markedCurve p q u) z v + markedDerivativeVariation (E := E) (K := K) z v h)
      (markedDerivativeVariation (E := E) (K := K) z v) 0 := by
    convert! hd using 1
    simp only [zero_add]
  apply hd'.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun h => markedCurve_derivative_variation p q u h z v)

def pointMarkedCR (J : E → E →L[ℝ] E) (p q : E) (u : COne ℂ E) (z : ℂ)
    (h : markedModel (E := E) K) : E :=
  fderiv ℝ (markedCurve p q (u+h.val)) z Complex.I -
    J (markedCurve p q (u+h.val) z) (fderiv ℝ (markedCurve p q (u+h.val)) z 1)

def pointMarkedCRDeriv (J : E → E →L[ℝ] E) (p q : E) (u : COne ℂ E) (z : ℂ) :
    markedModel (E := E) K →L[ℝ] E :=
  markedDerivativeVariation z Complex.I -
    ((J (markedCurve p q u z)).comp (markedDerivativeVariation z 1) +
      ((fderiv ℝ J (markedCurve p q u z)).flip (fderiv ℝ (markedCurve p q u) z 1)).comp
        (markedVariation z))

lemma pointMarkedCR_hasFDerivAt {J : E → E →L[ℝ] E} (hJ : Differentiable ℝ J)
    (p q : E) (u : COne ℂ E) (z : ℂ) :
    HasFDerivAt (pointMarkedCR (K := K) J p q u z) (pointMarkedCRDeriv J p q u z) 0 := by
  have hU := markedCurve_model_hasFDerivAt (K := K) p q u z
  have hY := markedCurve_derivative_model_hasFDerivAt (K := K) p q u z Complex.I
  have hX := markedCurve_derivative_model_hasFDerivAt (K := K) p q u z 1
  have hJC := (hJ (markedCurve p q (u+(0 : markedModel (E := E) K).val) z)).hasFDerivAt.comp 0 hU
  have hN := hJC.clm_apply hX
  convert! hY.sub hN using 1
  apply ContinuousLinearMap.ext
  intro h
  simp only [pointMarkedCRDeriv,sub_apply,add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,Function.comp_apply,Submodule.coe_zero,add_zero]

omit [CompleteSpace E] in
lemma pointMarkedCRDeriv_value [CompleteSpace E] (J : E → E →L[ℝ] E) (p q : E) (u : COne ℂ E)
    (z : ℂ) (h : markedModel (E := E) K) :
    pointMarkedCRDeriv J p q u z h =
      cDeriv h.val z Complex.I - J (markedCurve p q u z) (cDeriv h.val z 1) -
        fderiv ℝ J (markedCurve p q u z) (cValue h.val z) (fderiv ℝ (markedCurve p q u) z 1) +
      (J (markedCurve p q u z) (cValue h.val 1) - Complex.I • cValue h.val 1 +
        fderiv ℝ J (markedCurve p q u z) (z • cValue h.val 1) (fderiv ℝ (markedCurve p q u) z 1)) := by
  simp only [pointMarkedCRDeriv,sub_apply,add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,markedDerivativeVariation_value,markedVariation_value,
    one_smul,map_sub,sub_apply]
  abel


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {n : ℕ}
local instance compLinInst1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance compLinInst2 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace
local instance compLinInst3 : NormedAddCommGroup (Phase n →L[ℝ] End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance compLinInst4 : NormedSpace ℝ (Phase n →L[ℝ] End n) := ContinuousLinearMap.toNormedSpace
local instance compLinInst5 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance compLinInst6 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
local instance compLinInst7 : NormedAddCommGroup (HMap ℂ (Phase n)) := inferInstance
local instance compLinInst8 : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance
local instance compLinInst9 : NormedAddCommGroup (HMap ℂ (End n)) := inferInstance
local instance compLinInst10 : NormedSpace ℝ (HMap ℂ (End n)) := inferInstance

variable {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J) (hc : ∀ x, Compatible (J x)) {B : ℝ}
  (hstd : ∀ x, B < ‖x‖ → J x=standardJ n) (p q : Phase n) (u : COne ℂ (Phase n))

def completedDStructure : HMap ℂ (Phase n →L[ℝ] End n) :=
  affineJetValue (boundedCThree_of_compactSupport (hJ.fderiv_right (by simp))
    (compactSupport_fderiv_of_perturbation (standardJ n)
      (compactPerturbation_of_outside_constant _ hstd))) p (complexSlope (markedSlope p q u)) u

def completedDX : HMap ℂ (Phase n) :=
  const _ (markedSlope p q u)+jetDirection 1 u

@[simp] lemma completedDX_value (z : ℂ) :
    valueCLM _ (completedDX p q u) z = fderiv ℝ (markedCurve p q u) z 1 := by
  rw [markedCurve_fderiv]
  simp only [add_apply,complexSlope_apply,one_smul]
  rfl

def completedQ : HMap ℂ (End n) :=
  bilinCLM (X := ℂ) (α := (1:ℝ)/3)
    (ContinuousLinearMap.flipₗᵢ ℝ (Phase n) (Phase n) (Phase n)).toContinuousLinearEquiv.toContinuousLinearMap
    (completedDStructure hJ hstd p q u) (completedDX p q u)

@[simp] lemma completedQ_value (z : ℂ) (v : Phase n) :
    valueCLM _ (completedQ hJ hstd p q u) z v =
      fderiv ℝ J (markedCurve p q u z) v (fderiv ℝ (markedCurve p q u) z 1) := by
  change fderiv ℝ J (markedCurve p q u z) v (valueCLM _ (completedDX p q u) z) = _
  exact congrArg (fun w : Phase n => fderiv ℝ J (markedCurve p q u z) v w) (completedDX_value p q u z)

variable {K : Set ℂ} (hK : IsCompact K) (he : ∀ z ∉ K, B < ‖markedCurve p q u z‖)
local instance compLinInst11 : NormedAddCommGroup (markedModel (E := Phase n) K) := inferInstance
local instance compLinInst12 : NormedSpace ℝ (markedModel (E := Phase n) K) := inferInstance
local instance compLinInst13 : NormedAddCommGroup (supportedHolder (E := Phase n) K) := inferInstance
local instance compLinInst14 : NormedSpace ℝ (supportedHolder (E := Phase n) K) := inferInstance

include he in
lemma completedQ_zero_outside : ∀ z ∉ K, valueCLM _ (completedQ hJ hstd p q u) z=0 := by
  intro z hz
  apply ContinuousLinearMap.ext
  intro v
  have hd := fderiv_standard_outside hstd (he z hz)
  calc
    _ = fderiv ℝ J (markedCurve p q u z) v (fderiv ℝ (markedCurve p q u) z 1) :=
      completedQ_value hJ hstd p q u z v
    _ = 0 := by rw [hd]; rfl

variable (b : ContDiffBump (0:ℂ)) (hb : K ⊆ Metric.closedBall (0:ℂ) b.rIn)

def completedMarkHolder : HMap ℂ (End n) :=
  jetValueCLM _ (completedStructureJet hJ hstd p q u)-const _ (standardJ n) +
    bilinCLM (X := ℂ) (α := (1:ℝ)/3) (ContinuousLinearMap.compL ℝ (Phase n) (Phase n) (Phase n))
      (completedQ hJ hstd p q u)
      (mapCLM _ (ContinuousLinearMap.lsmul ℝ ℂ) (jetValueCLM _ (cutoffCoordinate b)))

include he hb in
lemma completedMarkHolder_value (z : ℂ) (v : Phase n) :
    valueCLM _ (completedMarkHolder hJ hstd p q u b) z v =
      J (markedCurve p q u z) v - Complex.I • v +
        fderiv ℝ J (markedCurve p q u z) (z • v) (fderiv ℝ (markedCurve p q u) z 1) := by
  have hcut : valueCLM _ (completedQ hJ hstd p q u) z ((b z • z) • v) =
      valueCLM _ (completedQ hJ hstd p q u) z (z • v) := by
    by_cases hz : z∈K
    · rw [b.one_of_mem_closedBall (hb hz),one_smul]
    · have hzero := completedQ_zero_outside hJ hstd p q u he z hz
      rw [hzero]; rfl
  change J (markedCurve p q u z) v-Complex.I • v +
    valueCLM _ (completedQ hJ hstd p q u) z ((b z • z) • v) = _
  exact congrArg (fun w : Phase n => J (markedCurve p q u z) v-Complex.I • v+w)
    (hcut.trans (completedQ_value hJ hstd p q u z (z • v)))

include he hb in
lemma completedMarkHolder_zero_outside : ∀ z ∉ K, valueCLM _ (completedMarkHolder hJ hstd p q u b) z=0 := by
  intro z hz
  apply ContinuousLinearMap.ext
  intro v
  have hj := hstd _ (he z hz)
  have hd := fderiv_standard_outside hstd (he z hz)
  calc
    _ = J (markedCurve p q u z) v-Complex.I • v +
        fderiv ℝ J (markedCurve p q u z) (z • v) (fderiv ℝ (markedCurve p q u) z 1) :=
      completedMarkHolder_value hJ hstd p q u he b hb z v
    _ = 0 := by rw [hj,hd]; change Complex.I • v-Complex.I • v+0=0; abel

def completedZeroOrder : markedModel (E := Phase n) K →L[ℝ] supportedHolder (E := Phase n) K :=
  markedZeroOrder (completedQ hJ hstd p q u) (completedQ_zero_outside hJ hstd p q u he)

def completedMarkCorrection : markedModel (E := Phase n) K →L[ℝ] supportedHolder (E := Phase n) K :=
  markedFiniteCorrection (completedMarkHolder hJ hstd p q u b)
    (completedMarkHolder_zero_outside hJ hstd p q u he b hb)

include hK in
lemma completedZeroOrder_compact : IsCompactOperator (completedZeroOrder hJ hstd p q u he) :=
  markedZeroOrder_isCompact_of_compact (E := Phase n) hK _ _

lemma completedMarkCorrection_compact : IsCompactOperator (completedMarkCorrection hJ hstd p q u he b hb) :=
  markedFiniteCorrection_isCompact (E := Phase n) _ _

def completedLinearized : markedModel (E := Phase n) K →L[ℝ] supportedHolder (E := Phase n) K :=
  completedPrincipal hJ hstd p q u he +
    (-completedZeroOrder hJ hstd p q u he + completedMarkCorrection hJ hstd p q u he b hb)

lemma completedLinearized_value (v : markedModel (E := Phase n) K) (z : ℂ) :
    valueCLM _ (completedLinearized hJ hstd p q u he b hb v).val z = pointMarkedCRDeriv J p q u z v := by
  have hQ := completedQ_value hJ hstd p q u z (cValue v.val z)
  have hM := completedMarkHolder_value hJ hstd p q u he b hb z (cValue v.val 1)
  change (cDeriv v.val z Complex.I-J (markedCurve p q u z) (cDeriv v.val z 1)) +
    (-valueCLM _ (completedQ hJ hstd p q u) z (cValue v.val z) +
      valueCLM _ (completedMarkHolder hJ hstd p q u b) z (cValue v.val 1)) = _
  calc
    _ = (cDeriv v.val z Complex.I-J (markedCurve p q u z) (cDeriv v.val z 1)) +
        (-fderiv ℝ J (markedCurve p q u z) (cValue v.val z) (fderiv ℝ (markedCurve p q u) z 1) +
        (J (markedCurve p q u z) (cValue v.val 1)-Complex.I • cValue v.val 1 +
        fderiv ℝ J (markedCurve p q u z) (z • cValue v.val 1) (fderiv ℝ (markedCurve p q u) z 1))) :=
      congrArg₂ (fun x y : Phase n =>
        (cDeriv v.val z Complex.I-J (markedCurve p q u z) (cDeriv v.val z 1))+(-x+y)) hQ hM
    _ = _ := by
      have hv := pointMarkedCRDeriv_value J p q u z v
      calc
        _ = cDeriv v.val z Complex.I-J (markedCurve p q u z) (cDeriv v.val z 1) -
          fderiv ℝ J (markedCurve p q u z) (cValue v.val z) (fderiv ℝ (markedCurve p q u) z 1) +
          (J (markedCurve p q u z) (cValue v.val 1)-Complex.I • cValue v.val 1 +
          fderiv ℝ J (markedCurve p q u z) (z • cValue v.val 1) (fderiv ℝ (markedCurve p q u) z 1)) := by abel
        _ = _ := hv.symm

include hc hK in
lemma completedLinearized_fredholm : (completedLinearized hJ hstd p q u he b hb).IsFredholm ∧
    Module.finrank ℝ (completedLinearized hJ hstd p q u he b hb).ker =
      Module.finrank ℝ (supportedHolder (E := Phase n) K ⧸ (completedLinearized hJ hstd p q u he b hb).range) := by
  let C : markedModel (E := Phase n) K →L[ℝ] supportedHolder (E := Phase n) K :=
    -completedZeroOrder hJ hstd p q u he + completedMarkCorrection hJ hstd p q u he b hb
  have hC : IsCompactOperator C :=
    (completedZeroOrder_compact hJ hstd p q u hK he).neg.add
      (completedMarkCorrection_compact hJ hstd p q u he b hb)
  have hh := completedPrincipal_add_compact_fredholm hJ hc hstd p q u hK he C hC
  exact hh


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
section Transport
variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
lemma fredholm_from_coordinates (D : X →L[ℝ] Z) (e : Y ≃L[ℝ] X)
    (L : Y →L[ℝ] Z) (he : D.comp e.toContinuousLinearMap=L) (hL : L.IsFredholm) : D.IsFredholm := by
  have hh := fredholm_pre_equiv L hL e.symm
  have h : L.comp e.symm.toContinuousLinearMap=D := by
    rw [←he]
    apply ContinuousLinearMap.ext
    intro x
    exact congrArg D (e.apply_symm_apply x)
  exact h ▸ hh
end Transport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance freeFredInst1 : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance freeFredInst2 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance freeFredInst3 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance freeFredInst4 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance freeFredInst5 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance freeFredInst6 : NormedSpace ℝ (HMap ℂ E) := inferInstance
variable {K : Set ℂ}
local instance freeFredInst7 : NormedAddCommGroup (freeModel (E := E) K) := inferInstance
local instance freeFredInst8 : NormedSpace ℝ (freeModel (E := E) K) := inferInstance
local instance freeFredInst9 : NormedAddCommGroup (markedModel (E := E) K) := inferInstance
local instance freeFredInst10 : NormedSpace ℝ (markedModel (E := E) K) := inferInstance
local instance freeFredInst11 : NormedAddCommGroup (supportedHolder (E := E) K) := inferInstance
local instance freeFredInst12 : NormedSpace ℝ (supportedHolder (E := E) K) := inferInstance

local instance freeFredInst13 : AddCommGroup (freeModel (E := E) K) := (freeFredInst7 (E := E) (K := K)).toAddCommGroup
local instance freeFredInst14 : Module ℝ (freeModel (E := E) K) := (freeFredInst8 (E := E) (K := K)).toModule
local instance freeFredInst15 : AddCommGroup (markedModel (E := E) K) := (freeFredInst9 (E := E) (K := K)).toAddCommGroup
local instance freeFredInst16 : Module ℝ (markedModel (E := E) K) := (freeFredInst10 (E := E) (K := K)).toModule
local instance freeFredInst17 : AddCommGroup (supportedHolder (E := E) K) := (freeFredInst11 (E := E) (K := K)).toAddCommGroup
local instance freeFredInst18 : Module ℝ (supportedHolder (E := E) K) := (freeFredInst12 (E := E) (K := K)).toModule

variable (A C : HMap ℂ (E →L[ℝ] E))
  (hA : ∀ z ∉ K, valueCLM _ A z = complexI (E := E))
  (hC : ∀ z ∉ K, valueCLM _ C z = 0)

def freePrincipal : freeModel (E := E) K →L[ℝ] supportedHolder (E := E) K :=
  (markedPrincipal A hA).comp freeNormalize

@[simp] lemma freePrincipal_value (u : freeModel (E := E) K) (z : ℂ) :
    valueCLM _ (freePrincipal A hA u).val z =
      cDeriv u.val z Complex.I-valueCLM _ A z (cDeriv u.val z 1) := by
  change cDeriv (zeroNormalize u.val) z Complex.I-valueCLM _ A z (cDeriv (zeroNormalize u.val) z 1)=_
  rw [zeroNormalize_deriv]

def freeZeroOrder : freeModel (E := E) K →L[ℝ] supportedHolder (E := E) K :=
  ((jetZeroOrder C).comp (freeModel (E := E) K).subtypeL).codRestrict _ (fun u => by
    apply (mem_supportedHolder _ _).mpr
    intro z hz
    change valueCLM _ C z (cValue u.val z)=0
    rw [hC z hz,zero_apply])

omit [CompleteSpace E] in
@[simp] lemma freeZeroOrder_value [CompleteSpace E] (u : freeModel (E := E) K) (z : ℂ) :
    valueCLM _ (freeZeroOrder C hC u).val z = valueCLM _ C z (cValue u.val z) := rfl

def constantZeroOrder : E →L[ℝ] supportedHolder (E := E) K :=
  ((holderCoefficientAction C).comp constHolderCLM).codRestrict _ (fun c => by
    apply (mem_supportedHolder _ _).mpr
    intro z hz
    change valueCLM _ C z c=0
    rw [hC z hz,zero_apply])

def freeLinearized : freeModel (E := E) K →L[ℝ] supportedHolder (E := E) K :=
  freePrincipal A hA-freeZeroOrder C hC

lemma freeLinearized_coords :
    (freeLinearized A C hA hC).comp (freeEquiv (E := E) (K := K)).symm.toContinuousLinearMap =
      (markedPrincipal A hA-markedZeroOrder C hC).comp
        (ContinuousLinearMap.snd ℝ E (markedModel (E := E) K)) +
      (-constantZeroOrder C hC).comp (ContinuousLinearMap.fst ℝ E (markedModel (E := E) K)) := by
  apply ContinuousLinearMap.ext
  intro v
  apply Subtype.ext
  apply value_ext
  intro z
  have hp := freePrincipal_value A hA (freeSum (E := E) (K := K) v) z
  have hq := freeZeroOrder_value C hC (freeSum (E := E) (K := K) v) z
  have hs := freeSum_value (E := E) (K := K) v z
  have hd := freeSum_deriv (E := E) (K := K) v z
  have hp' := hp.trans (congrArg (fun L : ℂ →L[ℝ] E => L Complex.I-valueCLM _ A z (L 1)) hd)
  have hq' := hq.trans (congrArg (valueCLM _ C z) hs)
  have hh := congrArg₂ (fun x y : E => x-y) hp' hq'
  apply hh.trans
  change (cDeriv v.2.val z Complex.I-valueCLM _ A z (cDeriv v.2.val z 1))-
    valueCLM _ C z (v.1+cValue v.2.val z) =
    ((cDeriv v.2.val z Complex.I-valueCLM _ A z (cDeriv v.2.val z 1))-
      valueCLM _ C z (cValue v.2.val z)) + -valueCLM _ C z v.1
  rw [map_add]
  abel

lemma freeLinearized_fredholm [FiniteDimensional ℝ E]
    (hP : (markedPrincipal A hA-markedZeroOrder C hC).IsFredholm) :
    (freeLinearized A C hA hC).IsFredholm := by
  let L := (markedPrincipal A hA-markedZeroOrder C hC).comp
    (ContinuousLinearMap.snd ℝ E (markedModel (E := E) K)) +
    (-constantZeroOrder C hC).comp (ContinuousLinearMap.fst ℝ E (markedModel (E := E) K))
  have hf : L.IsFredholm := fredholm_finite_extension _ hP (-constantZeroOrder C hC)
  exact fredholm_from_coordinates (freeLinearized (E := E) (K := K) A C hA hC)
    (freeEquiv (E := E) (K := K)).symm L (freeLinearized_coords (E := E) (K := K) A C hA hC) hf

lemma freePrincipal_fredholm [FiniteDimensional ℝ E] (hP : (markedPrincipal A hA).IsFredholm) :
    (freePrincipal A hA).IsFredholm := by
  have hs : (ContinuousLinearMap.snd ℝ E (markedModel (E := E) K)).IsFredholm := fredholm_snd_finite
  have hn : (freeNormalize (E := E) (K := K)).IsFredholm := by
    exact fredholm_pre_equiv (ContinuousLinearMap.snd ℝ E (markedModel (E := E) K))
      hs (freeEquiv (E := E) (K := K))
  exact fredholm_comp (freeNormalize (E := E) (K := K)) (markedPrincipal A hA) hn hP


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance chartDerInst1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance chartDerInst2 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance chartDerInst3 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance chartDerInst4 : NormedSpace ℝ (HMap ℂ E) := inferInstance
variable {K : Set ℂ}
local instance chartDerInst5 : NormedAddCommGroup (supportedHolder (E := E) K) := inferInstance
local instance chartDerInst6 : NormedSpace ℝ (supportedHolder (E := E) K) := inferInstance

def supportedEval (z : ℂ) : supportedHolder (E := E) K →L[ℝ] E :=
  ((BoundedContinuousFunction.evalCLM ℝ z).comp (valueCLM _)).comp
    (supportedHolder (E := E) K).subtypeL

omit [CompleteSpace E] in
@[simp] lemma supportedEval_value [CompleteSpace E] (z : ℂ) (g : supportedHolder (E := E) K) :
    supportedEval (E := E) (K := K) z g = valueCLM _ g.val z := rfl

variable {n : ℕ}
local instance chartDerInst7 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance chartDerInst8 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace

def compactJPerturbation (J : Phase n → End n) (x : Phase n) : End n := J x-standardJ n

lemma compactJPerturbation_smooth {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J) :
    ContDiff ℝ ∞ (compactJPerturbation J) := hJ.sub contDiff_const

lemma compactJPerturbation_compact {J : Phase n → End n} {B : ℝ}
    (hstd : ∀ x, B < ‖x‖ → J x = standardJ n) : HasCompactSupport (compactJPerturbation J) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Phase n) B)
  intro x hx
  by_contra hxB
  apply hx
  change J x-standardJ n=0
  rw [hstd x (by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hxB),sub_self]

variable {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J) {B : ℝ}
    (hstd : ∀ x, B < ‖x‖ → J x = standardJ n)

include hJ hstd in
theorem compactJPerturbationBound : BoundedCThree (compactJPerturbation J) :=
  boundedCThree_of_compactSupport (compactJPerturbation_smooth hJ) (compactJPerturbation_compact hstd)

include hstd in
lemma compactJPerturbation_outside : ∀ x, B < ‖x‖ → compactJPerturbation J x = 0 := by
  intro x hx
  exact sub_eq_zero.mpr (hstd x hx)

variable (b : ContDiffBump (0:ℂ)) (p q : Phase n)
local instance chartDerInst9 : NormedAddCommGroup (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance chartDerInst10 : NormedSpace ℝ (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance chartDerInst11 : AddCommGroup (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (chartDerInst9 (n := n) b).toAddCommGroup
local instance chartDerInst12 : Module ℝ (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (chartDerInst10 (n := n) b).toModule
local instance chartDerInst13 : TopologicalSpace (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) :=
  (chartDerInst9 (n := n) b).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
local instance chartDerInst14 : ContinuousSMul ℝ
    (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) :=
  IsBoundedSMul.continuousSMul

variable (u : markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut))

def actualMarkedChart := markedChart (compactJPerturbationBound hJ hstd) b p q u

lemma actualMarkedChart_contDiff : ContDiff ℝ ∞ (actualMarkedChart hJ hstd b p q u) :=
  markedChart_contDiff (compactJPerturbationBound hJ hstd) b (compactJPerturbation_compact hstd) p q u

lemma actualMarkedChart_value
    (h : markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut))
    (he : ∀ z : ℂ, b.rIn ≤ ‖z‖ → B < ‖markedCurve p q (u.val+h.val) z‖ ∧
      B < ‖truncatedCurve b p q u.val h.val z‖) (z : ℂ) :
    supportedEval (E := Phase n) z (actualMarkedChart hJ hstd b p q u h) =
      pointMarkedCR J p q u.val z h := by
  have hx := markedChart_actual_value (compactJPerturbationBound hJ hstd) b
    (compactJPerturbation_outside hstd) p q u h he z
  change valueCLM _ ((markedChart (compactJPerturbationBound hJ hstd) b p q u h).val) z = _
  rw [hx]
  have hI (v : Phase n) : standardJ n v = Complex.I • v := rfl
  simp only [pointMarkedCR,compactJPerturbation,sub_apply,hI]
  abel

lemma actualMarkedChart_fderiv_eval
    (he : ∀ᶠ h in 𝓝 (0 : markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)),
      ∀ z : ℂ, b.rIn ≤ ‖z‖ → B < ‖markedCurve p q (u.val+h.val) z‖ ∧
        B < ‖truncatedCurve b p q u.val h.val z‖) (z : ℂ) :
    (supportedEval (E := Phase n) (K := Metric.closedBall (0:ℂ) b.rOut) z).comp
      (fderiv ℝ (actualMarkedChart hJ hstd b p q u) 0) =
        pointMarkedCRDeriv J p q u.val z := by
  have hd := ((actualMarkedChart_contDiff hJ hstd b p q u).differentiable (by simp) 0).hasFDerivAt
  have hdE := (supportedEval (E := Phase n) (K := Metric.closedBall (0:ℂ) b.rOut) z).hasFDerivAt.comp 0 hd
  have hdP := pointMarkedCR_hasFDerivAt (K := Metric.closedBall (0:ℂ) b.rOut)
    (hJ.differentiable (by simp)) p q u.val z
  have heq : (fun h : markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut) =>
      supportedEval (E := Phase n) z (actualMarkedChart hJ hstd b p q u h)) =ᶠ[𝓝 0]
      pointMarkedCR J p q u.val z := by
    filter_upwards [he] with h hh
    exact actualMarkedChart_value hJ hstd b p q u h hh z
  exact hdE.unique (hdP.congr_of_eventuallyEq heq)


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance freeChartInst1 : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance freeChartInst2 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance freeChartInst3 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance freeChartInst4 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance freeChartInst5 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance freeChartInst6 : NormedSpace ℝ (HMap ℂ E) := inferInstance
variable {J : E → E →L[ℝ] E} (hJ : BoundedCThree J) (b : ContDiffBump (0:ℂ)) (p a : E)
local instance freeChartInst7 : NormedAddCommGroup (freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance freeChartInst8 : NormedSpace ℝ (freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance freeChartInst9 : NormedAddCommGroup (supportedHolder (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance freeChartInst10 : NormedSpace ℝ (supportedHolder (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance freeChartInst11 : AddCommGroup (freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := (freeChartInst7 (E := E) b).toAddCommGroup
local instance freeChartInst12 : Module ℝ (freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := (freeChartInst8 (E := E) b).toModule
local instance freeChartInst13 : TopologicalSpace (freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := (freeChartInst7 (E := E) b).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
local instance freeChartInst14 : AddCommGroup (COne ℂ E) := (freeChartInst3 (E := E)).toAddCommGroup
local instance freeChartInst15 : Module ℝ (COne ℂ E) := (freeChartInst4 (E := E)).toModule
local instance freeChartInst16 : TopologicalSpace (COne ℂ E) := (freeChartInst3 (E := E)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
variable (u : freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut))

def freeChart (v : freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) :
    supportedHolder (E := E) (Metric.closedBall (0:ℂ) b.rOut) :=
  freeCR (E := E) (K := Metric.closedBall (0:ℂ) b.rOut) (u+v) - supportedSourceCutoff b
    (standardJetCR (u.val+v.val)-crSection hJ p (complexSlope a) (u.val+v.val))

omit [CompleteSpace E] in
lemma freeChart_contDiff [CompleteSpace E] (hc : HasCompactSupport (fun x => J x-complexI (E := E))) :
    ContDiff ℝ ∞ (freeChart hJ b p a u) := by
  have hu : ContDiff ℝ ∞ (fun v : freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut) => u.val+v.val) :=
    contDiff_const.add (freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)).subtypeL.contDiff
  have hL : ContDiff ℝ ∞ (fun v : freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut) => freeCR (E := E) (K := Metric.closedBall (0:ℂ) b.rOut) (u+v)) :=
    (freeCR (E := E) (K := Metric.closedBall (0:ℂ) b.rOut)).contDiff.comp (contDiff_const.add contDiff_id)
  exact hL.sub ((supportedSourceCutoff (E := E) b).contDiff.comp
    (((standardJetCR (E := E)).contDiff.comp hu).sub
      ((crSection_contDiff hJ complexI hc p (complexSlope a)).comp hu)))

omit [CompleteSpace E] in
lemma freeChart_value [CompleteSpace E] (v : freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) (z : ℂ) :
    valueCLM _ (freeChart hJ b p a u v).val z =
      valueCLM _ (standardJetCR (u.val+v.val)) z - b z •
        (valueCLM _ (standardJetCR (u.val+v.val)) z-
          valueCLM _ (crSection hJ p (complexSlope a) (u.val+v.val)) z) := rfl

omit [CompleteSpace E] in
lemma crSection_value_of_standard [CompleteSpace E] (w : COne ℂ E) (z : ℂ)
    (hz : J (affineCurve p (complexSlope a) w z)=complexI (E := E)) :
    valueCLM _ (crSection hJ p (complexSlope a) w) z = valueCLM _ (standardJetCR w) z := by
  rw [crSection_value,affineCurve_fderiv,standardJetCR_value,hz]
  change (Complex.I • a+cDeriv w z Complex.I)-Complex.I • ((1:ℂ) • a+cDeriv w z 1) = _
  rw [one_smul]
  rw [smul_add]
  abel

omit [CompleteSpace E] in
lemma cutoff_residual_algebra [CompleteSpace E] (s t : E) (c : ℝ) (hc : c=1 ∨ s=t) :
    s-c • (s-t)=t := by
  rcases hc with rfl | rfl
  · rw [one_smul]; abel
  · rw [sub_self,smul_zero,sub_zero]

lemma freeChart_true_value {B : ℝ} (hstd : ∀ x, B < ‖x‖ → J x=complexI (E := E))
    (v : freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut))
    (he : ∀ z, b.rIn ≤ ‖z‖ → B < ‖affineCurve p (complexSlope a) (u.val+v.val) z‖) (z : ℂ) :
    valueCLM _ (freeChart hJ b p a u v).val z =
      valueCLM _ (crSection hJ p (complexSlope a) (u.val+v.val)) z := by
  apply (freeChart_value hJ b p a u v z).trans
  apply cutoff_residual_algebra
  by_cases hz : z ∈ Metric.closedBall (0:ℂ) b.rIn
  · exact Or.inl (b.one_of_mem_closedBall hz)
  · have hz' : b.rIn ≤ ‖z‖ := by
      simp only [Metric.mem_closedBall,dist_zero_right] at hz
      exact (lt_of_not_ge hz).le
    exact Or.inr (crSection_value_of_standard hJ p a _ z (hstd _ (he z hz'))).symm

lemma freeChart_hasFDerivAt_eval {B : ℝ} (hstd : ∀ x, B < ‖x‖ → J x=complexI (E := E))
    (he : ∀ᶠ v in 𝓝 (0 : freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)),
      ∀ z, b.rIn ≤ ‖z‖ → B < ‖affineCurve p (complexSlope a) (u.val+v.val) z‖) (z : ℂ) :
    HasFDerivAt (fun v => valueCLM _ (freeChart hJ b p a u v).val z)
      (((BoundedContinuousFunction.evalCLM ℝ z).comp (valueCLM _)).comp
        ((crSectionDeriv hJ p (complexSlope a) u.val).comp
          (freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)).subtypeL)) 0 := by
  let S := (freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)).subtypeL
  have hu : HasFDerivAt (fun v => u.val+S v) S 0 := by
    have hh := (hasFDerivAt_const u.val (0 : freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut))).add S.hasFDerivAt
    convert! hh using 1
    simp only [zero_add]
  have hu' : HasFDerivAt (fun v => u.val+S v) S (0 : freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := hu
  have hd0 : HasFDerivAt (crSection hJ p (complexSlope a)) (crSectionDeriv hJ p (complexSlope a) u.val) (u.val+S 0) := by
    simpa only [map_zero,add_zero] using crSection_hasFDerivAt hJ p (complexSlope a) u.val
  have hd := hd0.comp (f := fun v : freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut) => u.val+S v) 0 hu'
  have heval := (((BoundedContinuousFunction.evalCLM ℝ z).comp (valueCLM _)).hasFDerivAt.comp 0 hd)
  apply heval.congr_of_eventuallyEq
  filter_upwards [he] with v hv
  exact freeChart_true_value hJ b p a u hstd v hv z



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
