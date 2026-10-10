import Mathlib
import OAI.Geometry.BallPacking.Cauchy.GreenFormula

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion

section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance markedJetInst1 : NormedAddCommGroup (ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance markedJetInst2 : NormedSpace ℝ (ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance markedJetInst3 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance markedJetInst4 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance markedJetInst5 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance markedJetInst6 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance markedJetInst7 : NormedAddCommGroup (HMap ℂ (ℂ →L[ℝ] E)) := inferInstance
local instance markedJetInst8 : NormedSpace ℝ (HMap ℂ (ℂ →L[ℝ] E)) := inferInstance

def constJet (v : E) : COne ℂ E :=
  ⟨(const _ v,0),fun z => hasFDerivAt_const v z⟩

omit [CompleteSpace E] in
@[simp] lemma constJet_value (v : E) (z : ℂ) : cValue (constJet v) z = v := rfl
omit [CompleteSpace E] in
@[simp] lemma constJet_deriv (v : E) (z : ℂ) : cDeriv (constJet v) z = 0 := rfl

omit [CompleteSpace E] in
lemma constJet_norm_le (v : E) : ‖constJet v‖ ≤ ‖v‖ := by
  change max ‖const _ v‖ ‖(0 : HMap ℂ (ℂ →L[ℝ] E))‖ ≤ _
  rw [norm_zero]
  exact max_le (const_norm_le v) (norm_nonneg v)

def constJetCLM : E →L[ℝ] COne ℂ E :=
  LinearMap.mkContinuous
    { toFun := constJet
      map_add' := fun u v => by apply cValue_ext; intro z; rfl
      map_smul' := fun c v => by apply cValue_ext; intro z; rfl }
    1 (by intro v; change ‖constJet v‖ ≤ 1*‖v‖; rw [one_mul]; exact constJet_norm_le v)

def jetEval (z : ℂ) : COne ℂ E →L[ℝ] E :=
  (BoundedContinuousFunction.evalCLM ℝ z).comp ((valueCLM _).comp (jetValueCLM _))

omit [CompleteSpace E] in
@[simp] lemma jetEval_apply (z : ℂ) (u : COne ℂ E) : jetEval z u = cValue u z := rfl

def zeroNormalize : COne ℂ E →L[ℝ] COne ℂ E :=
  ContinuousLinearMap.id ℝ _ - constJetCLM.comp (jetEval 0)

omit [CompleteSpace E] in
@[simp] lemma zeroNormalize_value (u : COne ℂ E) (z : ℂ) :
    cValue (zeroNormalize u) z = cValue u z-cValue u 0 := rfl
omit [CompleteSpace E] in
@[simp] lemma zeroNormalize_deriv (u : COne ℂ E) (z : ℂ) :
    cDeriv (zeroNormalize u) z = cDeriv u z := by
  change cDeriv u z - 0 = _
  exact sub_zero _

def standardJetCR : COne ℂ E →L[ℝ] HMap ℂ E :=
  let L : HMap ℂ (ℂ →L[ℝ] E) →L[ℝ] HMap ℂ E := mapCLM _ (curlJet (E := E));
  -(L.comp (jetDerivCLM (D := ℂ) (E := E) ((1:ℝ)/3)))

omit [CompleteSpace E] in
@[simp] lemma standardJetCR_value (u : COne ℂ E) (z : ℂ) :
    valueCLM _ (standardJetCR u) z = cDeriv u z Complex.I - Complex.I • cDeriv u z 1 := by
  change -(Complex.I • cDeriv u z 1-cDeriv u z Complex.I) = _
  abel

omit [CompleteSpace E] in
lemma standardJetCR_zeroNormalize (u : COne ℂ E) :
    standardJetCR (zeroNormalize u) = standardJetCR u := by
  apply value_ext
  intro z
  simp only [standardJetCR_value,zeroNormalize_deriv]

omit [CompleteSpace E] in
lemma complex_differentiable_of_curl_zero {f : ℂ → E} {z : ℂ}
    (hd : DifferentiableAt ℝ f z) (hc : curlJet (fderiv ℝ f z) = 0) :
    DifferentiableAt ℂ f z := by
  let A := fderiv ℝ f z
  let L : ℂ →L[ℂ] E := ContinuousLinearMap.toSpanSingleton ℂ (A 1)
  have hI : A Complex.I = Complex.I • A 1 := by
    exact (sub_eq_zero.mp hc).symm
  have hL : L.restrictScalars ℝ = A := by
    ext w
    have hw : w = w.re • (1:ℂ) + w.im • Complex.I := by
      simpa only [Complex.real_smul,Complex.ofReal_one,mul_one] using (Complex.re_add_im w).symm
    have hAw : A w = w.re • A 1 + w.im • (Complex.I • A 1) := by
      conv_lhs => rw [hw]
      simp only [map_add,map_smul,hI]
    rw [hAw]
    change w • A 1 = _
    conv_lhs => rw [hw]
    rw [add_smul,smul_assoc,one_smul,smul_assoc]
  exact (hasFDerivAt_of_restrictScalars ℝ hd.hasFDerivAt hL).differentiableAt

omit [CompleteSpace E] in
lemma standardJetCR_injective_zeroMarked {u v : COne ℂ E}
    (hu : cValue u 0 = 0) (hv : cValue v 0 = 0)
    (he : standardJetCR u = standardJetCR v) : u = v := by
  have hd : Differentiable ℂ (cValue (u-v)) := by
    intro z
    apply complex_differentiable_of_curl_zero (c_differentiable (u-v) z)
    rw [c_fderiv]
    have h := congrArg (fun h : HMap ℂ E => valueCLM _ h z)
      (show standardJetCR (u-v) = 0 by rw [map_sub,he,sub_self])
    change -curlJet (cDeriv (u-v) z) = 0 at h
    exact neg_eq_zero.mp h
  apply cValue_ext
  intro z
  have h := hd.apply_eq_apply_of_bounded (cValue (u-v)).isBounded_range z 0
  change cValue u z-cValue v z = cValue u 0-cValue v 0 at h
  rw [hu,hv,sub_self] at h
  exact sub_eq_zero.mp h

variable {K : Set ℂ} (hK : IsCompact K)
local instance markedJetInst9 : NormedAddCommGroup (supportedHolder (E := E) K) := inferInstance
local instance markedJetInst10 : NormedSpace ℝ (supportedHolder (E := E) K) := inferInstance

def standardHolderInverse : supportedHolder (E := E) K →L[ℝ] COne ℂ E :=
  zeroNormalize.comp ((mapJetBilinear (D := ℂ) (E := E) (F := E) ((ContinuousLinearMap.lsmul ℝ ℂ (E := E)) (Complex.I/2))).comp
    (supportedCauchyCLM hK))

@[simp] lemma standardHolderInverse_value (g : supportedHolder (E := E) K) (z : ℂ) :
    cValue (standardHolderInverse hK g) z =
      (Complex.I/2) • (cauchyTransform (valueCLM _ g.val) z-cauchyTransform (valueCLM _ g.val) 0) := by
  simp only [standardHolderInverse, ContinuousLinearMap.comp_apply,zeroNormalize_value,
    mapJetBilinear_value,ContinuousLinearMap.lsmul_apply,supportedCauchyCLM_value,smul_sub]

lemma standardHolderInverse_zero (g : supportedHolder (E := E) K) :
    cValue (standardHolderInverse hK g) 0 = 0 := by rw [standardHolderInverse_value,sub_self,smul_zero]

lemma standardHolderInverse_residual (g : supportedHolder (E := E) K) :
    standardJetCR (standardHolderInverse hK g) = g.val := by
  rw [standardHolderInverse,ContinuousLinearMap.comp_apply,standardJetCR_zeroNormalize]
  apply value_ext
  intro z
  change -curlJet (((ContinuousLinearMap.lsmul ℝ ℂ (E := E)) (Complex.I/2)).comp
    (globalCauchyDerivative (valueCLM _ g.val) z)) = valueCLM _ g.val z
  have he : ((ContinuousLinearMap.lsmul ℝ ℂ (E := E)) (Complex.I/2)).comp
      (globalCauchyDerivative (valueCLM _ g.val) z) =
      (Complex.I/2) • globalCauchyDerivative (valueCLM _ g.val) z := rfl
  rw [he,curlJet_smul,globalCauchyDerivative_curl (valueCLM _ g.val).continuous
    (supportedHolder_integrable hK g) (norm_nonneg g.val)
    (by simpa only [dist_eq_norm] using norm_sub_value_le g.val),smul_smul]
  norm_num [Complex.I_mul_I,← mul_assoc]


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
universe u v
variable {D : Type v} {E F : Type u}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance smoothSuperInst1 : NormedAddCommGroup (E →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
local instance smoothSuperInst2 : NormedSpace ℝ (E →L[ℝ] F) := ContinuousLinearMap.toNormedSpace
local instance smoothSuperInst3 : NormedAddCommGroup (COne D E) := inferInstance
local instance smoothSuperInst4 : NormedSpace ℝ (COne D E) := inferInstance
local instance smoothSuperInst5 : NormedAddCommGroup (HMap D E) := inferInstance
local instance smoothSuperInst6 : NormedSpace ℝ (HMap D E) := inferInstance
local instance smoothSuperInst7 : NormedAddCommGroup (HMap D F) := inferInstance
local instance smoothSuperInst8 : NormedSpace ℝ (HMap D F) := inferInstance
local instance smoothSuperInst9 : NormedAddCommGroup (HMap D (E →L[ℝ] F)) := inferInstance
local instance smoothSuperInst10 : NormedSpace ℝ (HMap D (E →L[ℝ] F)) := inferInstance
local instance smoothSuperInst11 : ContinuousSMul ℝ (COne D E) := IsBoundedSMul.continuousSMul
local instance smoothSuperInst12 : NormedAddCommGroup (COne D E →L[ℝ] HMap D F) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance smoothSuperInst13 : NormedSpace ℝ (COne D E →L[ℝ] HMap D F) :=
  ContinuousLinearMap.toNormedSpace

lemma compactSupport_fderiv_of_perturbation {f : E → F} (c : F)
    (hc : HasCompactSupport (fun x => f x-c)) : HasCompactSupport (fderiv ℝ f) := by
  have he : fderiv ℝ (fun x => f x-c) = fderiv ℝ f := funext fun x => fderiv_sub_const c
  rw [← he]
  exact hc.fderiv ℝ

def derivativeAssembly : HMap D (E →L[ℝ] F) →L[ℝ] (COne D E →L[ℝ] HMap D F) :=
  ((bilinCLM (X := D) (α := (1:ℝ)/3) (ContinuousLinearMap.apply (E := E) ℝ F).flip).precompR
    (COne D E)).flip (jetValueCLM (D := D) (E := E) ((1:ℝ)/3))

@[simp] lemma derivativeAssembly_value (A : HMap D (E →L[ℝ] F)) (u : COne D E) (x : D) :
    valueCLM _ (derivativeAssembly (D := D) (E := E) (F := F) A u) x = valueCLM _ A x (cValue u x) := rfl

variable {f : E → F} (hf : BoundedCThree f)
  {b : D → E} (hb : Differentiable ℝ b) {B : ℝ} (hB : 0 ≤ B)
  (hbB : ∀ x, ‖fderiv ℝ b x‖ ≤ B)

lemma superposeDeriv_eq_assembly (u : COne D E) :
    superposeDeriv hf hb hB hbB u = derivativeAssembly (D := D) (E := E) (F := F) (coefficient hf hb hB hbB u) := rfl

lemma coefficient_eq_superpose (hdf : BoundedCThree (fderiv ℝ f)) (u : COne D E) :
    coefficient hf hb hB hbB u = superpose hdf hb hB hbB u := by
  apply value_ext
  intro x
  rfl

lemma superpose_eq_of_proofs (hf' : BoundedCThree f) :
    superpose hf hb hB hbB = superpose hf' hb hB hbB := rfl

theorem superpose_contDiff_nat (m : ℕ) :
    ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
      (hf : BoundedCThree f) (c : F) (_hc : HasCompactSupport (fun x => f x-c)),
      ContDiff ℝ m (superpose (D := D) hf hb hB hbB) := by
  induction m with
  | zero =>
      intro F _ _ f hf c hc
      have hc : Continuous (superpose (D := D) hf hb hB hbB) :=
        continuous_iff_continuousAt.mpr fun u =>
          (superpose_hasFDerivAt hf hb hB hbB u).continuousAt
      exact contDiff_zero.mpr hc
  | succ m ih =>
      intro F _ _ f hf c hc
      have hdc : HasCompactSupport (fderiv ℝ f) := compactSupport_fderiv_of_perturbation c hc
      have hdf : BoundedCThree (fderiv ℝ f) :=
        boundedCThree_of_compactSupport hf.fderiv_smooth hdc
      have hc' : HasCompactSupport (fun x => fderiv ℝ f x - 0) := by
        simpa only [sub_zero] using hdc
      have hd : ContDiff ℝ m (superpose hdf hb hB hbB) := ih hdf 0 hc'
      have hder : superposeDeriv (D := D) hf hb hB hbB =
          fun u => derivativeAssembly (D := D) (E := E) (F := F)
            (superpose hdf hb hB hbB u) := by
        funext u
        rw [superposeDeriv_eq_assembly, coefficient_eq_superpose]
      rw [show ((m+1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞)+1 by simp]
      apply contDiff_succ_iff_hasFDerivAt.mpr
      refine ⟨superposeDeriv hf hb hB hbB, ?_, fun u => superpose_hasFDerivAt hf hb hB hbB u⟩
      rw [hder]
      exact (derivativeAssembly (D := D) (E := E) (F := F)).contDiff.comp hd

theorem superpose_contDiff (c : F) (hc : HasCompactSupport (fun x => f x-c)) :
    ContDiff ℝ ∞ (superpose (D := D) hf hb hB hbB) := by
  apply contDiff_infty.mpr
  intro m
  exact superpose_contDiff_nat hb hB hbB m hf c hc


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance crSectInst1 : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance crSectInst2 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance crSectInst3 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance crSectInst4 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance crSectInst5 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance crSectInst6 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance crSectInst7 : NormedAddCommGroup (HMap ℂ (E →L[ℝ] E)) := inferInstance
local instance crSectInst8 : NormedSpace ℝ (HMap ℂ (E →L[ℝ] E)) := inferInstance

def jetDirection (v : ℂ) : COne ℂ E →L[ℝ] HMap ℂ E :=
  (mapCLM _ (ContinuousLinearMap.apply ℝ E v)).comp (jetDerivCLM _)

@[simp] lemma jetDirection_value (v : ℂ) (u : COne ℂ E) (z : ℂ) :
    valueCLM _ (jetDirection v u) z = cDeriv u z v := rfl

def affine (p : E) (a : ℂ →L[ℝ] E) (z : ℂ) : E := p + a z

lemma affine_hasFDerivAt (p : E) (a : ℂ →L[ℝ] E) (z : ℂ) :
    HasFDerivAt (affine p a) a z := by
  convert! (hasFDerivAt_const p z).add a.hasFDerivAt using 1
  simp only [zero_add]

lemma affine_differentiable (p : E) (a : ℂ →L[ℝ] E) : Differentiable ℝ (affine p a) :=
  fun z => (affine_hasFDerivAt p a z).differentiableAt

lemma affine_fderiv_bound (p : E) (a : ℂ →L[ℝ] E) (z : ℂ) :
    ‖fderiv ℝ (affine p a) z‖ ≤ ‖a‖ := by rw [(affine_hasFDerivAt p a z).fderiv]

def affineCurve (p : E) (a : ℂ →L[ℝ] E) (u : COne ℂ E) (z : ℂ) : E :=
  affine p a z + cValue u z

lemma affineCurve_hasFDerivAt (p : E) (a : ℂ →L[ℝ] E) (u : COne ℂ E) (z : ℂ) :
    HasFDerivAt (affineCurve p a u) (a+cDeriv u z) z :=
  (affine_hasFDerivAt p a z).add (c_hasFDerivAt u z)

lemma affineCurve_fderiv (p : E) (a : ℂ →L[ℝ] E) (u : COne ℂ E) (z : ℂ) :
    fderiv ℝ (affineCurve p a u) z = a+cDeriv u z :=
  (affineCurve_hasFDerivAt p a u z).fderiv

variable {J : E → E →L[ℝ] E} (hJ : BoundedCThree J)

def structureAlong (p : E) (a : ℂ →L[ℝ] E) (u : COne ℂ E) : HMap ℂ (E →L[ℝ] E) :=
  superpose hJ (affine_differentiable p a) (norm_nonneg a) (affine_fderiv_bound p a) u

@[simp] lemma structureAlong_value (p : E) (a : ℂ →L[ℝ] E) (u : COne ℂ E) (z : ℂ) :
    valueCLM _ (structureAlong hJ p a u) z = J (affineCurve p a u z) := rfl

def structureAlongDeriv (p : E) (a : ℂ →L[ℝ] E) (u : COne ℂ E) :
    COne ℂ E →L[ℝ] HMap ℂ (E →L[ℝ] E) :=
  superposeDeriv hJ (affine_differentiable p a) (norm_nonneg a) (affine_fderiv_bound p a) u

@[simp] lemma structureAlongDeriv_value (p : E) (a : ℂ →L[ℝ] E)
    (u h : COne ℂ E) (z : ℂ) :
    valueCLM _ (structureAlongDeriv hJ p a u h) z =
      fderiv ℝ J (affineCurve p a u z) (cValue h z) := rfl

lemma structureAlong_hasFDerivAt (p : E) (a : ℂ →L[ℝ] E) (u : COne ℂ E) :
    HasFDerivAt (structureAlong hJ p a) (structureAlongDeriv hJ p a u) u := by
  exact superpose_hasFDerivAt hJ (affine_differentiable p a) (norm_nonneg a)
    (affine_fderiv_bound p a) u

def crSection (p : E) (a : ℂ →L[ℝ] E) (u : COne ℂ E) : HMap ℂ E :=
  const _ (a Complex.I) + jetDirection Complex.I u -
    bilinCLM (X := ℂ) (α := (1:ℝ)/3) (ContinuousLinearMap.apply ℝ E).flip (structureAlong hJ p a u)
      (const _ (a 1) + jetDirection 1 u)

@[simp] lemma crSection_value (p : E) (a : ℂ →L[ℝ] E) (u : COne ℂ E) (z : ℂ) :
    valueCLM _ (crSection hJ p a u) z =
      fderiv ℝ (affineCurve p a u) z Complex.I -
        J (affineCurve p a u z) (fderiv ℝ (affineCurve p a u) z 1) := by
  rw [affineCurve_fderiv]
  rfl

def crSectionDeriv (p : E) (a : ℂ →L[ℝ] E) (u : COne ℂ E) :
    COne ℂ E →L[ℝ] HMap ℂ E :=
  jetDirection Complex.I -
    (bilinCLM (X := ℂ) (α := (1:ℝ)/3) (ContinuousLinearMap.apply ℝ E).flip (structureAlong hJ p a u)).comp
      (jetDirection 1) -
    ((bilinCLM (X := ℂ) (α := (1:ℝ)/3) (ContinuousLinearMap.apply ℝ E).flip).flip
      (const _ (a 1)+jetDirection 1 u)).comp (structureAlongDeriv hJ p a u)

lemma crSection_hasFDerivAt (p : E) (a : ℂ →L[ℝ] E) (u : COne ℂ E) :
    HasFDerivAt (crSection hJ p a) (crSectionDeriv hJ p a u) u := by
  have hI := (hasFDerivAt_const (const _ (a Complex.I)) u).add
    (jetDirection (E := E) Complex.I).hasFDerivAt
  have h1 := (hasFDerivAt_const (const _ (a 1)) u).add
    (jetDirection (E := E) 1).hasFDerivAt
  have hS := structureAlong_hasFDerivAt hJ p a u
  have hB := (bilinCLM (X := ℂ) (α := (1:ℝ)/3)
    (ContinuousLinearMap.apply ℝ E).flip).hasFDerivAt_of_bilinear
      (G := HMap ℂ E) (G' := COne ℂ E) hS h1
  convert! hI.sub hB using 1
  apply ContinuousLinearMap.ext
  intro v
  apply value_ext
  intro z
  simp only [crSectionDeriv, sub_apply, add_apply, zero_add,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.precompR_apply,
    ContinuousLinearMap.precompL_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply, Pi.add_apply]
  congr 1
  abel_nf

@[simp] lemma crSectionDeriv_value (p : E) (a : ℂ →L[ℝ] E)
    (u h : COne ℂ E) (z : ℂ) :
    valueCLM _ (crSectionDeriv hJ p a u h) z =
      fderiv ℝ (cValue h) z Complex.I - J (affineCurve p a u z) (fderiv ℝ (cValue h) z 1) -
      (fderiv ℝ J (affineCurve p a u z) (cValue h z))
        (fderiv ℝ (affineCurve p a u) z 1) := by
  rw [affineCurve_fderiv, c_fderiv]
  rfl

lemma crSection_eq_zero_iff (p : E) (a : ℂ →L[ℝ] E) (u : COne ℂ E) :
    crSection hJ p a u = 0 ↔ ∀ z,
      fderiv ℝ (affineCurve p a u) z Complex.I =
        J (affineCurve p a u z) (fderiv ℝ (affineCurve p a u) z 1) := by
  constructor
  · intro h z
    have he := congrArg (fun v : HMap ℂ E => valueCLM _ v z) h
    rw [crSection_value] at he
    change _ = 0 at he
    exact sub_eq_zero.mp he
  · intro h
    apply value_ext
    intro z
    rw [crSection_value, h z, sub_self]
    rfl

lemma crSection_contDiff (c : E →L[ℝ] E) (hc : HasCompactSupport (fun x => J x-c))
    (p : E) (a : ℂ →L[ℝ] E) : ContDiff ℝ ∞ (crSection hJ p a) := by
  have hS : ContDiff ℝ ∞ (structureAlong hJ p a) :=
    superpose_contDiff hJ (affine_differentiable p a) (norm_nonneg a)
      (affine_fderiv_bound p a) c hc
  have hI : ContDiff ℝ ∞ (fun u : COne ℂ E => const ((1:ℝ)/3) (a Complex.I) +
      jetDirection Complex.I u) := contDiff_const.add (jetDirection (E := E) Complex.I).contDiff
  have h1 : ContDiff ℝ ∞ (fun u : COne ℂ E => const ((1:ℝ)/3) (a 1) +
      jetDirection 1 u) := contDiff_const.add (jetDirection (E := E) 1).contDiff
  exact hI.sub (((bilinCLM (X := ℂ) (α := (1:ℝ)/3)
    (ContinuousLinearMap.apply (E := E) ℝ E).flip).contDiff.comp hS).clm_apply h1)

lemma complex_cr_iff (A : ℂ →L[ℝ] E) (Q : E →L[ℝ] E) (hQ : ∀ v, Q (Q v) = -v) :
    (∀ w : ℂ, A (Complex.I*w) = Q (A w)) ↔ A Complex.I = Q (A 1) := by
  constructor
  · intro h; simpa only [mul_one] using h 1
  · intro h w
    have hdec (z : ℂ) : A z = z.re • A 1 + z.im • A Complex.I := by
      have he : z = z.re • (1 : ℂ) + z.im • Complex.I := by
        simpa only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_one, mul_one]
          using (Complex.re_add_im z).symm
      conv_lhs => rw [he]
      exact map_add A _ _ |>.trans (congrArg₂ (· + ·) (map_smul A _ _) (map_smul A _ _))
    rw [hdec (Complex.I*w), hdec w, map_add, map_smul, map_smul, h, hQ]
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, zero_sub, neg_smul, smul_neg]
    abel_nf


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance markedAffineInst1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance markedAffineInst2 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance markedAffineInst3 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance markedAffineInst4 : NormedSpace ℝ (HMap ℂ E) := inferInstance

def markedModel (K : Set ℂ) : Submodule ℝ (COne ℂ E) :=
  (jetEval (E := E) 0).ker ⊓ (supportedHolder K).comap standardJetCR.toLinearMap

omit [CompleteSpace E] in
lemma mem_markedModel (K : Set ℂ) (u : COne ℂ E) :
    u ∈ markedModel K ↔ cValue u 0 = 0 ∧ standardJetCR u ∈ supportedHolder K := Iff.rfl

omit [CompleteSpace E] in
lemma markedModel_closed (K : Set ℂ) : IsClosed (markedModel (E := E) K : Set (COne ℂ E)) :=
  (jetEval (E := E) 0).isClosed_ker.inter ((supportedHolder_closed K).preimage standardJetCR.continuous)

instance (K : Set ℂ) : CompleteSpace (markedModel (E := E) K) :=
  (markedModel_closed K).completeSpace_coe

variable {K : Set ℂ} (hK : IsCompact K)
local instance markedAffineInst5 : NormedAddCommGroup (markedModel (E := E) K) := inferInstance
local instance markedAffineInst6 : NormedSpace ℝ (markedModel (E := E) K) := inferInstance
local instance markedAffineInst7 : NormedAddCommGroup (supportedHolder (E := E) K) := inferInstance
local instance markedAffineInst8 : NormedSpace ℝ (supportedHolder (E := E) K) := inferInstance

def markedCR : markedModel (E := E) K →L[ℝ] supportedHolder (E := E) K :=
  standardJetCR.restrict (fun _u hu => hu.2)

def markedInverse : supportedHolder (E := E) K →L[ℝ] markedModel (E := E) K :=
  (standardHolderInverse hK).codRestrict (markedModel K) (fun g => by
    apply (mem_markedModel K _).mpr
    refine ⟨standardHolderInverse_zero hK g, ?_⟩
    rw [standardHolderInverse_residual]; exact g.property)

def markedCREquiv : markedModel (E := E) K ≃L[ℝ] supportedHolder (E := E) K :=
  ContinuousLinearEquiv.equivOfInverse (markedCR (E := E) (K := K)) (markedInverse (E := E) hK)
    (by
      intro u
      apply Subtype.ext
      exact standardJetCR_injective_zeroMarked
        (standardHolderInverse_zero hK (markedCR (E := E) (K := K) u)) u.property.1
        (standardHolderInverse_residual hK (markedCR (E := E) (K := K) u)))
    (by
      intro g
      apply Subtype.ext
      exact standardHolderInverse_residual hK g)

def markedSlope (p q : E) (u : COne ℂ E) : E := q-p-cValue u 1

def markedCurve (p q : E) (u : COne ℂ E) (z : ℂ) : E :=
  p + z • markedSlope p q u + cValue u z

omit [CompleteSpace E] in
lemma markedCurve_zero (p q : E) {u : COne ℂ E} (hu : cValue u 0 = 0) :
    markedCurve p q u 0 = p := by simp [markedCurve,hu]

omit [CompleteSpace E] in
lemma markedCurve_one (p q : E) (u : COne ℂ E) : markedCurve p q u 1 = q := by
  simp only [markedCurve,one_smul,markedSlope]
  abel

def complexSlope (a : E) : ℂ →L[ℝ] E :=
  (ContinuousLinearMap.toSpanSingleton ℂ a).restrictScalars ℝ

omit [CompleteSpace E] in
@[simp] lemma complexSlope_apply (a : E) (z : ℂ) : complexSlope a z = z • a := rfl

omit [CompleteSpace E] in
lemma markedCurve_hasFDerivAt (p q : E) (u : COne ℂ E) (z : ℂ) :
    HasFDerivAt (markedCurve p q u) (complexSlope (markedSlope p q u)+cDeriv u z) z :=
  affineCurve_hasFDerivAt p (complexSlope (markedSlope p q u)) u z

omit [CompleteSpace E] in
lemma markedCurve_fderiv (p q : E) (u : COne ℂ E) (z : ℂ) :
    fderiv ℝ (markedCurve p q u) z = complexSlope (markedSlope p q u)+cDeriv u z :=
  (markedCurve_hasFDerivAt p q u z).fderiv

omit [CompleteSpace E] in
lemma markedCurve_standardResidual (p q : E) (u : COne ℂ E) (z : ℂ) :
    fderiv ℝ (markedCurve p q u) z Complex.I -
      Complex.I • fderiv ℝ (markedCurve p q u) z 1 = valueCLM _ (standardJetCR u) z := by
  rw [markedCurve_fderiv,standardJetCR_value]
  simp only [add_apply,complexSlope_apply,one_smul,smul_add]
  abel

omit [CompleteSpace E] in
lemma markedSlope_continuous (p q : E) : Continuous (markedSlope p q : COne ℂ E → E) :=
  continuous_const.sub (jetEval (E := E) 1).continuous

omit [CompleteSpace E] in
lemma markedSlope_nonzero_open (p q : E) : IsOpen {u : COne ℂ E | markedSlope p q u ≠ 0} :=
  isOpen_ne_fun (markedSlope_continuous p q) continuous_const

omit [CompleteSpace E] in
lemma markedCurve_asymptote (p q : E) (u : COne ℂ E) :
    Tendsto (fun z : ℂ => z⁻¹ • markedCurve p q u z) (cocompact ℂ)
      (𝓝 (markedSlope p q u)) := by
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa only [← Metric.cobounded_eq_cocompact] using (tendsto_inv₀_cobounded (α := ℂ))
  have hb : IsBoundedUnder (· ≤ ·) (cocompact ℂ) (norm ∘ (cValue u : ℂ → E)) :=
    ⟨‖cValue u‖, eventually_map.mpr (Eventually.of_forall fun z => (cValue u).norm_coe_le_norm z)⟩
  have hzero := hi.zero_smul_isBoundedUnder_le hb
  have ht := ((hi.smul_const p).add_const (markedSlope p q u)).add hzero
  simp only [zero_smul,zero_add,add_zero] at ht
  apply ht.congr'
  filter_upwards [(isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with z hz
  have hz0 : z ≠ 0 := by simpa only [mem_compl_iff,mem_singleton_iff] using hz
  simp only [markedCurve,smul_add,smul_smul,inv_mul_cancel₀ hz0,one_smul]



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
