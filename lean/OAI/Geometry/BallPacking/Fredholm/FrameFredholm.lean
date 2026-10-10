import Mathlib
import OAI.Geometry.BallPacking.Fredholm.CompactFredholmAlternative

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion

section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] [ProperSpace E]
local instance frameFredInst1 : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance frameFredInst2 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance frameFredInst3 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance frameFredInst4 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance frameFredInst5 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance frameFredInst6 : NormedSpace ℝ (HMap ℂ E) := inferInstance
variable {K : Set ℂ} (hK : IsCompact K)
local instance frameFredInst7 : NormedAddCommGroup (markedModel (E := E) K) := inferInstance
local instance frameFredInst8 : NormedSpace ℝ (markedModel (E := E) K) := inferInstance
local instance frameFredInst9 : NormedAddCommGroup (supportedHolder (E := E) K) := inferInstance
local instance frameFredInst10 : NormedSpace ℝ (supportedHolder (E := E) K) := inferInstance
local instance frameFredInst11 : AddCommGroup (markedModel (E := E) K) :=
  (frameFredInst7 (E := E) (K := K)).toAddCommGroup
local instance frameFredInst12 : Module ℝ (markedModel (E := E) K) :=
  (frameFredInst8 (E := E) (K := K)).toModule
local instance frameFredInst13 : AddCommGroup (supportedHolder (E := E) K) :=
  (frameFredInst9 (E := E) (K := K)).toAddCommGroup
local instance frameFredInst14 : Module ℝ (supportedHolder (E := E) K) :=
  (frameFredInst10 (E := E) (K := K)).toModule

include hK in
lemma framedJetPrincipal_add_compact_fredholm
    (M N : COne ℂ (E →L[ℝ] E)) (m r : ℝ)
    (hM : ∀ z ∉ K, cValue M z = m • ContinuousLinearMap.id ℝ E)
    (hN : ∀ z ∉ K, cValue N z = r • ContinuousLinearMap.id ℝ E)
    (hNM : ∀ z v, cValue N z (cValue M z v) = v)
    (hMN : ∀ z v, cValue M z (cValue N z v) = v)
    (A : HMap ℂ (E →L[ℝ] E))
    (hA : ∀ z ∉ K, valueCLM _ A z = (ContinuousLinearMap.lsmul ℝ ℂ (E := E)) Complex.I)
    (hi : ∀ z v, cValue M z (valueCLM _ A z v) = Complex.I • cValue M z v)
    (C : markedModel (E := E) K →L[ℝ] supportedHolder (E := E) K)
    (hC : IsCompactOperator C) :
    (markedPrincipal A hA+C).IsFredholm ∧
      Module.finrank ℝ (markedPrincipal A hA+C).ker =
        Module.finrank ℝ (supportedHolder (E := E) K ⧸ (markedPrincipal A hA+C).range) := by
  let Z : markedModel (E := E) K →L[ℝ] supportedHolder (E := E) K :=
    markedZeroOrder (frameCRCoefficient M) (frameCRCoefficient_zero_outside hK.isClosed M m hM)
  let d : markedModel (E := E) K ≃L[ℝ] supportedHolder (E := E) K :=
    (markedCoefficientEquiv hK.isClosed M N m r hM hN hNM hMN).trans (markedCREquiv hK)
  let e : supportedHolder (E := E) K ≃L[ℝ] supportedHolder (E := E) K :=
    supportedCoefficientEquiv (jetValueCLM _ M) (jetValueCLM _ N) hNM hMN
  have hz : IsCompactOperator Z := markedZeroOrder_isCompact_of_compact hK _ _
  have he : e.toContinuousLinearMap.comp (markedPrincipal A hA) = d.toContinuousLinearMap-Z :=
    frame_conjugates_principal hK.isClosed M m hM A hA hi
  have hh := framed_compact_perturbation_fredholm (E := markedModel (E := E) K)
    (F := supportedHolder (E := E) K) (markedPrincipal A hA) Z C d e he hz hC
  exact hh


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter

lemma compactPerturbation_of_outside_constant {D F : Type*} [NormedAddCommGroup D]
    [ProperSpace D] [NormedAddCommGroup F] {P : D → F} (c : F) {B : ℝ}
    (hP : ∀ x, B < ‖x‖ → P x=c) : HasCompactSupport (fun x => P x-c) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0:D) B)
  intro x hx
  by_contra hxB
  apply hx
  change P x-c=0
  rw [hP x (by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hxB),sub_self]

variable {n : ℕ}
local instance ccFrameInst1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance ccFrameInst2 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace
local instance ccFrameInst3 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance ccFrameInst4 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
local instance ccFrameInst5 : NormedAddCommGroup (HMap ℂ (Phase n)) := inferInstance
local instance ccFrameInst6 : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance
local instance ccFrameInst7 : NormedAddCommGroup (COne ℂ (End n)) := inferInstance
local instance ccFrameInst8 : NormedSpace ℝ (COne ℂ (End n)) := inferInstance
local instance ccFrameInst9 : NormedAddCommGroup (HMap ℂ (End n)) := inferInstance
local instance ccFrameInst10 : NormedSpace ℝ (HMap ℂ (End n)) := inferInstance

variable {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J) (hc : ∀ x, Compatible (J x)) {B : ℝ}
  (hstd : ∀ x, B < ‖x‖ → J x=standardJ n) (p q : Phase n) (u : COne ℂ (Phase n))

def completedStructureJet : COne ℂ (End n) :=
  compactPerturbationJet hJ (standardJ n) (compactPerturbation_of_outside_constant _ hstd)
    p (complexSlope (markedSlope p q u)) u

@[simp] lemma completedStructureJet_value (z : ℂ) :
    cValue (completedStructureJet hJ hstd p q u) z = J (markedCurve p q u z) := rfl

def completedFrameJet : COne ℂ (End n) :=
  compactPerturbationJet (compatibleFrame_smooth hJ) ((2:ℝ) • ContinuousLinearMap.id ℝ (Phase n))
    (compactPerturbation_of_outside_constant _ (fun x hx =>
      (congrArg compatibleFrame (hstd x hx)).trans compatibleFrame_standard))
    p (complexSlope (markedSlope p q u)) u

@[simp] lemma completedFrameJet_value (z : ℂ) :
    cValue (completedFrameJet hJ hstd p q u) z = compatibleFrame (J (markedCurve p q u z)) := rfl

def completedInverseJet : COne ℂ (End n) :=
  compactPerturbationJet (compatibleFrame_inverse_smooth hJ hc) ((1/2:ℝ) • ContinuousLinearMap.id ℝ (Phase n))
    (compactPerturbation_of_outside_constant _ (fun x hx =>
      (congrArg (fun A : End n => (compatibleFrame A).inverse) (hstd x hx)).trans compatibleFrame_inverse_standard))
    p (complexSlope (markedSlope p q u)) u

@[simp] lemma completedInverseJet_value (z : ℂ) :
    cValue (completedInverseJet hJ hc hstd p q u) z = (compatibleFrame (J (markedCurve p q u z))).inverse := rfl

variable {K : Set ℂ} (hK : IsCompact K) (he : ∀ z ∉ K, B < ‖markedCurve p q u z‖)
local instance ccFrameInst11 : NormedAddCommGroup (markedModel (E := Phase n) K) := inferInstance
local instance ccFrameInst12 : NormedSpace ℝ (markedModel (E := Phase n) K) := inferInstance
local instance ccFrameInst13 : NormedAddCommGroup (supportedHolder (E := Phase n) K) := inferInstance
local instance ccFrameInst14 : NormedSpace ℝ (supportedHolder (E := Phase n) K) := inferInstance

def completedPrincipal : markedModel (E := Phase n) K →L[ℝ] supportedHolder (E := Phase n) K :=
  markedPrincipal (jetValueCLM _ (completedStructureJet hJ hstd p q u))
    (fun z hz => hstd _ (he z hz))

@[simp] lemma completedPrincipal_value (v : markedModel (E := Phase n) K) (z : ℂ) :
    valueCLM _ (completedPrincipal hJ hstd p q u he v).val z =
      cDeriv v.val z Complex.I-J (markedCurve p q u z) (cDeriv v.val z 1) := rfl

include hc hK in
lemma completedPrincipal_add_compact_fredholm
    (C : markedModel (E := Phase n) K →L[ℝ] supportedHolder (E := Phase n) K)
    (hC : IsCompactOperator C) :
    (completedPrincipal hJ hstd p q u he+C).IsFredholm ∧
      Module.finrank ℝ (completedPrincipal hJ hstd p q u he+C).ker =
        Module.finrank ℝ (supportedHolder (E := Phase n) K ⧸ (completedPrincipal hJ hstd p q u he+C).range) := by
  have hh := framedJetPrincipal_add_compact_fredholm (E := Phase n) hK
    (completedFrameJet hJ hstd p q u) (completedInverseJet hJ hc hstd p q u) 2 (1/2)
    (fun z hz => (congrArg compatibleFrame (hstd _ (he z hz))).trans compatibleFrame_standard)
    (fun z hz => (congrArg (fun A : End n => (compatibleFrame A).inverse)
      (hstd _ (he z hz))).trans compatibleFrame_inverse_standard)
    (fun z v => compatibleFrame_inverse_left (hc _) v)
    (fun z v => compatibleFrame_inverse_right (hc _) v)
    (jetValueCLM _ (completedStructureJet hJ hstd p q u)) (fun z hz => hstd _ (he z hz))
    (fun z v => compatibleFrame_intertwine (hc _) v) C hC
  exact hh


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance markFiniteInst1 : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance markFiniteInst2 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance markFiniteInst3 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance markFiniteInst4 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance markFiniteInst5 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance markFiniteInst6 : NormedSpace ℝ (HMap ℂ E) := inferInstance
variable {K : Set ℂ}
local instance markFiniteInst7 : NormedAddCommGroup (markedModel (E := E) K) := inferInstance
local instance markFiniteInst8 : NormedSpace ℝ (markedModel (E := E) K) := inferInstance
local instance markFiniteInst9 : NormedAddCommGroup (supportedHolder (E := E) K) := inferInstance
local instance markFiniteInst10 : NormedSpace ℝ (supportedHolder (E := E) K) := inferInstance

def supportedFieldAction (B : HMap ℂ (E →L[ℝ] E)) (hB : ∀ z ∉ K, valueCLM _ B z = 0) :
    E →L[ℝ] supportedHolder (E := E) K :=
  ((holderCoefficientAction B).comp constHolderCLM).codRestrict _ (fun v => by
    apply (mem_supportedHolder _ K).mpr
    intro z hz
    change valueCLM _ B z v = 0
    rw [hB z hz,zero_apply])

omit [CompleteSpace E] in
@[simp] lemma supportedFieldAction_value [CompleteSpace E] (B : HMap ℂ (E →L[ℝ] E))
    (hB : ∀ z ∉ K, valueCLM _ B z = 0) (v : E) (z : ℂ) :
    valueCLM _ (supportedFieldAction B hB v).val z = valueCLM _ B z v := rfl

def markedEval (z : ℂ) : markedModel (E := E) K →L[ℝ] E :=
  (jetEval z).comp (markedModel (E := E) K).subtypeL

omit [CompleteSpace E] in
@[simp] lemma markedEval_value [CompleteSpace E] (z : ℂ) (u : markedModel (E := E) K) :
    markedEval (E := E) (K := K) z u = cValue u.val z := rfl

def markedFiniteCorrection (B : HMap ℂ (E →L[ℝ] E)) (hB : ∀ z ∉ K, valueCLM _ B z = 0) :
    markedModel (E := E) K →L[ℝ] supportedHolder (E := E) K :=
  (supportedFieldAction B hB).comp (markedEval (E := E) (K := K) 1)

omit [CompleteSpace E] in
@[simp] lemma markedFiniteCorrection_value [CompleteSpace E] (B : HMap ℂ (E →L[ℝ] E))
    (hB : ∀ z ∉ K, valueCLM _ B z = 0) (u : markedModel (E := E) K) (z : ℂ) :
    valueCLM _ (markedFiniteCorrection B hB u).val z = valueCLM _ B z (cValue u.val 1) := rfl

omit [CompleteSpace E] in
lemma markedFiniteCorrection_isCompact [CompleteSpace E] [FiniteDimensional ℝ E]
    (B : HMap ℂ (E →L[ℝ] E)) (hB : ∀ z ∉ K, valueCLM _ B z = 0) :
    IsCompactOperator (markedFiniteCorrection B hB) := by
  have hc : IsCompactOperator (ContinuousLinearMap.id ℝ E) :=
    (isCompactOperator_id_iff_finiteDimensional (𝕜 := ℝ)).mpr inferInstance
  exact (hc.clm_comp (supportedFieldAction B hB)).comp_clm (markedEval (E := E) (K := K) 1)


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {n : ℕ}
local instance geoLinInst1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance geoLinInst2 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace
local instance geoLinInst3 : NormedAddCommGroup (Phase n →L[ℝ] End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance geoLinInst4 : NormedSpace ℝ (Phase n →L[ℝ] End n) := ContinuousLinearMap.toNormedSpace
local instance geoLinInst5 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance geoLinInst6 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
local instance geoLinInst7 : NormedAddCommGroup (HMap ℂ (Phase n)) := inferInstance
local instance geoLinInst8 : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance
local instance geoLinInst9 : NormedAddCommGroup (HMap ℂ (End n)) := inferInstance
local instance geoLinInst10 : NormedSpace ℝ (HMap ℂ (End n)) := inferInstance

lemma fderiv_standard_outside {J : Phase n → End n} {B : ℝ}
    (hstd : ∀ x, B < ‖x‖ → J x = standardJ n) {x : Phase n} (hx : B < ‖x‖) :
    fderiv ℝ J x = 0 := by
  have he : J =ᶠ[𝓝 x] fun _ => standardJ n := by
    filter_upwards [isOpen_lt continuous_const continuous_norm |>.mem_nhds hx] with y hy
    exact hstd y hy
  rw [he.fderiv_eq]
  exact (hasFDerivAt_const (𝕜 := ℝ) (standardJ n) x).fderiv

def curveZeroOrder (J : Phase n → End n) (f : ℂ → Phase n) (z : ℂ) : End n :=
  (fderiv ℝ J (f z)).flip (fderiv ℝ f z 1)

@[simp] lemma curveZeroOrder_apply (J : Phase n → End n) (f : ℂ → Phase n) (z : ℂ) (v : Phase n) :
    curveZeroOrder J f z v = fderiv ℝ J (f z) v (fderiv ℝ f z 1) := rfl

def curveMarkCoefficient (J : Phase n → End n) (f : ℂ → Phase n) (z : ℂ) : End n :=
  J (f z)-standardJ n + (curveZeroOrder J f z).comp ((ContinuousLinearMap.lsmul ℝ ℂ) z)

@[simp] lemma curveMarkCoefficient_apply (J : Phase n → End n) (f : ℂ → Phase n) (z : ℂ) (v : Phase n) :
    curveMarkCoefficient J f z v = J (f z) v - Complex.I • v +
      fderiv ℝ J (f z) (z • v) (fderiv ℝ f z 1) := rfl

lemma curveZeroOrder_smooth {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J)
    {f : ℂ → Phase n} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (curveZeroOrder J f) := by
  have hDJ := (hJ.fderiv_right (by simp)).comp hf
  have hdF : ContDiff ℝ ∞ (fun z => fderiv ℝ f z 1) :=
    (hf.fderiv_right (by simp)).clm_apply contDiff_const
  let L := (ContinuousLinearMap.flipₗᵢ ℝ (Phase n) (Phase n) (Phase n)).toContinuousLinearEquiv.toContinuousLinearMap
  exact (L.contDiff.comp hDJ).clm_apply hdF

lemma curveMarkCoefficient_smooth {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J)
    {f : ℂ → Phase n} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (curveMarkCoefficient J f) := by
  have hsmul : ContDiff ℝ ∞ (fun z : ℂ => (ContinuousLinearMap.lsmul ℝ ℂ (E := Phase n)) z) :=
    (ContinuousLinearMap.lsmul ℝ ℂ (E := Phase n)).contDiff
  exact ((hJ.comp hf).sub contDiff_const).add ((curveZeroOrder_smooth hJ hf).clm_comp hsmul)

variable {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J) (hc : ∀ x, Compatible (J x))
  {f : ℂ → Phase n} (hf : ContDiff ℝ ∞ f) {B : ℝ}
  (hstd : ∀ x, B < ‖x‖ → J x = standardJ n) {K : Set ℂ} (hK : IsCompact K)
  (hesc : ∀ z ∉ K, B < ‖f z‖)
local instance geoLinInst11 : NormedAddCommGroup (markedModel (E := Phase n) K) := inferInstance
local instance geoLinInst12 : NormedSpace ℝ (markedModel (E := Phase n) K) := inferInstance
local instance geoLinInst13 : NormedAddCommGroup (supportedHolder (E := Phase n) K) := inferInstance
local instance geoLinInst14 : NormedSpace ℝ (supportedHolder (E := Phase n) K) := inferInstance

include hstd hesc in
lemma curveZeroOrder_zero_outside : ∀ z ∉ K, curveZeroOrder J f z = 0 := by
  intro z hz
  apply ContinuousLinearMap.ext
  intro v
  rw [curveZeroOrder_apply,fderiv_standard_outside hstd (hesc z hz)]
  rfl

include hstd hesc in
lemma curveMarkCoefficient_zero_outside : ∀ z ∉ K, curveMarkCoefficient J f z = 0 := by
  intro z hz
  rw [curveMarkCoefficient,hstd _ (hesc z hz),sub_self,zero_add,
    curveZeroOrder_zero_outside hstd hesc z hz,ContinuousLinearMap.zero_comp]

include hstd hK hesc in
lemma curveZeroOrder_compact : HasCompactSupport (curveZeroOrder J f) := by
  apply HasCompactSupport.of_support_subset_isCompact hK
  intro z hz
  by_contra hzK
  exact hz (curveZeroOrder_zero_outside hstd hesc z hzK)

include hstd hK hesc in
lemma curveMarkCoefficient_compact : HasCompactSupport (curveMarkCoefficient J f) := by
  apply HasCompactSupport.of_support_subset_isCompact hK
  intro z hz
  by_contra hzK
  exact hz (curveMarkCoefficient_zero_outside hstd hesc z hzK)

def curveZeroOrderHolder : HMap ℂ (End n) :=
  jetValueCLM _ (ofBoundedCThree (boundedCThree_of_compactSupport (curveZeroOrder_smooth hJ hf)
    (curveZeroOrder_compact hstd hK hesc)))

def curveMarkCoefficientHolder : HMap ℂ (End n) :=
  jetValueCLM _ (ofBoundedCThree (boundedCThree_of_compactSupport (curveMarkCoefficient_smooth hJ hf)
    (curveMarkCoefficient_compact hstd hK hesc)))

@[simp] lemma curveZeroOrderHolder_value (z : ℂ) :
    valueCLM _ (curveZeroOrderHolder hJ hf hstd hK hesc) z = curveZeroOrder J f z := rfl

@[simp] lemma curveMarkCoefficientHolder_value (z : ℂ) :
    valueCLM _ (curveMarkCoefficientHolder hJ hf hstd hK hesc) z = curveMarkCoefficient J f z := rfl

def geometricZeroOrder : markedModel (E := Phase n) K →L[ℝ] supportedHolder (E := Phase n) K :=
  markedZeroOrder (E := Phase n) (curveZeroOrderHolder hJ hf hstd hK hesc)
    (curveZeroOrder_zero_outside hstd hesc)

def geometricMarkCorrection : markedModel (E := Phase n) K →L[ℝ] supportedHolder (E := Phase n) K :=
  markedFiniteCorrection (E := Phase n) (curveMarkCoefficientHolder hJ hf hstd hK hesc)
    (curveMarkCoefficient_zero_outside hstd hesc)

lemma geometricZeroOrder_compact : IsCompactOperator (geometricZeroOrder hJ hf hstd hK hesc) :=
  markedZeroOrder_isCompact_of_compact (E := Phase n) hK _ _

lemma geometricMarkCorrection_compact : IsCompactOperator (geometricMarkCorrection hJ hf hstd hK hesc) :=
  markedFiniteCorrection_isCompact (E := Phase n) _ _

def geometricLinearized : markedModel (E := Phase n) K →L[ℝ] supportedHolder (E := Phase n) K :=
  smoothMarkedPrincipal hK (hJ.comp hf) (fun z hz => hstd _ (hesc z hz)) +
    (-geometricZeroOrder hJ hf hstd hK hesc + geometricMarkCorrection hJ hf hstd hK hesc)

lemma geometricLinearized_value (u : markedModel (E := Phase n) K) (z : ℂ) :
    valueCLM _ (geometricLinearized hJ hf hstd hK hesc u).val z =
      cDeriv u.val z Complex.I - J (f z) (cDeriv u.val z 1) -
        fderiv ℝ J (f z) (cValue u.val z) (fderiv ℝ f z 1) +
       (J (f z) (cValue u.val 1) - Complex.I • cValue u.val 1 +
        fderiv ℝ J (f z) (z • cValue u.val 1) (fderiv ℝ f z 1)) := by
  change (cDeriv u.val z Complex.I-J (f z) (cDeriv u.val z 1)) +
    (-(fderiv ℝ J (f z) (cValue u.val z) (fderiv ℝ f z 1)) +
      (J (f z) (cValue u.val 1)-Complex.I • cValue u.val 1 +
        fderiv ℝ J (f z) (z • cValue u.val 1) (fderiv ℝ f z 1))) = _
  abel

include hc in
lemma geometricLinearized_fredholm : (geometricLinearized hJ hf hstd hK hesc).IsFredholm ∧
    Module.finrank ℝ (geometricLinearized hJ hf hstd hK hesc).ker =
      Module.finrank ℝ (supportedHolder (E := Phase n) K ⧸ (geometricLinearized hJ hf hstd hK hesc).range) := by
  exact smoothMarkedPrincipal_add_compact_fredholm hK (hJ.comp hf) (fun z => hc (f z))
    (fun z hz => hstd _ (hesc z hz)) _
    ((geometricZeroOrder_compact hJ hf hstd hK hesc).neg.add
      (geometricMarkCorrection_compact hJ hf hstd hK hesc))


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance affineEscapeInst1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance affineEscapeInst2 : NormedSpace ℝ (COne ℂ E) := inferInstance

omit [CompleteSpace E] in
lemma exists_escape_radii [CompleteSpace E] (p q : E) (u : COne ℂ E) (ha : markedSlope p q u ≠ 0)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ δ R : ℝ, 0 < δ ∧ 0 < R ∧
      ∀ h : COne ℂ E, ‖h‖ < δ → ∀ z : ℂ, R ≤ ‖z‖ →
        B < ‖z‖*(‖markedSlope p q u‖-‖h‖)-‖p‖-‖u‖-‖h‖ := by
  let δ : ℝ := ‖markedSlope p q u‖/2
  have hδ : 0 < δ := by dsimp [δ]; exact half_pos (norm_pos_iff.mpr ha)
  let R : ℝ := (B+‖p‖+‖u‖+δ+1)/δ
  have hR : 0 < R := by dsimp [R]; positivity
  refine ⟨δ,R,hδ,hR,?_⟩
  intro h hh z hz
  have haδ : δ ≤ ‖markedSlope p q u‖-‖h‖ := by dsimp only [δ] at hh ⊢; linarith
  have hm : R*δ ≤ ‖z‖*(‖markedSlope p q u‖-‖h‖) :=
    mul_le_mul hz haδ hδ.le (norm_nonneg z)
  have he : R*δ = B+‖p‖+‖u‖+δ+1 := div_mul_cancel₀ _ hδ.ne'
  rw [he] at hm
  linarith

lemma exists_uniform_escape (p q : E) (u : COne ℂ E) (ha : markedSlope p q u ≠ 0)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ δ R : ℝ, 0 < δ ∧ 0 < R ∧
      ∀ h : COne ℂ E, ‖h‖ < δ → ∀ z : ℂ, R ≤ ‖z‖ →
        B < ‖markedCurve p q (u+h) z‖ ∧
        ∀ b : ContDiffBump (0:ℂ), B < ‖truncatedCurve b p q u h z‖ := by
  obtain ⟨δ,R,hδ,hR,he⟩ := exists_escape_radii p q u ha hB
  refine ⟨δ,R,hδ,hR,?_⟩
  intro h hh z hz
  exact ⟨(he h hh z hz).trans_le (markedCurve_norm_lower p q u h z),
    fun b => (he h hh z hz).trans_le (truncatedCurve_norm_lower b p q u h z)⟩

variable {F : Type*} [Zero F]

omit [CompleteSpace E] in
lemma compact_coefficient_truncated [CompleteSpace E] {P : E → F} {B : ℝ}
    (hP : ∀ x, B < ‖x‖ → P x = 0) (p q : E) (u : COne ℂ E)
    (b : ContDiffBump (0:ℂ)) {h : COne ℂ E}
    (he : ∀ z : ℂ, b.rIn ≤ ‖z‖ → B < ‖markedCurve p q (u+h) z‖ ∧
      B < ‖truncatedCurve b p q u h z‖) (z : ℂ) :
    P (truncatedCurve b p q u h z) = P (markedCurve p q (u+h) z) := by
  by_cases hz : z ∈ Metric.closedBall 0 b.rIn
  · rw [truncatedCurve_eq_marked b p q u h hz]
  · have hz' : b.rIn ≤ ‖z‖ := by
      simp only [Metric.mem_closedBall,dist_zero_right] at hz
      exact (lt_of_not_ge hz).le
    rw [hP _ (he z hz').1,hP _ (he z hz').2]

omit [CompleteSpace E] in
lemma compact_coefficient_zero_outside [CompleteSpace E] {P : E → F} {B : ℝ}
    (hP : ∀ x, B < ‖x‖ → P x = 0) (p q : E) (u : COne ℂ E)
    (b : ContDiffBump (0:ℂ)) {h : COne ℂ E}
    (he : ∀ z : ℂ, b.rIn ≤ ‖z‖ → B < ‖markedCurve p q (u+h) z‖)
    {z : ℂ} (hz : z ∉ Metric.closedBall 0 b.rIn) :
    P (markedCurve p q (u+h) z) = 0 := by
  apply hP
  apply he
  simp only [Metric.mem_closedBall,dist_zero_right] at hz
  exact (lt_of_not_ge hz).le


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance markedChartInst1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance markedChartInst2 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance markedChartInst3 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance markedChartInst4 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance markedChartInst5 : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance markedChartInst6 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance markedChartInst7 : NormedAddCommGroup (HMap ℂ (E →L[ℝ] E)) := inferInstance
local instance markedChartInst8 : NormedSpace ℝ (HMap ℂ (E →L[ℝ] E)) := inferInstance

local instance markedChartInst13 : NormedAddCommGroup (ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance markedChartInst14 : NormedSpace ℝ (ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedSpace

def markedDX (p q : E) (u h : COne ℂ E) : HMap ℂ E :=
  const _ (markedSlope p q u) - constHolderCLM (jetEval 1 h) + jetDirection 1 (u+h)

omit [CompleteSpace E] in
@[simp] lemma markedDX_value [CompleteSpace E] (p q : E) (u h : COne ℂ E) (z : ℂ) :
    valueCLM _ (markedDX p q u h) z = fderiv ℝ (markedCurve p q (u+h)) z 1 := by
  rw [markedCurve_fderiv,markedSlope_add]
  simp only [add_apply,complexSlope_apply,one_smul]
  rfl

omit [CompleteSpace E] in
lemma markedDX_contDiff [CompleteSpace E] (p q : E) (u : COne ℂ E) :
    ContDiff ℝ ∞ (markedDX p q u) := by
  have hC : ContDiff ℝ ∞ (fun h : COne ℂ E => (constHolderCLM (E := E)) (jetEval 1 h)) :=
    ((constHolderCLM (E := E)).comp (jetEval (E := E) 1)).contDiff
  have hD : ContDiff ℝ ∞ (fun h : COne ℂ E => jetDirection (E := E) 1 (u+h)) :=
    (jetDirection (E := E) 1).contDiff.comp (contDiff_const.add contDiff_id)
  exact (contDiff_const.sub hC).add hD

variable {P : E → E →L[ℝ] E} (hP : BoundedCThree P) (b : ContDiffBump (0:ℂ))

def truncatedCoefficient (p q : E) (u h : COne ℂ E) : HMap ℂ (E →L[ℝ] E) :=
  structureAlong hP p (complexSlope (markedSlope p q u)) (u+truncateShift b h)

omit [CompleteSpace E] in
@[simp] lemma truncatedCoefficient_value [CompleteSpace E] (p q : E) (u h : COne ℂ E) (z : ℂ) :
    valueCLM _ (truncatedCoefficient hP b p q u h) z = P (truncatedCurve b p q u h z) := rfl

omit [CompleteSpace E] in
lemma truncatedCoefficient_contDiff [CompleteSpace E]
    (hc : HasCompactSupport P) (p q : E) (u : COne ℂ E) :
    ContDiff ℝ ∞ (truncatedCoefficient hP b p q u) := by
  have hS : ContDiff ℝ ∞ (structureAlong hP p (complexSlope (markedSlope p q u))) :=
    superpose_contDiff hP (affine_differentiable p _) (norm_nonneg _)
      (affine_fderiv_bound p _) 0 (by simpa only [sub_zero] using hc)
  exact hS.comp (contDiff_const.add (truncateShift (E := E) b).contDiff)

def chartNonlinearity (p q : E) (u h : COne ℂ E) : HMap ℂ E :=
  bilinCLM (X := ℂ) (α := (1:ℝ)/3) (ContinuousLinearMap.apply (E := E) ℝ E).flip
    (truncatedCoefficient hP b p q u h) (markedDX p q u h)

@[simp] lemma chartNonlinearity_value (p q : E) (u h : COne ℂ E) (z : ℂ) :
    valueCLM _ (chartNonlinearity hP b p q u h) z = P (truncatedCurve b p q u h z)
      (fderiv ℝ (markedCurve p q (u+h)) z 1) := by
  rw [chartNonlinearity,bilinCLM_value,truncatedCoefficient_value,markedDX_value]
  rfl

lemma chartNonlinearity_contDiff (hc : HasCompactSupport P) (p q : E) (u : COne ℂ E) :
    ContDiff ℝ ∞ (chartNonlinearity hP b p q u) := by
  exact ((bilinCLM (X := ℂ) (α := (1:ℝ)/3) (ContinuousLinearMap.apply (E := E) ℝ E).flip).contDiff.comp
    (truncatedCoefficient_contDiff hP b hc p q u)).clm_apply (markedDX_contDiff p q u)

local instance markedChartInst9 : NormedAddCommGroup (markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance markedChartInst10 : NormedSpace ℝ (markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance markedChartInst11 : NormedAddCommGroup (supportedHolder (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance markedChartInst12 : NormedSpace ℝ (supportedHolder (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance

def markedChart (p q : E) (u h : markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) :
    supportedHolder (E := E) (Metric.closedBall (0:ℂ) b.rOut) :=
  (markedCR (E := E) (K := Metric.closedBall (0:ℂ) b.rOut)) (u+h) - supportedSourceCutoff b (chartNonlinearity hP b p q u.val h.val)

lemma markedChart_contDiff (hc : HasCompactSupport P) (p q : E)
    (u : markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) :
    ContDiff ℝ ∞ (markedChart hP b p q u) := by
  have hL : ContDiff ℝ ∞ (fun h : markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut) => (markedCR (E := E) (K := Metric.closedBall (0:ℂ) b.rOut)) (u+h)) :=
    (markedCR (E := E) (K := Metric.closedBall (0:ℂ) b.rOut)).contDiff.comp (contDiff_const.add contDiff_id)
  have hN := (chartNonlinearity_contDiff hP b hc p q u.val).comp
    (markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)).subtypeL.contDiff
  exact hL.sub ((supportedSourceCutoff (E := E) b).contDiff.comp hN)

lemma markedChart_value (p q : E)
    (u h : markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) (z : ℂ) :
    valueCLM _ (markedChart hP b p q u h).val z =
      valueCLM _ (standardJetCR (u.val+h.val)) z - b z •
      P (truncatedCurve b p q u.val h.val z) (fderiv ℝ (markedCurve p q (u.val+h.val)) z 1) := by
  exact congrArg (fun w : E => valueCLM _ (standardJetCR (u.val+h.val)) z - b z • w)
    (chartNonlinearity_value hP b p q u.val h.val z)

omit [CompleteSpace E] in
lemma cutoff_action_eq [CompleteSpace E] {A₀ A₁ : E →L[ℝ] E} {z : ℂ} (hA : A₀ = A₁)
    (hz0 : z ∉ Metric.closedBall 0 b.rIn → A₁ = 0) (v : E) :
    b z • A₀ v = A₁ v := by
  subst A₀
  by_cases hz : z ∈ Metric.closedBall 0 b.rIn
  · calc
      b z • A₁ v = (1:ℝ) • A₁ v := congrArg (fun c : ℝ => c • A₁ v) (b.one_of_mem_closedBall hz)
      _ = A₁ v := one_smul ℝ _
  · have ha : A₁ v = 0 := congrArg (fun A : E →L[ℝ] E => A v) (hz0 hz)
    calc
      b z • A₁ v = b z • (0:E) := congrArg (fun w : E => b z • w) ha
      _ = 0 := smul_zero _
      _ = A₁ v := ha.symm

lemma markedChart_actual_value {B : ℝ} (hPB : ∀ x, B < ‖x‖ → P x = 0) (p q : E)
    (u h : markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut))
    (he : ∀ z : ℂ, b.rIn ≤ ‖z‖ → B < ‖markedCurve p q (u.val+h.val) z‖ ∧
      B < ‖truncatedCurve b p q u.val h.val z‖) (z : ℂ) :
    valueCLM _ (markedChart hP b p q u h).val z =
      fderiv ℝ (markedCurve p q (u.val+h.val)) z Complex.I -
      (Complex.I • fderiv ℝ (markedCurve p q (u.val+h.val)) z 1 +
        P (markedCurve p q (u.val+h.val) z) (fderiv ℝ (markedCurve p q (u.val+h.val)) z 1)) := by
  have hPz : P (truncatedCurve b p q u.val h.val z) =
      P (markedCurve p q (u.val+h.val) z) :=
    compact_coefficient_truncated hPB p q u.val b he z
  have hS := markedCurve_standardResidual p q (u.val+h.val) z
  have hN := cutoff_action_eq b hPz
    (compact_coefficient_zero_outside hPB p q u.val b (fun w hw => (he w hw).1))
    (fderiv ℝ (markedCurve p q (u.val+h.val)) z 1)
  calc
    _ = valueCLM _ (standardJetCR (u.val+h.val)) z - b z •
        P (truncatedCurve b p q u.val h.val z) (fderiv ℝ (markedCurve p q (u.val+h.val)) z 1) :=
      markedChart_value hP b p q u h z
    _ = (fderiv ℝ (markedCurve p q (u.val+h.val)) z Complex.I -
        Complex.I • fderiv ℝ (markedCurve p q (u.val+h.val)) z 1) -
        P (markedCurve p q (u.val+h.val) z) (fderiv ℝ (markedCurve p q (u.val+h.val)) z 1) :=
      congrArg₂ (· - ·) hS.symm hN
    _ = _ := sub_sub _ _ _



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
