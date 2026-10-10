import Mathlib
import OAI.Geometry.BallPacking.Holder.MarkedFrame

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion

section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance scsInst1 : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance scsInst2 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance scsInst3 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance scsInst4 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance scsInst5 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance scsInst6 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance scsInst7 : NormedAddCommGroup (HMap ℂ (E →L[ℝ] E)) := inferInstance
local instance scsInst8 : NormedSpace ℝ (HMap ℂ (E →L[ℝ] E)) := inferInstance

def jetDirectional (z : ℂ) : COne ℂ E →L[ℝ] HMap ℂ E :=
  (mapCLM _ (ContinuousLinearMap.apply ℝ E z)).comp (jetDerivCLM _)

omit [CompleteSpace E] in
@[simp] lemma jetDirectional_value (z : ℂ) (v : COne ℂ E) (w : ℂ) :
    valueCLM _ (jetDirectional z v) w=cDeriv v w z := rfl

omit [CompleteSpace E] in
lemma holderCoefficientAction_norm_le (A : HMap ℂ (E →L[ℝ] E)) (v : HMap ℂ E) :
    ‖holderCoefficientAction A v‖≤
      ‖bilinCLM (X := ℂ) (α := (1:ℝ)/3) (ContinuousLinearMap.apply (E := E) ℝ E).flip‖*‖A‖*‖v‖ :=
  (bilinCLM (X := ℂ) (α := (1:ℝ)/3) (ContinuousLinearMap.apply (E := E) ℝ E).flip).le_opNorm₂ A v

lemma compact_zeroMarked_schauder {K : Set ℂ} (hK : IsCompact K) (v : COne ℂ E)
    (hv : cValue v 0=0) (hs : standardJetCR v∈supportedHolder K) :
    ‖v‖≤‖standardHolderInverse (E := E) hK‖*‖standardJetCR v‖ := by
  let g : supportedHolder (E := E) K := ⟨standardJetCR v,hs⟩
  have he : standardHolderInverse hK g=v := standardJetCR_injective_zeroMarked
    (standardHolderInverse_zero hK g) hv (standardHolderInverse_residual hK g)
  have hh := (standardHolderInverse hK).le_opNorm g
  rw [he] at hh
  exact hh

lemma scalar_absorption {D B N a v f : ℝ} (hD : 0≤D) (hB : 0≤B) (hN : 0≤N)
    (hf : 0≤f) (hv : 0≤v) (ha : a≤(2*(D*B*N+1))⁻¹)
    (hb : v≤D*((B*a*N)*v+f)) : v≤(2*D+1)*f := by
  have ht : D*B*N*(2*(D*B*N+1))⁻¹≤(1:ℝ)/2 := by
    rw [←div_eq_mul_inv]
    apply (div_le_iff₀ (by positivity : 0<2*(D*B*N+1))).mpr
    nlinarith
  have hs : D*B*N*a≤(1:ℝ)/2 :=
    (mul_le_mul_of_nonneg_left ha (by positivity)).trans ht
  have hh := mul_le_mul_of_nonneg_right hs hv
  nlinarith

lemma small_coefficient_schauder {K : Set ℂ} (hK : IsCompact K) :
    ∃ ε C : ℝ,0<ε ∧ 0<C ∧ ∀ (v : COne ℂ E),cValue v 0=0 →
      standardJetCR v∈supportedHolder K →∀ (A : HMap ℂ (E →L[ℝ] E)),‖A‖≤ε →
      ∀ f : HMap ℂ E,standardJetCR v=holderCoefficientAction A (jetDirectional 1 v)+f →
        ‖v‖≤C*‖f‖ := by
  let D := ‖standardHolderInverse (E := E) hK‖
  let B := ‖bilinCLM (X := ℂ) (α := (1:ℝ)/3) (ContinuousLinearMap.apply (E := E) ℝ E).flip‖
  let N := ‖jetDirectional (E := E) 1‖
  have hD : 0≤D := norm_nonneg (standardHolderInverse (E := E) hK)
  have hB : 0≤B := norm_nonneg (bilinCLM (X := ℂ) (α := (1:ℝ)/3)
    (ContinuousLinearMap.apply (E := E) ℝ E).flip)
  have hN : 0≤N := norm_nonneg (jetDirectional (E := E) 1)
  have hpos : 0<(2*(D*B*N+1))⁻¹ := by positivity
  refine ⟨(2*(D*B*N+1))⁻¹,2*D+1,hpos,by positivity,?_⟩
  intro v hv hs A hA f he
  have hi := compact_zeroMarked_schauder hK v hv hs
  have hp := holderCoefficientAction_norm_le A (jetDirectional 1 v)
  have hd := (jetDirectional (E := E) 1).le_opNorm v
  have hm := mul_le_mul_of_nonneg_left hd (by positivity : 0≤B*‖A‖)
  have hb : ‖holderCoefficientAction A (jetDirectional 1 v)‖≤(B*‖A‖*N)*‖v‖ :=
    hp.trans (hm.trans_eq (by ring))
  have hres : ‖standardJetCR v‖≤(B*‖A‖*N)*‖v‖+‖f‖ := by
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add hb (le_refl _))
  exact scalar_absorption hD hB hN (norm_nonneg f) (norm_nonneg v) hA
    (hi.trans (mul_le_mul_of_nonneg_left hres hD))


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance csInst1 : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance csInst2 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance csInst9 : NormedAddCommGroup (ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance csInst10 : NormedSpace ℝ (ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance csInst11 : NormedAddCommGroup (HMap ℂ (ℂ →L[ℝ] E)) := inferInstance
local instance csInst12 : NormedSpace ℝ (HMap ℂ (ℂ →L[ℝ] E)) := inferInstance
local instance csInst3 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance csInst4 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance csInst5 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance csInst6 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance csInst7 : NormedAddCommGroup (HMap ℂ (E →L[ℝ] E)) := inferInstance
local instance csInst8 : NormedSpace ℝ (HMap ℂ (E →L[ℝ] E)) := inferInstance

omit [CompleteSpace E] in
lemma standardJetCR_sub_explicit (v w : COne ℂ E) :
    standardJetCR (v-w)=standardJetCR v-standardJetCR w := by
  apply value_ext
  intro z
  rw [(valueCLM ((1:ℝ)/3)).map_sub]
  simp only [BoundedContinuousFunction.sub_apply,standardJetCR_value]
  change ((cDeriv v z Complex.I-cDeriv w z Complex.I)-
      Complex.I • (cDeriv v z 1-cDeriv w z 1))=
      (cDeriv v z Complex.I-Complex.I • cDeriv v z 1)-
      (cDeriv w z Complex.I-Complex.I • cDeriv w z 1)
  rw [smul_sub]
  abel

omit [CompleteSpace E] in
lemma clm_principal_sub_algebra (A B : E →L[ℝ] E) (x y f g : E) :
    (A x+f)-(B y+g)=A (x-y)+((A-B) y+(f-g)) := by
  simp only [map_sub,sub_apply]
  abel

omit [CompleteSpace E] in
lemma principal_difference_identity (v w : COne ℂ E) (A B : HMap ℂ (E →L[ℝ] E))
    (f g : HMap ℂ E)
    (hv : standardJetCR v=holderCoefficientAction A (jetDirectional 1 v)+f)
    (hw : standardJetCR w=holderCoefficientAction B (jetDirectional 1 w)+g) :
    standardJetCR (v-w)=holderCoefficientAction A (jetDirectional 1 (v-w))+
      (holderCoefficientAction (A-B) (jetDirectional 1 w)+(f-g)) := by
  rw [standardJetCR_sub_explicit,hv,hw]
  apply value_ext
  intro z
  change (valueCLM _ A z (cDeriv v z 1)+valueCLM _ f z)-
      (valueCLM _ B z (cDeriv w z 1)+valueCLM _ g z)=
      valueCLM _ A z (cDeriv v z 1-cDeriv w z 1)+
        ((valueCLM _ A z-valueCLM _ B z) (cDeriv w z 1)+(valueCLM _ f z-valueCLM _ g z))
  exact clm_principal_sub_algebra (valueCLM _ A z) (valueCLM _ B z)
    (cDeriv v z 1) (cDeriv w z 1) (valueCLM _ f z) (valueCLM _ g z)

omit [CompleteSpace E] in
lemma holderCoefficientAction_jet_norm_le (A : HMap ℂ (E →L[ℝ] E)) (w : COne ℂ E) :
    ‖holderCoefficientAction A (jetDirectional 1 w)‖≤
      (‖bilinCLM (X := ℂ) (α := (1:ℝ)/3) (ContinuousLinearMap.apply (E := E) ℝ E).flip‖*
      ‖jetDirectional (E := E) 1‖)*‖A‖*‖w‖ := by
  have hp := holderCoefficientAction_norm_le A (jetDirectional 1 w)
  have hd := (jetDirectional (E := E) 1).le_opNorm w
  exact hp.trans ((mul_le_mul_of_nonneg_left hd (by positivity)).trans_eq (by ring))

omit [CompleteSpace E] in
lemma zeroMarked_sub (v w : COne ℂ E) (hv : cValue v 0=0) (hw : cValue w 0=0) :
    cValue (v-w) 0=0 := by
  change cValue v 0-cValue w 0=0
  rw [hv,hw,sub_self]

omit [CompleteSpace E] in
lemma jet_residual_sub_supported {K : Set ℂ} (v w : COne ℂ E)
    (hv : standardJetCR v∈supportedHolder K) (hw : standardJetCR w∈supportedHolder K) :
    standardJetCR (v-w)∈supportedHolder K := by
  rw [standardJetCR_sub_explicit]
  exact (supportedHolder (E := E) K).sub_mem hv hw

lemma small_coefficient_difference_estimate {K : Set ℂ} (hK : IsCompact K) :
    ∃ ε C D : ℝ,0<ε ∧ 0<C ∧ 0≤D ∧
    ∀ (v w : COne ℂ E),cValue v 0=0 →cValue w 0=0 →
      standardJetCR v∈supportedHolder K →standardJetCR w∈supportedHolder K →
    ∀ (A B : HMap ℂ (E →L[ℝ] E)),‖A‖≤ε →‖B‖≤ε →
    ∀ (f g : HMap ℂ E),
      standardJetCR v=holderCoefficientAction A (jetDirectional 1 v)+f →
      standardJetCR w=holderCoefficientAction B (jetDirectional 1 w)+g →
      ‖v‖≤C*‖f‖ ∧ ‖v-w‖≤C*(D*‖A-B‖*‖w‖+‖f-g‖) := by
  obtain ⟨ε,C,hε,hC,he⟩ := small_coefficient_schauder (E := E) hK
  let D := ‖bilinCLM (X := ℂ) (α := (1:ℝ)/3) (ContinuousLinearMap.apply (E := E) ℝ E).flip‖*
    ‖jetDirectional (E := E) 1‖
  have hD : 0≤D := by dsimp [D]; positivity
  refine ⟨ε,C,D,hε,hC,hD,?_⟩
  intro v w hv hw hvs hws A B hA hB f g hve hwe
  refine ⟨he v hv hvs A hA f hve,?_⟩
  have hest := he (v-w) (zeroMarked_sub v w hv hw) (jet_residual_sub_supported v w hvs hws)
    A hA _ (principal_difference_identity v w A B f g hve hwe)
  have hp' : ‖holderCoefficientAction (A-B) (jetDirectional 1 w)‖≤D*‖A-B‖*‖w‖ :=
    holderCoefficientAction_jet_norm_le (A-B) w
  exact hest.trans (mul_le_mul_of_nonneg_left
    ((norm_add_le _ _).trans (add_le_add hp' (le_refl _))) hC.le)

lemma cauchySeq_of_pair_distance_bound {X Y Z : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] [PseudoMetricSpace Z] {u : ℕ →X} {a : ℕ →Y} {b : ℕ →Z}
    {P Q : ℝ} (hP : 0≤P) (hQ : 0≤Q) (ha : CauchySeq a) (hb : CauchySeq b)
    (hu : ∀ i j,dist (u i) (u j)≤P*dist (a i) (a j)+Q*dist (b i) (b j)) :
    CauchySeq u := by
  rw [Metric.cauchySeq_iff] at ha hb ⊢
  intro ε hε
  have hp : 0<P+Q+1 := by linarith
  obtain ⟨N,hN⟩ := ha (ε/(P+Q+1)) (div_pos hε hp)
  obtain ⟨M,hM⟩ := hb (ε/(P+Q+1)) (div_pos hε hp)
  refine ⟨max N M,fun i hi j hj => ?_⟩
  have h1 := hN i (le_trans (le_max_left _ _) hi) j (le_trans (le_max_left _ _) hj)
  have h2 := hM i (le_trans (le_max_right _ _) hi) j (le_trans (le_max_right _ _) hj)
  have hh := add_le_add (mul_le_mul_of_nonneg_left h1.le hP) (mul_le_mul_of_nonneg_left h2.le hQ)
  have he : P*(ε/(P+Q+1))+Q*(ε/(P+Q+1))<ε := by
    have hδ := div_pos hε hp
    have hid : (P+Q+1)*(ε/(P+Q+1))=ε := mul_div_cancel₀ ε (ne_of_gt hp)
    nlinarith
  exact (hu i j).trans_lt (hh.trans_lt he)

theorem small_coefficient_cauchy {K : Set ℂ} (hK : IsCompact K) :
    ∃ ε : ℝ,0<ε ∧ ∀ (v : ℕ → COne ℂ E) (A : ℕ → HMap ℂ (E →L[ℝ] E))
      (f : ℕ → HMap ℂ E),
      (∀ i,cValue (v i) 0=0) →(∀ i,standardJetCR (v i)∈supportedHolder K) →
      (∀ i,‖A i‖≤ε) →
      (∀ i,standardJetCR (v i)=holderCoefficientAction (A i) (jetDirectional 1 (v i))+f i) →
      CauchySeq A → CauchySeq f → CauchySeq v := by
  obtain ⟨ε,C,D,hε,hC,hD,he⟩ := small_coefficient_difference_estimate (E := E) hK
  refine ⟨ε,hε,?_⟩
  intro v A f hv hs hA hres hAc hfc
  obtain ⟨M,hM,hMf'⟩ := hfc.isBounded_range.exists_pos_norm_le
  have hMf : ∀ i,‖f i‖≤M := fun i => hMf' (f i) ⟨i,rfl⟩
  have hbound : ∀ j,‖v j‖≤C*M := fun j =>
    ((he (v j) (v j) (hv j) (hv j) (hs j) (hs j) (A j) (A j) (hA j) (hA j)
      (f j) (f j) (hres j) (hres j)).1).trans (mul_le_mul_of_nonneg_left (hMf j) hC.le)
  apply cauchySeq_of_pair_distance_bound (P := C*D*(C*M)) (Q := C)
    (by positivity) hC.le hAc hfc
  intro i j
  simp only [dist_eq_norm]
  have hh := (he (v i) (v j) (hv i) (hv j) (hs i) (hs j) (A i) (A j) (hA i) (hA j)
    (f i) (f j) (hres i) (hres j)).2
  have hb := mul_le_mul_of_nonneg_left (hbound j) (by positivity : 0≤D*‖A i-A j‖)
  exact hh.trans ((mul_le_mul_of_nonneg_left (add_le_add hb (le_refl _)) hC.le).trans_eq (by ring))


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance ccInst1 : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance ccInst2 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance ccInst3 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance ccInst4 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance ccInst5 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance ccInst6 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance ccInst7 : NormedAddCommGroup (HMap ℂ (E →L[ℝ] E)) := inferInstance
local instance ccInst8 : NormedSpace ℝ (HMap ℂ (E →L[ℝ] E)) := inferInstance

variable (b : ContDiffBump (0:ℂ)) {u : ℂ → E} (hu : ContDiff ℝ ∞ u)

def cutoffCurveJet : COne ℂ E :=
  ofBoundedCThree (boundedCThree_of_compactSupport (b.contDiff.smul hu) b.hasCompactSupport.smul_right)

omit [CompleteSpace E] in
@[simp] lemma cutoffCurveJet_value (z : ℂ) : cValue (cutoffCurveJet b hu) z=b z • u z := rfl

omit [CompleteSpace E] in
lemma cutoffCurveJet_deriv (z h : ℂ) :
    cDeriv (cutoffCurveJet b hu) z h=
      (fderiv ℝ b z h) • u z+b z • fderiv ℝ u z h := by
  rw [←c_fderiv]
  change fderiv ℝ (fun z => b z • u z) z h=_
  rw [fderiv_fun_smul (b.contDiff.differentiable (by simp : (∞ : WithTop ℕ∞) ≠ 0) z) (hu.differentiable (by simp : (∞ : WithTop ℕ∞) ≠ 0) z)]
  simp only [add_apply,smul_apply,ContinuousLinearMap.smulRight_apply]
  exact add_comm _ _

omit [CompleteSpace E] in
lemma cutoffCurveJet_zero (h0 : u 0=0) : cValue (cutoffCurveJet b hu) 0=0 := by
  rw [cutoffCurveJet_value,h0,smul_zero]

omit [CompleteSpace E] in
lemma cutoffCurveJet_supported : standardJetCR (cutoffCurveJet b hu)∈
    supportedHolder (Metric.closedBall (0:ℂ) b.rOut) := by
  apply (mem_supportedHolder _ _).mpr
  intro z hz
  have hb : z∉tsupport b := by
    rw [b.tsupport_eq]
    exact hz
  have hb0 := image_eq_zero_of_notMem_tsupport hb
  have hbd := fderiv_of_notMem_tsupport ℝ hb
  rw [standardJetCR_value]
  change cDeriv (cutoffCurveJet b hu) z Complex.I-Complex.I • cDeriv (cutoffCurveJet b hu) z 1=0
  rw [cutoffCurveJet_deriv,cutoffCurveJet_deriv,hbd,hb0]
  simp

omit [CompleteSpace E] in
lemma cutoffCurveJet_CR {A : ℂ → E →L[ℝ] E}
    (hcr : ∀ z,b z≠0 → fderiv ℝ u z Complex.I-Complex.I • fderiv ℝ u z 1=A z (fderiv ℝ u z 1))
    (ac : HMap ℂ (E →L[ℝ] E)) (hac : ∀ z,b z≠0 → valueCLM _ ac z=A z)
    (f : HMap ℂ E) (hf : ∀ z,valueCLM _ f z=
      (fderiv ℝ b z Complex.I) • u z-Complex.I • ((fderiv ℝ b z 1) • u z)-
        valueCLM _ ac z ((fderiv ℝ b z 1) • u z)) :
    standardJetCR (cutoffCurveJet b hu)=
      holderCoefficientAction ac (jetDirectional 1 (cutoffCurveJet b hu))+f := by
  apply value_ext
  intro z
  rw [standardJetCR_value]
  change cDeriv (cutoffCurveJet b hu) z Complex.I-Complex.I • cDeriv (cutoffCurveJet b hu) z 1=
    valueCLM _ ac z (cDeriv (cutoffCurveJet b hu) z 1)+valueCLM _ f z
  rw [cutoffCurveJet_deriv,cutoffCurveJet_deriv,hf]
  have he : b z • (fderiv ℝ u z Complex.I-Complex.I • fderiv ℝ u z 1)=
      valueCLM _ ac z (b z • fderiv ℝ u z 1) := by
    by_cases hb : b z=0
    · simp [hb]
    · rw [hac z hb,hcr z hb,map_smul]
  rw [map_add]
  simp only [smul_add,smul_sub] at *
  rw [smul_comm Complex.I (b z)]
  rw [←he]
  abel

lemma small_value_elliptic_estimate {K : Set ℂ} (hK : IsCompact K)
    {L M η : ℝ} (hL : 0≤L) (hM : 0≤M) (hη : 0<η) :
    ∃ δ : ℝ,0<δ ∧ ∀ (v : COne ℂ E),cValue v 0=0 →
      standardJetCR v∈supportedHolder K → ∀ (A : HMap ℂ (E →L[ℝ] E)) (f : HMap ℂ E),
      (∀ z,‖valueCLM _ A z‖≤δ) → (∀ x y,‖valueCLM _ A x-valueCLM _ A y‖≤L*dist x y) →
      (∀ z,‖valueCLM _ f z‖≤δ) → (∀ x y,‖valueCLM _ f x-valueCLM _ f y‖≤M*dist x y) →
      standardJetCR v=holderCoefficientAction A (jetDirectional 1 v)+f → ‖v‖<η := by
  obtain ⟨ε,C,hε,hC,hest⟩ := small_coefficient_schauder (E := E) hK
  obtain ⟨d,hd,hda⟩ := holder_small_of_small_value (E := E →L[ℝ] E) (X := ℂ) hL hε
  obtain ⟨e,he,hef⟩ := holder_small_of_small_value (E := E) (X := ℂ) hM (div_pos hη hC)
  refine ⟨min d e,lt_min hd he,?_⟩
  intro v hv hs A f hA hAL hf hfL hres
  have hAn : ‖A‖<ε := hda A (fun z => (hA z).trans (min_le_left _ _)) hAL
  have hfn : ‖f‖<η/C := hef f (fun z => (hf z).trans (min_le_right _ _)) hfL
  have hh := hest v hv hs A hAn.le f hres
  have ht : C*‖f‖<η := by
    have h := (lt_div_iff₀ hC).mp hfn
    simpa only [mul_comm] using h
  exact hh.trans_lt ht


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {X E F : Type*} [MetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def ofBoundedLipschitz (f : X → E) (hf : Continuous f) (M L : ℝ)
    (hM : 0≤M) (hL : 0≤L) (hb : ∀ x,‖f x‖≤M)
    (hl : ∀ x y,‖f x-f y‖≤L*dist x y) : HMap X E :=
  ofBound f hf M (2*M+L) hb (by positivity) (by
    apply third_interpolation hM hL (by positivity) (show (0:ℝ)<1 by norm_num) hb hl
    · simp only [Real.one_rpow,mul_one]; linarith
    · simp only [Real.one_rpow,mul_one]; linarith)

@[simp] lemma ofBoundedLipschitz_value (f : X → E) (hf : Continuous f) (M L : ℝ)
    (hM : 0≤M) (hL : 0≤L) (hb : ∀ x,‖f x‖≤M)
    (hl : ∀ x y,‖f x-f y‖≤L*dist x y) (x : X) :
    valueCLM _ (ofBoundedLipschitz f hf M L hM hL hb hl) x=f x := rfl

lemma clm_pair_difference (A B : E →L[ℝ] F) (u v : E) :
    ‖A u-B v‖≤‖A‖*‖u-v‖+‖A-B‖*‖v‖ := by
  have he : A u-B v=A (u-v)+(A-B) v := by simp only [map_sub,sub_apply]; abel
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (A.le_opNorm _) ((A-B).le_opNorm _))

lemma clm_pair_bounds {A : X → E →L[ℝ] F} {u : X → E} {B C L M : ℝ}
    (hB : 0≤B) (_hC : 0≤C) (hL : 0≤L) (_hM : 0≤M)
    (hA : ∀ z,‖A z‖≤B) (hu : ∀ z,‖u z‖≤C)
    (hAL : ∀ x y,‖A x-A y‖≤L*dist x y)
    (huL : ∀ x y,‖u x-u y‖≤M*dist x y) :
    (∀ z,‖A z (u z)‖≤B*C) ∧
    (∀ x y,‖A x (u x)-A y (u y)‖≤(B*M+L*C)*dist x y) := by
  constructor
  · intro z
    exact ((A z).le_opNorm _).trans (mul_le_mul (hA z) (hu z) (norm_nonneg _) hB)
  · intro x y
    apply (clm_pair_difference _ _ _ _).trans
    have h1 := mul_le_mul (hA x) (huL x y) (norm_nonneg _) hB
    have h2 := mul_le_mul (hAL x y) (hu y) (norm_nonneg _) (by positivity : 0≤L*dist x y)
    exact (add_le_add h1 h2).trans_eq (by ring)

local instance bcpInst1 : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance bcpInst2 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace

lemma cutoff_forcing_bounds {u : X → E} {A C D : X → E →L[ℝ] E}
    {δ H L B : ℝ} (hδ : 0≤δ) (hδ1 : δ≤1) (hH : 0≤H) (hL : 0≤L) (hB : 0≤B)
    (hu : ∀ z,‖u z‖≤δ) (huL : ∀ x y,‖u x-u y‖≤H*dist x y)
    (hA : ∀ z,‖A z‖≤L*δ) (hAL : ∀ x y,‖A x-A y‖≤(L*H)*dist x y)
    (hC : ∀ z,‖C z‖≤B) (hCL : ∀ x y,‖C x-C y‖≤B*dist x y)
    (hD : ∀ z,‖D z‖≤B) (hDL : ∀ x y,‖D x-D y‖≤B*dist x y) :
    (∀ z,‖C z (u z)-A z (D z (u z))‖≤((1+L)*B)*δ) ∧
    (∀ x y,‖(C x (u x)-A x (D x (u x)))-(C y (u y)-A y (D y (u y)))‖≤
      (B*(H+1)+L*(B*(H+1))+L*H*B)*dist x y) := by
  have hHL : 0≤B*(H+1) := by positivity
  have hbδ : B*δ≤B := by nlinarith
  have hstep : B*H+B*δ≤B*(H+1) := by nlinarith
  obtain ⟨hc,hcl⟩ := clm_pair_bounds hB hδ hB hH hC hu hCL huL
  obtain ⟨hd,hdl⟩ := clm_pair_bounds hB hδ hB hH hD hu hDL huL
  have hAu : ∀ z,‖A z‖≤L := fun z => (hA z).trans (by nlinarith)
  have hDu : ∀ z,‖D z (u z)‖≤B := fun z => (hd z).trans hbδ
  have hDul : ∀ x y,‖D x (u x)-D y (u y)‖≤B*(H+1)*dist x y :=
    fun x y => (hdl x y).trans (mul_le_mul_of_nonneg_right hstep (dist_nonneg))
  obtain ⟨ _,hal⟩ := clm_pair_bounds hL hB (mul_nonneg hL hH) hHL hAu hDu hAL hDul
  refine ⟨?_,?_⟩
  · intro z
    have hh : ‖A z (D z (u z))‖≤L*(B*δ) :=
      ((A z).le_opNorm _).trans (mul_le_mul (hAu z) (hd z) (norm_nonneg _) hL)
    exact (norm_sub_le _ _).trans ((add_le_add (hc z) hh).trans_eq (by ring))
  · intro x y
    have he : (C x (u x)-A x (D x (u x)))-(C y (u y)-A y (D y (u y)))=
        (C x (u x)-C y (u y))-(A x (D x (u x))-A y (D y (u y))) := by abel
    rw [he]
    have hc' := (hcl x y).trans (mul_le_mul_of_nonneg_right hstep (dist_nonneg))
    exact (norm_sub_le _ _).trans ((add_le_add hc' (hal x y)).trans_eq (by ring))


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance ctInst1 : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance ctInst2 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
variable (b : ContDiffBump (0:ℂ))

def cutoffTransport (h z : ℂ) : E →L[ℝ] E :=
  (fderiv ℝ b z h) • ContinuousLinearMap.id ℝ E

def cutoffCommute (z : ℂ) : E →L[ℝ] E :=
  cutoffTransport b Complex.I z-(ContinuousLinearMap.lsmul ℝ ℂ (E := E) Complex.I).comp (cutoffTransport b 1 z)

omit [CompleteSpace E] in
@[simp] lemma cutoffTransport_apply (h z : ℂ) (v : E) : cutoffTransport b h z v=(fderiv ℝ b z h) • v := rfl
omit [CompleteSpace E] in
@[simp] lemma cutoffCommute_apply (z : ℂ) (v : E) :
    cutoffCommute b z v=(fderiv ℝ b z Complex.I) • v-Complex.I • ((fderiv ℝ b z 1) • v) := rfl

omit [CompleteSpace E] in
lemma cutoffTransport_smooth (h : ℂ) : ContDiff ℝ ∞ (cutoffTransport (E := E) b h) := by
  exact ((b.contDiff.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1≤∞)).clm_apply contDiff_const).smul contDiff_const

omit [CompleteSpace E] in
lemma cutoffTransport_compact (h : ℂ) : HasCompactSupport (cutoffTransport (E := E) b h) :=
  (b.hasCompactSupport.fderiv_apply ℝ h).smul_right

omit [CompleteSpace E] in
lemma cutoffCommute_smooth : ContDiff ℝ ∞ (cutoffCommute (E := E) b) :=
  (cutoffTransport_smooth b Complex.I).sub (contDiff_const.clm_comp (cutoffTransport_smooth b 1))

omit [CompleteSpace E] in
lemma cutoffCommute_compact : HasCompactSupport (cutoffCommute (E := E) b) := by
  apply HasCompactSupport.of_support_subset_isCompact b.hasCompactSupport
  intro z hz
  by_contra hn
  apply hz
  have hd := fderiv_of_notMem_tsupport ℝ hn
  simp only [cutoffCommute,cutoffTransport,hd,zero_apply,zero_smul,
    ContinuousLinearMap.comp_zero,sub_zero]

omit [CompleteSpace E] in
lemma cutoff_transport_bounds : ∃ B : ℝ,0<B ∧
    (∀ z,‖cutoffTransport (E := E) b 1 z‖≤B) ∧
    (∀ x y,‖cutoffTransport (E := E) b 1 x-cutoffTransport b 1 y‖≤B*dist x y) ∧
    (∀ z,‖cutoffCommute (E := E) b z‖≤B) ∧
    (∀ x y,‖cutoffCommute (E := E) b x-cutoffCommute b y‖≤B*dist x y) := by
  have hd := boundedCThree_of_compactSupport (cutoffTransport_smooth (E := E) b 1) (cutoffTransport_compact b 1)
  have hc := boundedCThree_of_compactSupport (cutoffCommute_smooth (E := E) b) (cutoffCommute_compact b)
  let B := hd.bound+hc.bound+1
  have hB : 0<B := by dsimp [B]; linarith [hd.bound_nonneg,hc.bound_nonneg]
  have hdb : hd.bound≤B := by dsimp [B]; linarith [hc.bound_nonneg]
  have hcb : hc.bound≤B := by dsimp [B]; linarith [hd.bound_nonneg]
  refine ⟨B,hB,fun z => (hd.norm_le z).trans hdb,?_,fun z => (hc.norm_le z).trans hcb,?_⟩
  · intro x y
    exact (hd.norm_sub_le x y).trans (by rw [dist_eq_norm]; exact mul_le_mul_of_nonneg_right hdb (norm_nonneg _))
  · intro x y
    exact (hc.norm_sub_le x y).trans (by rw [dist_eq_norm]; exact mul_le_mul_of_nonneg_right hcb (norm_nonneg _))


end
open scoped Topology BoundedContinuousFunction
open Set Filter
variable {X E : Type*} [MetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance uhcInst1 : NormedAddCommGroup (HMap X E) := inferInstance
local instance uhcInst2 : NormedSpace ℝ (HMap X E) := inferInstance

lemma holder_cauchy_of_uniform_values {v : ℕ → HMap X E} {L : ℝ} (hL : 0≤L)
    (hl : ∀ i x y,‖valueCLM _ (v i) x-valueCLM _ (v i) y‖≤L*dist x y)
    (hv : ∀ ε : ℝ,0<ε →∃ N : ℕ,∀ i≥N,∀ j≥N,∀ x,
      ‖valueCLM _ (v i) x-valueCLM _ (v j) x‖≤ε) : CauchySeq v := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨δ,hδ,hd⟩ := holder_small_of_small_value (X := X) (E := E) (by linarith : 0≤2*L) hε
  obtain ⟨N,hN⟩ := hv δ hδ
  refine ⟨N,fun i hi j hj => ?_⟩
  rw [dist_eq_norm]
  apply hd (v i-v j)
  · intro x
    exact hN i hi j hj x
  · intro x y
    change ‖(valueCLM _ (v i) x-valueCLM _ (v j) x)-
      (valueCLM _ (v i) y-valueCLM _ (v j) y)‖≤2*L*dist x y
    have he : (valueCLM _ (v i) x-valueCLM _ (v j) x)-
        (valueCLM _ (v i) y-valueCLM _ (v j) y)=
        (valueCLM _ (v i) x-valueCLM _ (v i) y)-
        (valueCLM _ (v j) x-valueCLM _ (v j) y) := by abel
    rw [he]
    exact (norm_sub_le _ _).trans ((add_le_add (hl i x y) (hl j x y)).trans_eq (by ring))

omit [MetricSpace X] [NormedSpace ℝ E] in
lemma uniform_cauchy_of_tendstoUniformly {v : ℕ → X → E} {w : X → E}
    (hv : TendstoUniformly v w atTop) :
    ∀ ε : ℝ,0<ε →∃ N : ℕ,∀ i≥N,∀ j≥N,∀ x,‖v i x-v j x‖≤ε := by
  intro ε hε
  have hh := (Metric.tendstoUniformly_iff.mp hv) (ε/2) (half_pos hε)
  obtain ⟨N,hN⟩ := eventually_atTop.mp hh
  refine ⟨N,fun i hi j hj x => ?_⟩
  have h1 := hN i hi x
  have h2 := hN j hj x
  rw [dist_comm,dist_eq_norm] at h1 h2
  have he : v i x-v j x=(v i x-w x)-(v j x-w x) := by abel
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith)

lemma holder_cauchy_of_tendstoUniformly {v : ℕ → HMap X E} {w : X → E}
    {L : ℝ} (hL : 0≤L)
    (hl : ∀ i x y,‖valueCLM _ (v i) x-valueCLM _ (v i) y‖≤L*dist x y)
    (hv : TendstoUniformly (fun i => valueCLM _ (v i)) w atTop) : CauchySeq v :=
  holder_cauchy_of_uniform_values hL hl (uniform_cauchy_of_tendstoUniformly hv)



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
