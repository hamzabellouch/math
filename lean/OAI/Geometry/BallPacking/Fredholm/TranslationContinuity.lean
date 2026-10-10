import Mathlib
import OAI.Geometry.BallPacking.Fredholm.FreeLinearization

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
section
section BilinearLimit
variable {T X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
lemma bilinear_tendsto_zero_of_bounded (B : X →L[ℝ] Y →L[ℝ] Z) {l : Filter T}
    {A : T → X} (hA : Tendsto A l (𝓝 0)) (V : T → Y) (M : ℝ) (hM : ∀ t, ‖V t‖≤M) :
    Tendsto (fun t => B (A t) (V t)) l (𝓝 0) := by
  have hbound (t : T) : ‖B (A t) (V t)‖≤‖B‖*‖A t‖*M :=
    (B.le_opNorm₂ _ _).trans (mul_le_mul_of_nonneg_left (hM t) (by positivity))
  have hl : Tendsto (fun t => ‖B‖*‖A t‖*M) l (𝓝 0) := by
    simpa only [norm_zero,mul_zero,zero_mul] using (tendsto_const_nhds.mul hA.norm).mul_const M
  exact squeeze_zero_norm hbound hl
end BilinearLimit

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance tcInst1 : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance tcInst2 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance tcInst3 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance tcInst4 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance tcInst5 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance tcInst6 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance tcInst7 : NormedAddCommGroup (COne ℂ (E →L[ℝ] E)) := inferInstance
local instance tcInst8 : NormedSpace ℝ (COne ℂ (E →L[ℝ] E)) := inferInstance
local instance tcInst9 : NormedAddCommGroup (HMap ℂ (E →L[ℝ] E)) := inferInstance
local instance tcInst10 : NormedSpace ℝ (HMap ℂ (E →L[ℝ] E)) := inferInstance

def translationError (A : COne ℂ (E →L[ℝ] E)) (a : E) (u : COne ℂ E) (t : ℂ) : HMap ℂ E :=
  bilinCLM (X := ℂ) (α := (1:ℝ)/3) (ContinuousLinearMap.apply (E := E) ℝ E).flip
    (holderTranslate t (jetValueCLM _ A)-jetValueCLM _ A)
    (const _ a+holderTranslate t (jetDirection 1 u))

omit [CompleteSpace E] in
lemma translationError_value [CompleteSpace E] (A : COne ℂ (E →L[ℝ] E)) (a : E) (u : COne ℂ E) (t z : ℂ) :
    valueCLM _ (translationError A a u t) z =
      (cValue A (z+t)-cValue A z) (a+cDeriv u (z+t) 1) := rfl

omit [CompleteSpace E] in
lemma translation_second_factor_bound [CompleteSpace E] (a : E) (u : COne ℂ E) (t : ℂ) :
    ‖const (X := ℂ) ((1:ℝ)/3) a+holderTranslate t (jetDirection 1 u)‖ ≤
      ‖const (X := ℂ) ((1:ℝ)/3) a‖+‖jetDirection 1 u‖ := by
  have ht : ‖holderTranslate t (jetDirection 1 u)‖ ≤ ‖jetDirection 1 u‖ := holderTranslate_norm_le t (jetDirection 1 u)
  exact (norm_add_le (const (X := ℂ) ((1:ℝ)/3) a) (holderTranslate t (jetDirection 1 u))).trans
    (add_le_add le_rfl ht)

lemma translationError_tendsto (A : COne ℂ (E →L[ℝ] E)) (a : E) (u : COne ℂ E) :
    Tendsto (translationError A a u) (𝓝 0) (𝓝 0) := by
  have hA : Tendsto (fun t => holderTranslate t (jetValueCLM _ A)-jetValueCLM _ A) (𝓝 0) (𝓝 0) := by
    simpa only [sub_self] using (jetValue_translate_tendsto A).sub_const (jetValueCLM _ A)
  exact bilinear_tendsto_zero_of_bounded
    (bilinCLM (X := ℂ) (α := (1:ℝ)/3) (ContinuousLinearMap.apply (E := E) ℝ E).flip) hA
    (fun t => const _ a+holderTranslate t (jetDirection 1 u))
    (‖const (X := ℂ) ((1:ℝ)/3) a‖+‖jetDirection 1 u‖) (translation_second_factor_bound a u)

omit [CompleteSpace E] in
lemma translation_CR_algebra [CompleteSpace E] (A0 A1 : E →L[ℝ] E) (a dx0 dy0 dx1 dy1 : E)
    (h0 : Complex.I • a+dy0=A0 (a+dx0)) (h1 : Complex.I • a+dy1=A1 (a+dx1)) :
    (dy1-dy0)-A0 (dx1-dx0)=(A1-A0) (a+dx1) := by
  rw [map_sub,sub_apply,map_add,map_add]
  rw [map_add] at h0 h1
  calc
    _ = (Complex.I • a+dy1)-(Complex.I • a+dy0)-A0 dx1+A0 dx0 := by abel
    _ = _ := by rw [h1,h0]; abel

variable {R S : ℝ} (hRS : R+1 ≤ S) (a : E)
  (u : freeModel (E := E) (Metric.closedBall (0:ℂ) R))
  (A : COne ℂ (E →L[ℝ] E))
  (hA : ∀ z ∉ Metric.closedBall (0:ℂ) S, cValue A z=complexI (E := E))
  (hcr : ∀ z, Complex.I • a+cDeriv u.val z Complex.I = cValue A z (a+cDeriv u.val z 1))
local instance tcInst11 : NormedAddCommGroup (freeModel (E := E) (Metric.closedBall (0:ℂ) S)) := inferInstance
local instance tcInst12 : NormedSpace ℝ (freeModel (E := E) (Metric.closedBall (0:ℂ) S)) := inferInstance
local instance tcInst13 : NormedAddCommGroup (supportedHolder (E := E) (Metric.closedBall (0:ℂ) S)) := inferInstance
local instance tcInst14 : NormedSpace ℝ (supportedHolder (E := E) (Metric.closedBall (0:ℂ) S)) := inferInstance

include hcr in
lemma freeTranslation_principal_near :
    ∀ᶠ t in 𝓝 (0:ℂ),
      (freePrincipal (jetValueCLM _ A) hA (freeTranslation hRS a u t)).val=translationError A a u.val t := by
  filter_upwards [freeTranslation_near hRS a u] with t ht
  apply value_ext
  intro z
  have hv := freePrincipal_value (jetValueCLM _ A) hA (freeTranslation hRS a u t) z
  have he : cDeriv (freeTranslation hRS a u t).val z = cDeriv u.val (z+t)-cDeriv u.val z :=
    (congrArg (fun w : COne ℂ E => cDeriv w z) ht).trans (translationVariation_deriv a u.val t z)
  have hh := congrArg (fun L : ℂ →L[ℝ] E => L Complex.I-cValue A z (L 1)) he
  apply hv.trans (hh.trans _)
  exact (translation_CR_algebra (cValue A z) (cValue A (z+t)) a
    (cDeriv u.val z 1) (cDeriv u.val z Complex.I)
    (cDeriv u.val (z+t) 1) (cDeriv u.val (z+t) Complex.I) (hcr z) (hcr (z+t))).trans
      (translationError_value A a u.val t z).symm

include hcr in
lemma freeTranslation_principal_tendsto :
    Tendsto (fun t => freePrincipal (jetValueCLM _ A) hA (freeTranslation hRS a u t)) (𝓝 0) (𝓝 0) := by
  have heq : (fun t => (freePrincipal (jetValueCLM _ A) hA (freeTranslation hRS a u t)).val) =ᶠ[𝓝 0]
      translationError A a u.val := freeTranslation_principal_near hRS a u A hA hcr
  have hh : Tendsto (fun t => (freePrincipal (jetValueCLM _ A) hA (freeTranslation hRS a u t)).val)
      (𝓝 0) (𝓝 (0 : HMap ℂ E)) :=
    (translationError_tendsto A a u.val).congr' heq.symm
  exact tendsto_subtype_rng.mpr hh

variable [FiniteDimensional ℝ E]
include hcr in
lemma elliptic_freeTranslation_continuous
    (hP : (freePrincipal (jetValueCLM _ A) hA).IsFredholm) :
    ContinuousAt (freeTranslation hRS a u) 0 := by
  obtain ⟨s,L,hL⟩ := exists_jet_fredholm_observations
    (freeModel (E := E) (Metric.closedBall (0:ℂ) S)) (freePrincipal (jetValueCLM _ A) hA) hP
  have hQ := (freeTranslation_observation_smoothAt hRS a u s).continuousAt
  have hQt : Tendsto (fun t => subspaceObservations (freeModel (E := E) (Metric.closedBall (0:ℂ) S)) s
      (freeTranslation hRS a u t)) (𝓝 0) (𝓝 0) := by
    simpa only [freeTranslation_zero,map_zero] using hQ.tendsto
  have hb := (freeTranslation_principal_tendsto hRS a u A hA hcr).prodMk_nhds hQt
  have hh := (L.continuous.tendsto (0,0)).comp hb
  have he (t : ℂ) : L (freePrincipal (jetValueCLM _ A) hA (freeTranslation hRS a u t),
      subspaceObservations (freeModel (E := E) (Metric.closedBall (0:ℂ) S)) s (freeTranslation hRS a u t)) =
      freeTranslation hRS a u t := hL _
  change Tendsto (freeTranslation hRS a u) _ _
  simpa only [Function.comp_def,he,freeTranslation_zero,Prod.mk_zero_zero,map_zero] using hh

end
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance teInst1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance teInst2 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance teInst3 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance teInst4 : NormedSpace ℝ (HMap ℂ E) := inferInstance

omit [CompleteSpace E] in
lemma affineCurve_translation [CompleteSpace E] (p a : E) (u : COne ℂ E) (t z : ℂ) :
    affineCurve p (complexSlope a) (u+translationVariation a u t) z =
      affineCurve p (complexSlope a) u (z+t) := by
  change p+z • a+(cValue u z+(t • a+cValue u (z+t)-cValue u z)) = p+(z+t) • a+cValue u (z+t)
  rw [add_smul]
  abel

lemma affineCurve_translation_fderiv (p a : E) (u : COne ℂ E) (t z : ℂ) :
    fderiv ℝ (affineCurve p (complexSlope a) (u+translationVariation a u t)) z =
      fderiv ℝ (affineCurve p (complexSlope a) u) (z+t) := by
  rw [affineCurve_fderiv,affineCurve_fderiv]
  change complexSlope a+(cDeriv u z+cDeriv (translationVariation a u t) z) = _
  rw [translationVariation_deriv]
  abel

lemma affineCurve_translation_CR (J : E → E →L[ℝ] E) (p a : E) (u : COne ℂ E)
    (hcr : ∀ z, fderiv ℝ (affineCurve p (complexSlope a) u) z Complex.I =
      J (affineCurve p (complexSlope a) u z) (fderiv ℝ (affineCurve p (complexSlope a) u) z 1)) (t z : ℂ) :
    fderiv ℝ (affineCurve p (complexSlope a) (u+translationVariation a u t)) z Complex.I =
      J (affineCurve p (complexSlope a) (u+translationVariation a u t) z)
        (fderiv ℝ (affineCurve p (complexSlope a) (u+translationVariation a u t)) z 1) := by
  rw [affineCurve_translation_fderiv,affineCurve_translation]
  exact hcr (z+t)

variable {J : E → E →L[ℝ] E} (hJ : BoundedCThree J) (b : ContDiffBump (0:ℂ)) (p a : E)
local instance teInst5 : NormedAddCommGroup (freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance teInst6 : NormedSpace ℝ (freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
variable (u : freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) {B : ℝ}
  (hstd : ∀ x, B<‖x‖ → J x=complexI (E := E))
  (hesc : ∀ᶠ v in 𝓝 (0 : freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)),
    ∀ z, b.rIn≤‖z‖ → B<‖affineCurve p (complexSlope a) (u.val+v.val) z‖)

include hstd in
lemma freeChart_zero_of_CR (v : freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut))
    (he : ∀ z, b.rIn≤‖z‖ → B<‖affineCurve p (complexSlope a) (u.val+v.val) z‖)
    (hcr : ∀ z, fderiv ℝ (affineCurve p (complexSlope a) (u.val+v.val)) z Complex.I =
      J (affineCurve p (complexSlope a) (u.val+v.val) z)
        (fderiv ℝ (affineCurve p (complexSlope a) (u.val+v.val)) z 1)) :
    freeChart hJ b p a u v=0 := by
  apply Subtype.ext
  apply value_ext
  intro z
  have hv := freeChart_true_value hJ b p a u hstd v he z
  have hzero := (crSection_eq_zero_iff hJ p (complexSlope a) (u.val+v.val)).mpr hcr
  apply hv.trans
  rw [hzero]
  rfl

include hstd hesc in
lemma freeChart_translation_zero_near
    (V : ℂ → freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut))
    (hV : ContinuousAt V 0) (hV0 : V 0=0)
    (hv : ∀ᶠ t in 𝓝 (0:ℂ), (V t).val=translationVariation a u.val t)
    (hcr : ∀ z, fderiv ℝ (affineCurve p (complexSlope a) u.val) z Complex.I =
      J (affineCurve p (complexSlope a) u.val z) (fderiv ℝ (affineCurve p (complexSlope a) u.val) z 1)) :
    ∀ᶠ t in 𝓝 (0:ℂ), freeChart hJ b p a u (V t)=0 := by
  have ht : Tendsto V (𝓝 0) (𝓝 0) := by simpa only [hV0] using hV.tendsto
  filter_upwards [ht.eventually hesc,hv] with t hte htv
  apply freeChart_zero_of_CR hJ b p a u hstd (V t) hte
  intro z
  rw [htv]
  exact affineCurve_translation_CR J p a u.val hcr t z

omit hJ hstd hesc in
lemma source_smooth_of_translation
    (V : ℂ → freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut))
    (hv : ∀ᶠ t in 𝓝 (0:ℂ), (V t).val=translationVariation a u.val t)
    (hs : ContDiffAt ℝ ∞ V 0) : ContDiff ℝ ∞ (affineCurve p (complexSlope a) u.val) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  let L : freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut) →L[ℝ] E :=
    (jetEval z).comp (freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)).subtypeL
  have ho : ContDiffAt ℝ ∞ (fun t => affineCurve p (complexSlope a) u.val z+L (V t)) 0 :=
    contDiffAt_const.add (L.contDiff.contDiffAt.comp 0 hs)
  have heq : (fun t => affineCurve p (complexSlope a) u.val (z+t)) =ᶠ[𝓝 0]
      (fun t => affineCurve p (complexSlope a) u.val z+L (V t)) := by
    filter_upwards [hv] with t ht
    change affineCurve p (complexSlope a) u.val (z+t) =
      affineCurve p (complexSlope a) u.val z+cValue (V t).val z
    rw [ht,translationVariation_value]
    change p+(z+t) • a+cValue u.val (z+t) =
      (p+z • a+cValue u.val z)+(t • a+cValue u.val (z+t)-cValue u.val z)
    rw [add_smul]
    abel
  have hf := ho.congr_of_eventuallyEq heq
  have hsub : ContDiffAt ℝ ∞ (fun t : ℂ => t-z) z := contDiffAt_id.sub contDiffAt_const
  have hf' : ContDiffAt ℝ ∞ (fun t => affineCurve p (complexSlope a) u.val (z+t)) (z-z) := by
    simpa only [sub_self] using hf
  have hcomp := hf'.comp (f := fun t : ℂ => t-z) z hsub
  convert! hcomp using 1
  funext t
  congr 1
  simp only
  abel

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance feInst1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance feInst2 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance feInst3 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance feInst4 : NormedSpace ℝ (HMap ℂ E) := inferInstance

omit [CompleteSpace E] in
lemma affine_free_norm_lower [CompleteSpace E] (p a : E) (u v : COne ℂ E) (z : ℂ) :
    ‖z‖*‖a‖-‖p‖-‖u‖-‖v‖ ≤ ‖affineCurve p (complexSlope a) (u+v) z‖ := by
  have h : ‖z • a‖ ≤ ‖affineCurve p (complexSlope a) (u+v) z‖+‖p‖+‖cValue u z‖+‖cValue v z‖ := by
    calc
      _ = ‖((affineCurve p (complexSlope a) (u+v) z-p)-cValue u z)-cValue v z‖ := by
        congr 1
        change z • a=((p+z • a+(cValue u z+cValue v z)-p)-cValue u z)-cValue v z
        abel
      _ ≤ ‖(affineCurve p (complexSlope a) (u+v) z-p)-cValue u z‖+‖cValue v z‖ := norm_sub_le _ _
      _ ≤ (‖affineCurve p (complexSlope a) (u+v) z-p‖+‖cValue u z‖)+‖cValue v z‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ _ := by linarith [norm_sub_le (affineCurve p (complexSlope a) (u+v) z) p]
  rw [norm_smul] at h
  linarith [c_value_bound u z,c_value_bound v z]

lemma exists_free_escape_radius (p a : E) (u : COne ℂ E) (ha : a≠0) (B : ℝ) :
    ∃ R : ℝ, 0<R ∧ ∀ v : COne ℂ E, ‖v‖<1 → ∀ z : ℂ, R≤‖z‖ →
      B<‖affineCurve p (complexSlope a) (u+v) z‖ := by
  let R := (max B 0+‖p‖+‖u‖+2)/‖a‖
  have ha' : 0<‖a‖ := norm_pos_iff.mpr ha
  have hR : 0<R := div_pos (by have := le_max_right B 0; positivity) ha'
  refine ⟨R,hR,?_⟩
  intro v hv z hz
  have hn : max B 0+‖p‖+‖u‖+2 ≤ ‖z‖*‖a‖ := by
    have hm := mul_le_mul_of_nonneg_right hz ha'.le
    dsimp only [R] at hm
    rwa [div_mul_cancel₀ _ ha'.ne'] at hm
  exact (show B<‖z‖*‖a‖-‖p‖-‖u‖-‖v‖ by linarith [le_max_left B 0]).trans_le
    (affine_free_norm_lower p a u v z)

omit [CompleteSpace E] in
lemma freeModel_mono [CompleteSpace E] {K L : Set ℂ} (h : K⊆L) : freeModel (E := E) K ≤ freeModel (E := E) L := by
  intro u hu
  apply (mem_supportedHolder _ _).mpr
  intro z hz
  exact (mem_supportedHolder _ _).mp hu z (fun hK => hz (h hK))

omit [CompleteSpace E] in
lemma freeModel_of_elliptic [CompleteSpace E] {J : E → E →L[ℝ] E} {B R : ℝ}
    (hstd : ∀ x, B<‖x‖ → J x=complexI (E := E))
    (p a : E) (u : COne ℂ E)
    (hcr : ∀ z, fderiv ℝ (affineCurve p (complexSlope a) u) z Complex.I =
      J (affineCurve p (complexSlope a) u z) (fderiv ℝ (affineCurve p (complexSlope a) u) z 1))
    (he : ∀ z, R≤‖z‖ → B<‖affineCurve p (complexSlope a) u z‖) :
    u∈freeModel (E := E) (Metric.closedBall (0:ℂ) R) := by
  apply (mem_supportedHolder _ _).mpr
  intro z hz
  have hz' : R≤‖z‖ := (show R<‖z‖ by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hz).le
  have hh := hcr z
  rw [hstd _ (he z hz'),affineCurve_fderiv] at hh
  change Complex.I • a+cDeriv u z Complex.I=Complex.I • ((1:ℂ) • a+cDeriv u z 1) at hh
  rw [one_smul,smul_add] at hh
  have hd := add_left_cancel hh
  change valueCLM _ (standardJetCR u) z=0
  rw [standardJetCR_value]
  exact sub_eq_zero.mpr hd

variable (b : ContDiffBump (0:ℂ))
local instance feInst5 : NormedAddCommGroup (freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance feInst6 : NormedSpace ℝ (freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance

def FreeEscapeNeighborhood (p a : E) (u : COne ℂ E) (B : ℝ) : Prop :=
  ∀ᶠ v : freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut) in 𝓝 0,
    ∀ z, b.rIn≤‖z‖ → B<‖affineCurve p (complexSlope a) (u+v.val) z‖

omit [CompleteSpace E] in
lemma freeEscape_of_radius [CompleteSpace E] (p a : E) (u : COne ℂ E) (B : ℝ)
    (he : ∀ v : COne ℂ E, ‖v‖<1 → ∀ z : ℂ, b.rIn≤‖z‖ →
      B<‖affineCurve p (complexSlope a) (u+v) z‖) : FreeEscapeNeighborhood b p a u B := by
  filter_upwards [Metric.ball_mem_nhds (0 : freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) (show (0:ℝ)<1 by norm_num)] with v hv
  have hv' : ‖v.val‖<1 := by simpa only [Metric.mem_ball,dist_zero_right,Submodule.norm_coe] using hv
  exact he v.val hv'

end HigherDimensionalBallPacking.Rigidity.HolderCompletion

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter
variable {X E F D : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup D] [NormedSpace ℝ D]

lemma nonlinear_stabilized_regularity {f : E → F} (hf : ContDiff ℝ ∞ f)
    {P : E →L[ℝ] F} {v : X → E} {x : X} (hP : HasFDerivAt f P (v x))
    (Q : E →L[ℝ] D) (L : F × D →L[ℝ] E) (hL : LeftInverse L (P.prod Q))
    (hv : ContinuousAt v x) (hQ : ContDiffAt ℝ ∞ (fun t => Q (v t)) x)
    (he : ∀ᶠ t in 𝓝 x, f (v t)=0) : ContDiffAt ℝ ∞ v x := by
  let G : E → E := fun y => L (f y,Q y)
  have hG : ContDiff ℝ ∞ G := L.contDiff.comp (hf.prodMk Q.contDiff)
  have hd : HasFDerivAt G (ContinuousLinearEquiv.refl ℝ E).toContinuousLinearMap (v x) := by
    have hh := L.hasFDerivAt.comp (v x) (hP.prodMk (Q.hasFDerivAt (x := v x)))
    have h : L.comp (P.prod Q) = (ContinuousLinearEquiv.refl ℝ E).toContinuousLinearMap := by
      ext y
      exact hL y
    exact h ▸ hh
  let e := hG.contDiffAt.toOpenPartialHomeomorph G hd (by simp)
  have hm : v x ∈ e.source := ContDiffAt.mem_toOpenPartialHomeomorph_source hG.contDiffAt hd (by simp)
  have hs : ContDiffAt ℝ ∞ e.symm (G (v x)) :=
    ContDiffAt.to_localInverse hG.contDiffAt hd (by simp)
  have hval : G (v x)=L (0,Q (v x)) := by
    change L (f (v x),Q (v x)) = _
    rw [he.self_of_nhds]
  have hout : ContDiffAt ℝ ∞ (fun t => e.symm (L (0,Q (v t)))) x := by
    rw [hval] at hs
    exact hs.comp x (L.contDiff.contDiffAt.comp x (contDiffAt_const.prodMk hQ))
  apply hout.congr_of_eventuallyEq
  have hn : ∀ᶠ t in 𝓝 x, v t∈e.source := hv.eventually (e.open_source.mem_nhds hm)
  filter_upwards [hn,he] with t ht ht0
  have hh := e.left_inv ht
  change e.symm (G (v t))=v t at hh
  change v t=e.symm (L (0,Q (v t)))
  calc
    v t = e.symm (G (v t)) := hh.symm
    _ = e.symm (L (0,Q (v t))) := by
      apply congrArg e.symm
      change L (f (v t),Q (v t))=L (0,Q (v t))
      rw [ht0]

end HigherDimensionalBallPacking.Rigidity

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
section
variable {n : ℕ}
local instance srInst1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance srInst2 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace
local instance srInst3 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance srInst4 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
local instance srInst5 : NormedAddCommGroup (HMap ℂ (Phase n)) := inferInstance
local instance srInst6 : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance
variable {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J) (hc : ∀ x, Compatible (J x)) {B : ℝ}
  (hstd : ∀ x, B<‖x‖ → J x=standardJ n) (b : ContDiffBump (0:ℂ)) (p q : Phase n)
local instance srInst7 : NormedAddCommGroup (freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance srInst8 : NormedSpace ℝ (freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance srInst9 : AddCommGroup (freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (srInst7 (n := n) b).toAddCommGroup
local instance srInst10 : Module ℝ (freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (srInst8 (n := n) b).toModule
local instance srInst11 : TopologicalSpace (freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) :=
  (srInst7 (n := n) b).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
variable (w : freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) {R : ℝ}
  (hRS : R+1≤b.rOut) (hsupp : w.val ∈ freeModel (E := Phase n) (Metric.closedBall (0:ℂ) R))
  (hesc : FreeEscapeNeighborhood b p (markedSlope p q w.val) w.val B)
  (hcr : ∀ z, fderiv ℝ (markedCurve p q w.val) z Complex.I =
    J (markedCurve p q w.val z) (fderiv ℝ (markedCurve p q w.val) z 1))

def regularityTranslation : ℂ → freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut) :=
  freeTranslation hRS (markedSlope p q w.val) ⟨w.val,hsupp⟩

@[simp] lemma regularityTranslation_zero : regularityTranslation b p q w hRS hsupp 0=0 :=
  freeTranslation_zero hRS (markedSlope p q w.val) ⟨w.val,hsupp⟩

lemma regularityTranslation_near : ∀ᶠ t in 𝓝 (0:ℂ),
    (regularityTranslation b p q w hRS hsupp t).val=translationVariation (markedSlope p q w.val) w.val t :=
  freeTranslation_near hRS (markedSlope p q w.val) ⟨w.val,hsupp⟩

include hJ hstd hc hesc hcr hRS hsupp in
lemma regularityTranslation_continuous : ContinuousAt (regularityTranslation b p q w hRS hsupp) 0 := by
  let A := completedStructureJet hJ hstd p q w.val
  have he := free_escape_base p q b w hesc
  have hA : ∀ z ∉ Metric.closedBall (0:ℂ) b.rOut, cValue A z=complexI (E := Phase n) :=
    fun z hz => hstd _ (he z hz)
  have hcr' : ∀ z, Complex.I • markedSlope p q w.val+cDeriv w.val z Complex.I =
      cValue A z (markedSlope p q w.val+cDeriv w.val z 1) := by
    intro z
    simpa only [A,completedStructureJet_value,markedCurve_fderiv,add_apply,complexSlope_apply,one_smul] using hcr z
  have hp : (freePrincipal (jetValueCLM _ A) hA).IsFredholm :=
    completedFreePrincipal_fredholm hJ hc hstd p q w.val (isCompact_closedBall (0:ℂ) b.rOut) he
  exact elliptic_freeTranslation_continuous hRS (markedSlope p q w.val) ⟨w.val,hsupp⟩ A hA hcr' hp

include hJ hstd hc hesc hcr hRS hsupp in
lemma regularityTranslation_smooth : ContDiffAt ℝ ∞ (regularityTranslation b p q w hRS hsupp) 0 := by
  let V := regularityTranslation b p q w hRS hsupp
  let D := fderiv ℝ (actualFreeChart hJ hstd p q b w) 0
  have hf := actualFreeChart_contDiff hJ hstd p q b w
  have hD : D.IsFredholm := actualFreeChart_fderiv_fredholm hJ hc hstd p q b w hesc
  obtain ⟨s,L,hL⟩ := exists_jet_fredholm_observations
    (freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) D hD
  have hd : HasFDerivAt (actualFreeChart hJ hstd p q b w) D (V 0) := by
    change HasFDerivAt _ D (regularityTranslation b p q w hRS hsupp 0)
    rw [regularityTranslation_zero]
    exact (hf.differentiable (by simp) 0).hasFDerivAt
  have hV : ContinuousAt V 0 := regularityTranslation_continuous hJ hc hstd b p q w hRS hsupp hesc hcr
  have hQ : ContDiffAt ℝ ∞ (fun t => subspaceObservations
      (freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) s (V t)) 0 :=
    freeTranslation_observation_smoothAt hRS (markedSlope p q w.val) ⟨w.val,hsupp⟩ s
  have hz : ∀ᶠ t in 𝓝 (0:ℂ), actualFreeChart hJ hstd p q b w (V t)=0 :=
    freeChart_translation_zero_near (actualStructureBound hJ hstd) b p (markedSlope p q w.val) w hstd hesc V hV
      (regularityTranslation_zero b p q w hRS hsupp) (regularityTranslation_near b p q w hRS hsupp) hcr
  exact nonlinear_stabilized_regularity hf hd _ L hL hV hQ hz

include hJ hstd hc hesc hcr hRS hsupp in
lemma completed_free_source_contDiff : ContDiff ℝ ∞ (markedCurve p q w.val) := by
  have hs := regularityTranslation_smooth hJ hc hstd b p q w hRS hsupp hesc hcr
  have hh := source_smooth_of_translation b p (markedSlope p q w.val) w
    (regularityTranslation b p q w hRS hsupp) (regularityTranslation_near b p q w hRS hsupp) hs
  exact hh

end
section
variable {n : ℕ}
local instance actFredInst1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance actFredInst2 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace
local instance actFredInst3 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance actFredInst4 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
local instance actFredInst5 : NormedAddCommGroup (HMap ℂ (Phase n)) := inferInstance
local instance actFredInst6 : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance
variable {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J) (hc : ∀ x, Compatible (J x)) {B : ℝ}
  (hstd : ∀ x, B < ‖x‖ → J x=standardJ n) (b : ContDiffBump (0:ℂ)) (p q : Phase n)
local instance actFredInst7 : NormedAddCommGroup (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance actFredInst8 : NormedSpace ℝ (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance actFredInst9 : AddCommGroup (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (actFredInst7 (n := n) b).toAddCommGroup
local instance actFredInst10 : Module ℝ (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (actFredInst8 (n := n) b).toModule
local instance actFredInst11 : TopologicalSpace (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) :=
  (actFredInst7 (n := n) b).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
local instance actFredInst12 : NormedAddCommGroup (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance actFredInst13 : NormedSpace ℝ (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance actFredInst14 : AddCommGroup (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (actFredInst12 (n := n) b).toAddCommGroup
local instance actFredInst15 : Module ℝ (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (actFredInst13 (n := n) b).toModule
variable (u : markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut))
  (he : ∀ᶠ h in 𝓝 (0 : markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)),
    ∀ z : ℂ, b.rIn ≤ ‖z‖ → B < ‖markedCurve p q (u.val+h.val) z‖ ∧
      B < ‖truncatedCurve b p q u.val h.val z‖)

include he in
lemma marked_escape_base : ∀ z ∉ Metric.closedBall (0:ℂ) b.rOut, B < ‖markedCurve p q u.val z‖ := by
  intro z hz
  have hz' : b.rIn ≤ ‖z‖ := by
    have hz'' : b.rOut < ‖z‖ := by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hz
    exact (b.rIn_lt_rOut.trans hz'').le
  have hh := (he.self_of_nhds z hz').1
  simpa only [Submodule.coe_zero,add_zero] using hh

lemma actualMarkedChart_derivative_eq_linearized
    (b₁ : ContDiffBump (0:ℂ)) (hb₁ : Metric.closedBall (0:ℂ) b.rOut ⊆ Metric.closedBall (0:ℂ) b₁.rIn) :
    fderiv ℝ (actualMarkedChart hJ hstd b p q u) 0 =
      completedLinearized hJ hstd p q u.val (marked_escape_base b p q u he) b₁ hb₁ := by
  apply ContinuousLinearMap.ext
  intro v
  apply Subtype.ext
  apply value_ext
  intro z
  have hd := congrArg (fun L : markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut) →L[ℝ] Phase n => L v)
    (actualMarkedChart_fderiv_eval hJ hstd b p q u he z)
  exact hd.trans (completedLinearized_value hJ hstd p q u.val (marked_escape_base b p q u he) b₁ hb₁ v z).symm

def actualMarkedDerivative := fderiv ℝ (actualMarkedChart hJ hstd b p q u) 0

def IsIndexZeroFredholm {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (D : X →L[ℝ] Y) : Prop :=
  D.IsFredholm ∧ Module.finrank ℝ D.ker = Module.finrank ℝ (Y ⧸ D.range)

include hc he in
lemma actualMarkedChart_derivative_fredholm :
    IsIndexZeroFredholm (actualMarkedDerivative hJ hstd b p q u) := by
  obtain ⟨b₁,hb₁⟩ := compact_subset_bump_inner (K := Metric.closedBall (0:ℂ) b.rOut)
    (isCompact_closedBall (0:ℂ) b.rOut)
  have hd : actualMarkedDerivative hJ hstd b p q u =
      completedLinearized hJ hstd p q u.val (marked_escape_base b p q u he) b₁ hb₁ :=
    actualMarkedChart_derivative_eq_linearized hJ hstd b p q u he b₁ hb₁
  have hf : IsIndexZeroFredholm
      (completedLinearized hJ hstd p q u.val (marked_escape_base b p q u he) b₁ hb₁) :=
    completedLinearized_fredholm hJ hc hstd p q u.val (isCompact_closedBall (0:ℂ) b.rOut)
      (marked_escape_base b p q u he) b₁ hb₁
  exact hd ▸ hf

end
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance chartNbInst1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance chartNbInst2 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance chartNbInst3 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance chartNbInst4 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance chartNbInst5 (K : Set ℂ) : NormedAddCommGroup (markedModel (E := E) K) := inferInstance
local instance chartNbInst6 (K : Set ℂ) : NormedSpace ℝ (markedModel (E := E) K) := inferInstance
local instance chartNbInst7 (K : Set ℂ) : AddCommGroup (markedModel (E := E) K) := (chartNbInst5 K).toAddCommGroup
local instance chartNbInst8 (K : Set ℂ) : Module ℝ (markedModel (E := E) K) := (chartNbInst6 K).toModule
local instance chartNbInst9 (K : Set ℂ) : TopologicalSpace (markedModel (E := E) K) :=
  (chartNbInst5 K).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

omit [CompleteSpace E] in
lemma supportedHolder_mono [CompleteSpace E] {K L : Set ℂ} (hKL : K ⊆ L) :
    supportedHolder (E := E) K ≤ supportedHolder (E := E) L := by
  intro g hg
  rw [mem_supportedHolder] at hg ⊢
  intro z hz
  exact hg z (fun hzK => hz (hKL hzK))

lemma markedModel_mono {K L : Set ℂ} (hKL : K ⊆ L) :
    markedModel (E := E) K ≤ markedModel (E := E) L := by
  intro u hu
  exact ⟨hu.1,supportedHolder_mono hKL hu.2⟩

def widenMarked {K L : Set ℂ} (hKL : K ⊆ L) (u : markedModel (E := E) K) : markedModel (E := E) L :=
  ⟨u.val,markedModel_mono hKL u.property⟩

def MarkedEscapeNeighborhood (b : ContDiffBump (0:ℂ)) (p q : E) (u : COne ℂ E) (B : ℝ) : Prop :=
  ∀ᶠ h in 𝓝 (0 : markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)),
    ∀ z : ℂ, b.rIn ≤ ‖z‖ → B < ‖markedCurve p q (u+h.val) z‖ ∧
      B < ‖truncatedCurve b p q u h.val z‖

omit [CompleteSpace E] in
lemma markedEscape_of_uniform [CompleteSpace E] (p q : E) (u : COne ℂ E) (B δ R : ℝ) (hδ : 0 < δ)
    (he : ∀ h : COne ℂ E, ‖h‖ < δ → ∀ z : ℂ, R ≤ ‖z‖ →
      B < ‖markedCurve p q (u+h) z‖ ∧ ∀ b : ContDiffBump (0:ℂ), B < ‖truncatedCurve b p q u h z‖)
    (b : ContDiffBump (0:ℂ)) (hR : R ≤ b.rIn) : MarkedEscapeNeighborhood b p q u B := by
  filter_upwards [Metric.ball_mem_nhds (0 : markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) hδ] with h hh
  intro z hz
  have hh' : ‖h.val‖ < δ := by simpa only [Metric.mem_ball,dist_zero_right,Submodule.norm_coe] using hh
  exact ⟨(he h.val hh' z (hR.trans hz)).1,(he h.val hh' z (hR.trans hz)).2 b⟩

lemma exists_chart_escape_neighborhood {K : Set ℂ} (hK : IsCompact K) (p q : E)
    (u : markedModel (E := E) K) (ha : markedSlope p q u.val ≠ 0) {B : ℝ} (hB : 0 ≤ B) :
    ∃ b : ContDiffBump (0:ℂ), K ⊆ Metric.closedBall (0:ℂ) b.rOut ∧
      MarkedEscapeNeighborhood b p q u.val B := by
  obtain ⟨δ,R,hδ,hR,he⟩ := exists_uniform_escape p q u.val ha hB
  obtain ⟨S,hS,hKS⟩ := hK.isBounded.exists_pos_norm_le
  let b : ContDiffBump (0:ℂ) := ⟨max R S,max R S+1,lt_max_iff.mpr (Or.inl hR),by linarith⟩
  have hKL : K ⊆ Metric.closedBall (0:ℂ) b.rOut := by
    intro z hz
    have hzS := hKS z hz
    change dist z 0 ≤ max R S+1
    rw [dist_zero_right]
    exact hzS.trans ((le_max_right R S).trans (by linarith))
  refine ⟨b,hKL,?_⟩
  exact markedEscape_of_uniform p q u.val B δ R hδ he b (le_max_left R S)

end
section

lemma realCR_axis_implies_all {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] E) (hA : ∀ v, A (A v) = -v) (L : ℂ →L[ℝ] E)
    (hL : L Complex.I = A (L 1)) (w : ℂ) : L (Complex.I*w) = A (L w) := by
  have hw : w = w.re • (1:ℂ)+w.im • Complex.I := by
    apply Complex.ext <;> simp [Complex.real_smul]
  have hIw : Complex.I*w = (-w.im) • (1:ℂ)+w.re • Complex.I := by
    apply Complex.ext <;> simp [Complex.real_smul,Complex.mul_re,Complex.mul_im]
  calc
    L (Complex.I*w) = (-w.im) • L 1 + w.re • L Complex.I := by
      rw [hIw,map_add,map_smul,map_smul]
    _ = A (w.re • L 1+w.im • L Complex.I) := by
      rw [map_add,map_smul,map_smul,hL,hA]
      module
    _ = A (L w) := congrArg A (by simpa only [map_add,map_smul] using (congrArg L hw).symm)

variable {n : ℕ}
local instance chartZeroInst1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance chartZeroInst2 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace
local instance chartZeroInst3 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance chartZeroInst4 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
local instance chartZeroInst5 : NormedAddCommGroup (HMap ℂ (Phase n)) := inferInstance
local instance chartZeroInst6 : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance
variable {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J) (hc : ∀ x, Compatible (J x)) {B : ℝ}
  (hstd : ∀ x, B < ‖x‖ → J x=standardJ n) (b : ContDiffBump (0:ℂ)) (p q : Phase n)
local instance chartZeroInst7 : NormedAddCommGroup (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance chartZeroInst8 : NormedSpace ℝ (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
variable (u h : markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut))
  (he : ∀ z : ℂ, b.rIn ≤ ‖z‖ → B < ‖markedCurve p q (u.val+h.val) z‖ ∧
    B < ‖truncatedCurve b p q u.val h.val z‖)

include hc he in
lemma actualMarkedChart_zero_pseudoholomorphic
    (hz : actualMarkedChart hJ hstd b p q u h = 0) (z : ℂ) :
    PseudoHolomorphicAt J (markedCurve p q (u.val+h.val)) z := by
  have hV := actualMarkedChart_value hJ hstd b p q u h he z
  have hzero : pointMarkedCR J p q u.val z h = 0 := by
    rw [hz,map_zero] at hV
    exact hV.symm
  have haxis : fderiv ℝ (markedCurve p q (u.val+h.val)) z Complex.I =
      J (markedCurve p q (u.val+h.val) z) (fderiv ℝ (markedCurve p q (u.val+h.val)) z 1) :=
    sub_eq_zero.mp hzero
  refine ⟨(markedCurve_hasFDerivAt p q (u.val+h.val) z).differentiableAt,?_⟩
  exact realCR_axis_implies_all _ (hc _).1 _ haxis

lemma completedMarkedCurve_contDiff_one : ContDiff ℝ 1 (markedCurve p q (u.val+h.val)) := by
  have hlinear : ContDiff ℝ 1 (fun z : ℂ => p+complexSlope (markedSlope p q (u.val+h.val)) z) :=
    contDiff_const.add (complexSlope _).contDiff
  exact hlinear.add (contDiff_one (u.val+h.val))

lemma completedMarkedCurve_marks : markedCurve p q (u.val+h.val) 0=p ∧
    markedCurve p q (u.val+h.val) 1=q := by
  have hz : cValue (u.val+h.val) 0=0 := by
    change cValue u.val 0+cValue h.val 0=0
    have hu0 : cValue u.val 0 = 0 := u.property.1
    have hh0 : cValue h.val 0 = 0 := h.property.1
    rw [hu0,hh0,add_zero]
  exact ⟨markedCurve_zero p q hz,markedCurve_one p q _⟩

lemma completedMarkedCurve_asymptote (ha : markedSlope p q (u.val+h.val) ≠ 0) :
    ∃ v : Phase n, v ≠ 0 ∧ Tendsto (fun z : ℂ => z⁻¹ • markedCurve p q (u.val+h.val) z)
      (cocompact ℂ) (𝓝 v) :=
  ⟨markedSlope p q (u.val+h.val),ha,markedCurve_asymptote p q (u.val+h.val)⟩

end
section
variable {n : ℕ}
local instance azInst1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance azInst2 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace
local instance azInst3 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance azInst4 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
local instance azInst5 : NormedAddCommGroup (HMap ℂ (Phase n)) := inferInstance
local instance azInst6 : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance
variable {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J) (hc : ∀ x, Compatible (J x)) {B : ℝ}
  (hstd : ∀ x, B<‖x‖ → J x=standardJ n) (p q : Phase n)

include hJ hc hstd in
lemma completed_markedCurve_contDiff (u : COne ℂ (Phase n)) (ha : markedSlope p q u ≠ 0)
    (hcr : ∀ z, fderiv ℝ (markedCurve p q u) z Complex.I =
      J (markedCurve p q u z) (fderiv ℝ (markedCurve p q u) z 1)) :
    ContDiff ℝ ∞ (markedCurve p q u) := by
  obtain ⟨R,hR,he⟩ := exists_free_escape_radius p (markedSlope p q u) u ha B
  have he0 : ∀ z, R≤‖z‖ → B<‖affineCurve p (complexSlope (markedSlope p q u)) u z‖ := by
    intro z hz
    simpa only [add_zero] using he 0 (by simp) z hz
  have huR : u∈freeModel (E := Phase n) (Metric.closedBall (0:ℂ) R) :=
    freeModel_of_elliptic hstd p (markedSlope p q u) u hcr he0
  let b : ContDiffBump (0:ℂ) := ⟨R,R+2,hR,by linarith⟩
  have hRS : R+1≤b.rOut := by change R+1≤R+2; linarith
  have huS : u∈freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut) :=
    freeModel_mono (Metric.closedBall_subset_closedBall (by change R≤R+2; linarith)) huR
  let w : freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut) := ⟨u,huS⟩
  have hesc : FreeEscapeNeighborhood b p (markedSlope p q w.val) w.val B :=
    freeEscape_of_radius b p (markedSlope p q u) u B he
  exact completed_free_source_contDiff hJ hc hstd b p q w hRS huR hesc hcr

variable (b : ContDiffBump (0:ℂ))
local instance azInst7 : NormedAddCommGroup (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance azInst8 : NormedSpace ℝ (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
variable (u h : markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut))
  (he : ∀ z : ℂ, b.rIn≤‖z‖ → B<‖markedCurve p q (u.val+h.val) z‖ ∧
    B<‖truncatedCurve b p q u.val h.val z‖)

include hc he in
lemma actualMarkedChart_zero_affineLine
    (ha : markedSlope p q (u.val+h.val) ≠ 0)
    (hz : actualMarkedChart hJ hstd b p q u h=0) :
    AffineLineCurve J p q (markedCurve p q (u.val+h.val)) := by
  have hph := actualMarkedChart_zero_pseudoholomorphic hJ hc hstd b p q u h he hz
  have hcr : ∀ z, fderiv ℝ (markedCurve p q (u.val+h.val)) z Complex.I =
      J (markedCurve p q (u.val+h.val) z) (fderiv ℝ (markedCurve p q (u.val+h.val)) z 1) := by
    intro z
    simpa only [mul_one] using (hph z).2 1
  have hm := completedMarkedCurve_marks b p q u h
  exact ⟨completed_markedCurve_contDiff hJ hc hstd p q _ ha hcr,hph,hm.1,hm.2,
    completedMarkedCurve_asymptote b p q u h ha⟩

end

variable {n : ℕ}
local instance gcInst1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance gcInst2 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace
local instance gcInst3 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance gcInst4 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
local instance gcInst5 : NormedAddCommGroup (HMap ℂ (Phase n)) := inferInstance
local instance gcInst6 : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance

local instance gcInst7 (K : Set ℂ) : NormedAddCommGroup (markedModel (E := Phase n) K) := inferInstance
local instance gcInst8 (K : Set ℂ) : NormedSpace ℝ (markedModel (E := Phase n) K) := inferInstance
local instance gcInst9 (K : Set ℂ) : NormedAddCommGroup (supportedHolder (E := Phase n) K) := inferInstance
local instance gcInst10 (K : Set ℂ) : NormedSpace ℝ (supportedHolder (E := Phase n) K) := inferInstance

def geometricResidual (u : ℂ → Phase n) (z : ℂ) : Phase n :=
  fderiv ℝ u z Complex.I-Complex.I • fderiv ℝ u z 1

lemma geometricResidual_smooth {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (geometricResidual u) := by
  have hd := hu.fderiv_right (m := ∞) (by simp)
  have hx : ContDiff ℝ ∞ (fun z => fderiv ℝ u z 1) := hd.clm_apply contDiff_const
  have hy : ContDiff ℝ ∞ (fun z => fderiv ℝ u z Complex.I) := hd.clm_apply contDiff_const
  have hI : ContDiff ℝ ∞ (fun _ : ℂ => Complex.I) := contDiff_const
  exact hy.sub (hI.smul hx)

lemma geometricResidual_compact {J : Phase n → End n} {p q : Phase n} {u : ℂ → Phase n}
    (hu : AffineLineCurve J p q u) (hJc : HasCompactSupport (fun x => J x-standardJ n)) :
    HasCompactSupport (geometricResidual u) := by
  apply HasCompactSupport.of_support_subset_isCompact (hu.isProperMap.isCompact_preimage hJc)
  intro z hz
  by_contra hn
  have hstd : J (u z)=standardJ n := sub_eq_zero.mp
    (image_eq_zero_of_notMem_tsupport (f := fun x => J x-standardJ n) hn)
  have hcr := (hu.2.1 z).2 1
  simp only [mul_one,hstd] at hcr
  apply hz
  exact sub_eq_zero.mpr hcr

lemma inverse_correction_holomorphic {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u)
    {K : Set ℂ} (hK : IsCompact K) (g : supportedHolder (E := Phase n) K)
    (hg : ∀ z, valueCLM _ g.val z=geometricResidual u z) :
    Differentiable ℂ (fun z => u z-cValue (standardHolderInverse hK g) z) := by
  let v := standardHolderInverse hK g
  intro z
  have hd := ((hu.differentiable (by simp)) z).hasFDerivAt.sub (c_hasFDerivAt v z)
  apply complex_differentiable_of_curl_zero hd.differentiableAt
  have hres : cDeriv v z Complex.I-Complex.I • cDeriv v z 1=geometricResidual u z := by
    have he := congrArg (fun w : HMap ℂ (Phase n) => valueCLM _ w z)
      (standardHolderInverse_residual hK g)
    simpa only [standardJetCR_value] using he.trans (hg z)
  rw [hd.fderiv]
  change Complex.I • (fderiv ℝ u z 1-cDeriv v z 1)-
    (fderiv ℝ u z Complex.I-cDeriv v z Complex.I)=0
  rw [smul_sub]
  calc
    _ = (cDeriv v z Complex.I-Complex.I • cDeriv v z 1)-geometricResidual u z := by
      unfold geometricResidual
      abel
    _ = 0 := sub_eq_zero.mpr hres

lemma inverse_correction_asymptote {u : ℂ → Phase n} {a : Phase n}
    (ha : Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 a))
    (v : COne ℂ (Phase n)) :
    Tendsto (fun z : ℂ => z⁻¹ • (u z-cValue v z)) (cocompact ℂ) (𝓝 a) := by
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa only [←Metric.cobounded_eq_cocompact] using (tendsto_inv₀_cobounded (α := ℂ))
  have hb : IsBoundedUnder (· ≤ ·) (cocompact ℂ) (norm ∘ (cValue v : ℂ → Phase n)) :=
    ⟨‖cValue v‖,eventually_map.mpr (Eventually.of_forall fun z => (cValue v).norm_coe_le_norm z)⟩
  simpa only [smul_sub,sub_zero] using ha.sub (hi.zero_smul_isBoundedUnder_le hb)

lemma affine_reconstruction_from_correction {u : ℂ → Phase n} {p a : Phase n}
    (v : COne ℂ (Phase n))
    (hd : Differentiable ℂ (fun z => u z-cValue v z))
    (ha : Tendsto (fun z : ℂ => z⁻¹ • (u z-cValue v z)) (cocompact ℂ) (𝓝 a))
    (h0 : u 0=p) (hv0 : cValue v 0=0) (z : ℂ) :
    u z=p+z • a+cValue v z := by
  have he := entire_affine_of_asymptote hd ha z
  rw [h0,hv0,sub_zero] at he
  exact sub_eq_iff_eq_add.mp he

lemma marked_reconstruction_from_correction {u : ℂ → Phase n} {p q a : Phase n}
    (v : COne ℂ (Phase n))
    (hd : Differentiable ℂ (fun z => u z-cValue v z))
    (ha : Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 a))
    (h0 : u 0=p) (h1 : u 1=q) (hv0 : cValue v 0=0) :
    markedCurve p q v=u ∧ markedSlope p q v=a := by
  have hinf := inverse_correction_asymptote ha v
  have hrec := affine_reconstruction_from_correction v hd hinf h0 hv0
  have hslope : markedSlope p q v=a := by
    have he := hrec 1
    rw [h1,one_smul] at he
    rw [markedSlope,he]
    abel
  refine ⟨?_,hslope⟩
  funext z
  rw [markedCurve,hslope]
  exact (hrec z).symm

lemma affineLineCurve_completed_representation {J : Phase n → End n} {p q : Phase n}
    {u : ℂ → Phase n} (hu : AffineLineCurve J p q u)
    (hJc : HasCompactSupport (fun x => J x-standardJ n)) :
    ∃ (K : Set ℂ), IsCompact K ∧ ∃ v : markedModel (E := Phase n) K,
      markedCurve p q v.val=u ∧ markedSlope p q v.val ≠ 0 := by
  have hr := geometricResidual_compact hu hJc
  have hG := boundedCThree_of_compactSupport (geometricResidual_smooth hu.1) hr
  let G : HMap ℂ (Phase n) := jetValueCLM _ (ofBoundedCThree hG)
  have hGval : ∀ z, valueCLM _ G z=geometricResidual u z := fun _ => rfl
  let K := tsupport (geometricResidual u)
  have hK : IsCompact K := hr
  have hGK : G∈supportedHolder K := by
    apply (mem_supportedHolder _ _).mpr
    intro z hz
    rw [hGval]
    exact image_eq_zero_of_notMem_tsupport hz
  let g : supportedHolder (E := Phase n) K := ⟨G,hGK⟩
  let w : COne ℂ (Phase n) := standardHolderInverse hK g
  have hwK : w∈markedModel K := by
    refine ⟨standardHolderInverse_zero hK g,?_⟩
    have he : standardJetCR w=g.val := standardHolderInverse_residual hK g
    change standardJetCR w ∈ supportedHolder K
    rw [he]
    exact g.property
  let v : markedModel (E := Phase n) K := ⟨w,hwK⟩
  have hv0 : cValue v.val 0=0 := standardHolderInverse_zero hK g
  have hd : Differentiable ℂ (fun z => u z-cValue v.val z) :=
    inverse_correction_holomorphic hu.1 hK g hGval
  obtain ⟨a,ha,hau⟩ := hu.2.2.2.2
  have hf := marked_reconstruction_from_correction v.val hd hau hu.2.2.1 hu.2.2.2.1 hv0
  exact ⟨K,hK,v,hf.1,fun h => ha (hf.2.symm.trans h)⟩

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
