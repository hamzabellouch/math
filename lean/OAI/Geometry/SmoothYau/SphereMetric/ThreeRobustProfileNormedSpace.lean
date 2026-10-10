import Mathlib
import OAI.Geometry.SmoothYau.Estimates.ExistsBoxIccSubsetOpen
import OAI.Geometry.SmoothYau.Estimates.ExistsExhaustibleSignedEnvelope
import OAI.Geometry.SmoothYau.Estimates.ThreeNoncancelNormedSpace
import OAI.Geometry.SmoothYau.Geometry.ExistsGlobalBoxAmplifiedProfile
import OAI.Geometry.SmoothYau.Geometry.ThreeLogNormedSpace

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold MeasureTheory Metric
open scoped Topology ContDiff InnerProductSpace
section LocalLogExtension
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
lemma exists_smooth_local_log {q : E → ℝ} (hq : ContDiff ℝ ∞ q) {x : E} (hx : q x ≠ 0) (c : ℝ) :
    ∃ f : E → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      f =ᶠ[𝓝 x] (fun y => c*Real.log (q y)) := by
  have hO : {y | q y ≠ 0} ∈ 𝓝 x := hq.continuous.continuousAt.eventually_ne hx
  obtain ⟨r,hr,hs⟩ := Metric.mem_nhds_iff.mp hO
  let χ : ContDiffBump x := ⟨r/4,r/2,by positivity,by linarith⟩
  have hχ : tsupport χ ⊆ {y | q y ≠ 0} := by
    rw [χ.tsupport_eq]
    exact (closedBall_subset_ball (half_lt_self hr)).trans hs
  let f : E → ℝ := fun y => χ y*(c*Real.log (q y))
  have hf : ContDiff ℝ ∞ f := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ tsupport χ
    · exact χ.contDiffAt.mul (contDiffAt_const.mul (hq.contDiffAt.log (hχ hy)))
    · apply (contDiffAt_const (c:=(0:ℝ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
      simp [f,hz]
  refine ⟨f,hf,χ.hasCompactSupport.mul_right,?_⟩
  filter_upwards [χ.eventuallyEq_one] with y hy
  simp [f,hy]

lemma actual_strict_region_open (g : SmoothMetric E E) {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    IsOpen {x | coordinateMetricGradient g f x ≠ 0 ∧ actualProfileStrict g f x} := by
  have hJ : Continuous (fun x => (x,actualCoordinateHessian g f x,fderiv ℝ f x)) :=
    continuous_id.prodMk ((continuous_coordinateCovariantSecond _
      (contDiff_metricChristoffel g).continuous hf).prodMk
      (hf.continuous_fderiv (by simp)))
  have hh := (isOpen_metricJetStrict g).preimage hJ
  change IsOpen {x | metricJetStrict g (x,actualCoordinateHessian g f x,fderiv ℝ f x)} at hh
  simpa only [metricJetStrict_actual] using hh
lemma exists_local_strict_ball (g : SmoothMetric E E) {f : E → ℝ} (hf : ContDiff ℝ ∞ f) {x : E}
    (hx : coordinateMetricGradient g f x ≠ 0 ∧ actualProfileStrict g f x) :
    ∃ r>0, ∀ y ∈ closedBall x r,
      coordinateMetricGradient g f y ≠ 0 ∧ actualProfileStrict g f y := by
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp ((actual_strict_region_open g hf).mem_nhds hx)
  exact ⟨r/2,half_pos hr,fun y hy => hsub (closedBall_subset_ball (half_lt_self hr) hy)⟩
end LocalLogExtension

local instance threeLocalNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
local instance threeLocalContinuousSMul : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
lemma exists_three_local_strict_profile (p : ThreeManifold) (c : ℝ)
    (hx : (p.1:Euclidean 3) 0 ≠ 0) (hy : (p.1:Euclidean 3) 1=0)
    (hxlt : ((p.1:Euclidean 3) 0)^2<1) (hc : 0<c) (hc1 : c<1) :
    ∃ f : ThreeModel → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      f =ᶠ[𝓝 0] threeLogEnvelope p c ∧ ∃ r>0, ∀ y ∈ closedBall 0 r,
      coordinateMetricGradient (threeChartMetric threeBackgroundMetric p) f y ≠ 0 ∧
      actualProfileStrict (threeChartMetric threeBackgroundMetric p) f y := by
  have hq : threeRadiusSq p 0 ≠ 0 := by simp [threeRadiusSq_zero,hy,pow_ne_zero 2 hx]
  obtain ⟨f,hf,hfc,he⟩ := exists_smooth_local_log (threeRadiusSq_smooth p) hq (c/2)
  have he : f =ᶠ[𝓝 0] threeLogEnvelope p c := he
  have hj := actualJet_eventuallyEq (threeChartMetric threeBackgroundMetric p) he
  have hh := threeLogEnvelope_strict p c hx hy hxlt hc hc1
  have hf0 : coordinateMetricGradient (threeChartMetric threeBackgroundMetric p) f 0 ≠ 0 ∧
      actualProfileStrict (threeChartMetric threeBackgroundMetric p) f 0 := by
    rw [hj.1,hj.2.2.1]
    exact hh
  obtain ⟨r,hr,hstrict⟩ := exists_local_strict_ball _ hf hf0
  exact ⟨f,hf,hfc,he,r,hr,hstrict⟩
end


section
open Set Filter Function Manifold MeasureTheory Metric
open scoped Topology ContDiff InnerProductSpace
local instance threeCenterNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
local instance threeCenterContinuousSMul : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul

def threeProfilePoint : Sphere 2 :=
  ⟨(WithLp.toLp 2 ![(3/5:ℝ),0,4/5] : Euclidean 3), by
    rw [Metric.mem_sphere,dist_zero_right]
    have h := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ)
      (WithLp.toLp 2 ![(3/5:ℝ),0,4/5] : Euclidean 3)
    norm_num [Fin.sum_univ_succ,Real.norm_eq_abs,sq_abs] at h
    rcases h with h | h
    · exact h
    · nlinarith [norm_nonneg (WithLp.toLp 2 ![(3/5:ℝ),0,4/5] : Euclidean 3)]⟩
def threeProfileCenter : ThreeManifold := (threeProfilePoint,1)
lemma threeProfilePoint_zero : (threeProfilePoint:Euclidean 3) 0 = 3/5 := rfl
lemma threeProfilePoint_one : (threeProfilePoint:Euclidean 3) 1 = 0 := rfl
lemma threeProfilePoint_two : (threeProfilePoint:Euclidean 3) 2 = 4/5 := rfl

def threeEnvelopeExponent : ℝ := (Real.sqrt 2)⁻¹
lemma threeEnvelopeExponent_pos : 0<threeEnvelopeExponent := by
  exact inv_pos.mpr (Real.sqrt_pos.mpr (by norm_num))
lemma threeEnvelopeExponent_lt : threeEnvelopeExponent<1 := by
  unfold threeEnvelopeExponent
  have h : 1<Real.sqrt 2 := by nlinarith [Real.sq_sqrt (show (0:ℝ)≤2 by norm_num),Real.sqrt_nonneg 2]
  exact (inv_lt_one₀ (lt_trans zero_lt_one h)).mpr h
lemma threeEnvelopeExponent_mul : threeEnvelopeExponent*Real.sqrt 2=1 := by
  exact inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr (by norm_num))

theorem exists_three_profile_seed :
    ∃ f : ThreeModel → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      f =ᶠ[𝓝 0] threeLogEnvelope threeProfileCenter threeEnvelopeExponent ∧
      ∃ r>0, ∀ y ∈ closedBall 0 r,
        coordinateMetricGradient (threeChartMetric threeBackgroundMetric threeProfileCenter) f y ≠ 0 ∧
        actualProfileStrict (threeChartMetric threeBackgroundMetric threeProfileCenter) f y := by
  apply exists_three_local_strict_profile threeProfileCenter threeEnvelopeExponent
  · norm_num [threeProfileCenter,threeProfilePoint_zero]
  · exact threeProfilePoint_one
  · norm_num [threeProfileCenter,threeProfilePoint_zero]
  · exact threeEnvelopeExponent_pos
  · exact threeEnvelopeExponent_lt

theorem exists_three_amplified_profile (T : ℝ) {ε : ℝ} (hε : 0<ε) :
    ∃ f v : ThreeModel → ℝ, ∃ r>0,
      ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      f =ᶠ[𝓝 0] threeLogEnvelope threeProfileCenter threeEnvelopeExponent ∧
      ContDiff ℝ ∞ v ∧ HasCompactSupport v ∧ tsupport (fun x => v x-f x) ⊆ ball 0 r ∧
      (∀ x, |v x-f x|<ε) ∧
      (∀ x ∈ closedBall 0 r,
        coordinateMetricGradient (threeChartMetric threeBackgroundMetric threeProfileCenter) v x ≠ 0 ∧
        actualProfileStrict (threeChartMetric threeBackgroundMetric threeProfileCenter) v x) ∧
      T < actualProfileMass (threeChartMetric threeBackgroundMetric threeProfileCenter) v volume (ball 0 r) := by
  obtain ⟨f,hf,hfc,hfe,r,hr,hstrict⟩ := exists_three_profile_seed
  have hcl : closure (ball (0:ThreeModel) r) = closedBall 0 r := closure_ball 0 hr.ne'
  have hvb : volume (ball (0:ThreeModel) r) ≠ 0 := (measure_ball_pos volume 0 hr).ne'
  obtain ⟨v,hv,hvc,hvs,hv0,hvp,hvm⟩ := actual_metric_profile_amplification threeModel_finrank
    (threeChartMetric threeBackgroundMetric threeProfileCenter) hf isOpen_ball
    (by rw [hcl]; exact isCompact_closedBall 0 r)
    (fun x hx => (hstrict x (hcl ▸ hx)).1)
    (fun x hx => (hstrict x (hcl ▸ hx)).2) volume hvb T hε
  have hvc' : HasCompactSupport v := by
    have he : (fun x => v x-f x)+f=v := by ext x; simp
    exact he ▸ hvc.add hfc
  exact ⟨f,v,r,hr,hf,hfc,hfe,hv,hvc',hvs,hv0,fun x hx => hvp x (hcl.symm ▸ hx),hvm⟩
end


section
open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff InnerProductSpace
section LinearStrictTransport
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
lemma linearPullbackMetric_trace (g : SmoothMetric E E) (L : F ≃L[ℝ] E)
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x v : F) :
    actualProfileTraceForm (linearPullbackMetric g L) (f ∘ L) x v v =
      actualProfileTraceForm g f (L x) (L v) (L v) := by
  simp only [actualProfileTraceForm,metricProfileTraceForm_apply]
  rw [linearPullbackMetric_flat,linearPullbackMetric_hessian g L hf,
    linearPullbackMetric_flat,linearPullbackMetric_hessian g L hf,
    linearPullbackMetric_gradient g L hf]
lemma linearPullbackMetric_strict (g : SmoothMetric E E) (L : F ≃L[ℝ] E)
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x : F)
    (h : coordinateMetricGradient g f (L x) ≠ 0 ∧ actualProfileStrict g f (L x)) :
    coordinateMetricGradient (linearPullbackMetric g L) (f ∘ L) x ≠ 0 ∧
      actualProfileStrict (linearPullbackMetric g L) (f ∘ L) x := by
  constructor
  · intro hz
    have hh := linearPullbackMetric_gradient g L hf x
    rw [hz,map_zero] at hh
    exact h.1 hh.symm
  · have hh := h.2
    rw [actualProfileStrict,quadraticPlaneStrict_iff_nonzero] at hh
    rcases hh with ⟨v,hv,hd,ht⟩
    rw [actualProfileStrict,quadraticPlaneStrict_iff_nonzero]
    refine ⟨L.symm v,by simpa using L.symm.injective.ne hv,?_,?_⟩
    · rw [InnerProductSpace.toDual_symm_apply,fderiv_linearEquiv_comp hf L,L.apply_symm_apply]
      simpa only [InnerProductSpace.toDual_symm_apply] using hd
    · rw [linearPullbackMetric_trace g L hf,L.apply_symm_apply]
      exact ht
end LinearStrictTransport
local instance threeTransportNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
local instance threeTransportContinuousSMul : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul

def threeNormalEquiv : NormalWaveSpace ≃L[ℝ] ThreeModel := by
  letI : ContinuousSMul ℝ NormalWaveSpace := IsBoundedSMul.continuousSMul
  exact ContinuousLinearEquiv.ofFinrankEq (by simpa [NormalWaveSpace] using threeModel_finrank.symm)
def threeNormalMetric : SmoothMetric NormalWaveSpace NormalWaveSpace :=
  linearPullbackMetric (threeChartMetric threeBackgroundMetric threeProfileCenter) threeNormalEquiv

theorem exists_three_normal_seed :
    ∃ f : NormalWaveSpace → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      ∃ r>0, ∀ y ∈ closedBall 0 r,
        coordinateMetricGradient threeNormalMetric f y ≠ 0 ∧ actualProfileStrict threeNormalMetric f y := by
  obtain ⟨f,hf,hfc,he,r,hr,hs⟩ := exists_three_profile_seed
  have h0 := linearPullbackMetric_strict (threeChartMetric threeBackgroundMetric threeProfileCenter)
    threeNormalEquiv hf 0 (by simpa using hs 0 (mem_closedBall_self hr.le))
  obtain ⟨s,hs,ht⟩ := exists_local_strict_ball threeNormalMetric (hf.comp threeNormalEquiv.contDiff) h0
  refine ⟨f ∘ threeNormalEquiv,hf.comp threeNormalEquiv.contDiff,?_,s,hs,ht⟩
  exact hfc.comp_homeomorph threeNormalEquiv.toHomeomorph
end


section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff InnerProductSpace
local instance threeGlobalLogNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
local instance threeGlobalLogContinuousSMul : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul

def threeCouplingRadius : ℝ := 1/100
def threeGlobalRadius (p : ThreeManifold) : ℝ :=
  max ‖productA p.1‖ (threeCouplingRadius*‖productB p.1‖)
def threeGlobalLog (p : ThreeManifold) : ℝ :=
  threeEnvelopeExponent*Real.log (threeGlobalRadius p)
lemma threeGlobalRadius_lower (p : ThreeManifold) : (1/200:ℝ) ≤ threeGlobalRadius p := by
  have ha := Complex.normSq_eq_norm_sq (productA p.1)
  have hb := Complex.normSq_eq_norm_sq (productB p.1)
  simp only [Complex.normSq_apply,productA_re,productA_im,productB_re,productB_im] at ha hb
  have hs := productSphere_norm_sq p.1
  by_contra hn
  have hn : threeGlobalRadius p < 1/200 := lt_of_not_ge hn
  have hA := (le_max_left ‖productA p.1‖ (threeCouplingRadius*‖productB p.1‖)).trans_lt hn
  have hB := (le_max_right ‖productA p.1‖ (threeCouplingRadius*‖productB p.1‖)).trans_lt hn
  dsimp [threeCouplingRadius] at hB
  have hB' : ‖productB p.1‖<1/2 := by linarith
  have hA' : ‖productA p.1‖<1/2 := by linarith
  nlinarith [norm_nonneg (productA p.1), norm_nonneg (productB p.1),sq_nonneg ((p.1:Euclidean 3) 0)]
lemma threeGlobalRadius_pos (p : ThreeManifold) : 0<threeGlobalRadius p :=
  lt_of_lt_of_le (by norm_num) (threeGlobalRadius_lower p)
lemma threeGlobalRadius_le_one (p : ThreeManifold) : threeGlobalRadius p≤1 := by
  apply max_le (productA_norm_le p.1)
  have hb:=productB_norm_le p.1
  dsimp [threeCouplingRadius]
  nlinarith [norm_nonneg (productB p.1)]
lemma threeGlobalRadius_continuous : Continuous threeGlobalRadius := by
  have hA : Continuous (fun p : ThreeManifold => productA p.1) :=
    (planarLinear _ _).continuous.comp (continuous_subtype_val.comp continuous_fst)
  have hB : Continuous (fun p : ThreeManifold => productB p.1) :=
    (planarLinear _ _).continuous.comp (continuous_subtype_val.comp continuous_fst)
  exact hA.norm.max (continuous_const.mul hB.norm)
lemma threeGlobalLog_continuous : Continuous threeGlobalLog :=
  continuous_const.mul (threeGlobalRadius_continuous.log (fun p => (threeGlobalRadius_pos p).ne'))
lemma threeGlobalLog_bounds (p : ThreeManifold) :
    threeEnvelopeExponent*Real.log (1/200) ≤ threeGlobalLog p ∧ threeGlobalLog p≤0 := by
  constructor
  · exact mul_le_mul_of_nonneg_left (Real.log_le_log (by norm_num) (threeGlobalRadius_lower p))
      threeEnvelopeExponent_pos.le
  · exact mul_nonpos_of_nonneg_of_nonpos threeEnvelopeExponent_pos.le
      (Real.log_nonpos (threeGlobalRadius_pos p).le (threeGlobalRadius_le_one p))
lemma three_chart_symm_zero (p : ThreeManifold) : (chartAt ThreeModel p).symm 0=p := by
  rw [←three_chart_center p]
  exact (chartAt ThreeModel p).left_inv (mem_chart_source _ _)
lemma three_chart_symm_continuous (p : ThreeManifold) : Continuous (chartAt ThreeModel p).symm := by
  exact continuousOn_univ.mp (by simpa only [OpenPartialHomeomorph.symm_source,three_chart_target] using
    (chartAt ThreeModel p).symm.continuousOn)
lemma threeRadiusSq_eq_norm (p : ThreeManifold) (y : ThreeModel) :
    threeRadiusSq p y=‖productA ((chartAt ThreeModel p).symm y).1‖^2 := by
  have hh := congrArg (fun z : ThreeAmbient => z.fst) (congrFun (three_chart_symm p) y)
  change (((chartAt ThreeModel p).symm y).1:Euclidean 3)=threeSphereMap p y at hh
  rw [threeRadiusSq,threeSphereCoord,threeSphereCoord,productAxis_coord,productAxis_coord,←hh]
  have hn := Complex.normSq_eq_norm_sq (productA ((chartAt ThreeModel p).symm y).1)
  simpa only [Complex.normSq_apply,productA_re,productA_im,pow_two] using hn
lemma threeLogEnvelope_eq (p : ThreeManifold) (c : ℝ) (y : ThreeModel) :
    threeLogEnvelope p c y=c*Real.log ‖productA ((chartAt ThreeModel p).symm y).1‖ := by
  rw [threeLogEnvelope,threeRadiusSq_eq_norm,Real.log_pow]
  norm_num
  ring
lemma threeGlobalLog_local :
    threeGlobalLog ∘ (chartAt ThreeModel threeProfileCenter).symm =ᶠ[𝓝 0]
      threeLogEnvelope threeProfileCenter threeEnvelopeExponent := by
  have hA : Continuous (fun y : ThreeModel => ‖productA ((chartAt ThreeModel threeProfileCenter).symm y).1‖) :=
    ((planarLinear _ _).continuous.comp (continuous_subtype_val.comp
      (continuous_fst.comp (three_chart_symm_continuous _)))).norm
  have hB : Continuous (fun y : ThreeModel => threeCouplingRadius*‖productB ((chartAt ThreeModel threeProfileCenter).symm y).1‖) :=
    continuous_const.mul (((planarLinear _ _).continuous.comp (continuous_subtype_val.comp
      (continuous_fst.comp (three_chart_symm_continuous _)))).norm)
  have hA0 : ‖productA threeProfileCenter.1‖=3/5 := by
    have he : productA threeProfileCenter.1=(3/5:ℂ) := by
      apply Complex.ext <;> simp [productA_re,productA_im,threeProfileCenter,threeProfilePoint_zero,threeProfilePoint_one]
    rw [he]; norm_num
  have h0 : threeCouplingRadius*‖productB ((chartAt ThreeModel threeProfileCenter).symm 0).1‖<
      ‖productA ((chartAt ThreeModel threeProfileCenter).symm 0).1‖ := by
    rw [three_chart_symm_zero,hA0]
    have hb:=productB_norm_le threeProfileCenter.1
    dsimp [threeCouplingRadius]
    nlinarith [norm_nonneg (productB threeProfileCenter.1)]
  filter_upwards [(hB.continuousAt.sub hA.continuousAt).eventually_lt_const
    (show threeCouplingRadius*‖productB ((chartAt ThreeModel threeProfileCenter).symm 0).1‖-
      ‖productA ((chartAt ThreeModel threeProfileCenter).symm 0).1‖<0 by linarith)] with y hy
  change threeCouplingRadius*‖productB ((chartAt ThreeModel threeProfileCenter).symm y).1‖-
    ‖productA ((chartAt ThreeModel threeProfileCenter).symm y).1‖<0 at hy
  rw [threeLogEnvelope_eq]
  dsimp [threeGlobalLog,threeGlobalRadius,Function.comp_apply]
  rw [max_eq_left (by linarith : threeCouplingRadius*‖productB ((chartAt ThreeModel threeProfileCenter).symm y).1‖≤
    ‖productA ((chartAt ThreeModel threeProfileCenter).symm y).1‖)]
end


section
open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff InnerProductSpace
local instance threeNormalEnvelopeNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
local instance threeNormalEnvelopeContinuousSMul : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul

def threeNormalInv : NormalWaveSpace → ThreeManifold :=
  (chartAt ThreeModel threeProfileCenter).symm ∘ threeNormalEquiv
def threeNormalGlue (C : ℝ) (f : NormalWaveSpace → ℝ) : ThreeManifold → ℝ :=
  fun p => C+manifoldChartPush threeProfileCenter ((fun y => f y-C) ∘ threeNormalEquiv.symm) p
lemma threeNormalGlue_chart (C : ℝ) (f : NormalWaveSpace → ℝ) :
    threeNormalGlue C f ∘ threeNormalInv=f := by
  funext y
  dsimp [threeNormalGlue,threeNormalInv]
  rw [manifoldChartPush_apply _ _ (by rw [three_chart_target]; trivial)]
  simp
lemma threeNormalGlue_smooth (C : ℝ) {f : NormalWaveSpace → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport (fun y => f y-C)) :
    ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ (threeNormalGlue C f) := by
  exact contMDiff_const.add (contMDiff_manifoldChartPush _
    ((hf.sub contDiff_const).comp threeNormalEquiv.symm.contDiff)
    (hc.comp_homeomorph threeNormalEquiv.symm.toHomeomorph)
    (by rw [three_chart_target]; exact subset_univ _))
lemma threeNormalGlue_tsupport (C : ℝ) {f : NormalWaveSpace → ℝ}
    (hc : HasCompactSupport (fun y => f y-C)) {K : Set NormalWaveSpace}
    (hK : tsupport (fun y => f y-C) ⊆ K) :
    tsupport (fun p => threeNormalGlue C f p-C) ⊆ threeNormalInv '' K := by
  have he : (fun p => threeNormalGlue C f p-C)=
      manifoldChartPush threeProfileCenter ((fun y => f y-C) ∘ threeNormalEquiv.symm) := by
    funext p; simp [threeNormalGlue]
  rw [he]
  intro p hp
  obtain ⟨y,hy,rfl⟩ := manifoldChartPush_tsupport _
    (hc.comp_homeomorph threeNormalEquiv.symm.toHomeomorph)
    (by rw [three_chart_target]; exact subset_univ _) hp
  rw [tsupport_comp_eq_preimage _ threeNormalEquiv.symm.toHomeomorph] at hy
  refine ⟨threeNormalEquiv.symm y,hK hy,?_⟩
  simp [threeNormalInv]
lemma threeNormalGlue_exterior (C δ : ℝ) {f l : NormalWaveSpace → ℝ}
    {L : ThreeManifold → ℝ} {K : Set NormalWaveSpace}
    (heL : l=L ∘ threeNormalInv) (hmin : ∀ p, C≤L p-δ)
    (hext : ∀ y ∉ K, f y≤l y-δ) :
    ∀ p ∉ threeNormalInv '' K, threeNormalGlue C f p≤L p-δ := by
  intro p hp
  by_cases hs : p ∈ (chartAt ThreeModel threeProfileCenter).source
  · let y := threeNormalEquiv.symm (chartAt ThreeModel threeProfileCenter p)
    have hey : threeNormalInv y=p := by simp [threeNormalInv,y,(chartAt ThreeModel threeProfileCenter).left_inv hs]
    have hy : y ∉ K := fun hh => hp ⟨y,hh,hey⟩
    have hec := congrFun (threeNormalGlue_chart C f) y
    have hec' : threeNormalGlue C f p=f y := by
      simpa only [Function.comp_apply,hey] using hec
    rw [hec']
    simpa only [heL,Function.comp_apply,hey] using hext y hy
  · simpa [threeNormalGlue,manifoldChartPush,Set.indicator_of_notMem hs] using hmin p

theorem exists_three_normal_envelope :
    ∃ C R δ : ℝ, 0<R ∧ 0<δ ∧ δ≤1/2 ∧ ∃ f : NormalWaveSpace → ℝ,
      ContDiff ℝ ∞ f ∧ HasCompactSupport (fun y => f y-C) ∧
      tsupport (fun y => f y-C) ⊆ closedBall 0 (3*R/4) ∧
      (∀ y ∈ closedBall 0 (R/3), coordinateMetricGradient threeNormalMetric f y ≠ 0 ∧
        actualProfileStrict threeNormalMetric f y) ∧
      (∀ y ∈ closedBall 0 (R/8), f y=threeGlobalLog (threeNormalInv y)+δ) ∧
      (∀ y ∉ closedBall 0 (R/3), f y≤threeGlobalLog (threeNormalInv y)-δ) ∧
      (∀ p, C≤threeGlobalLog p-δ) := by
  obtain ⟨f,hf,hfc,he,r,hr,hs⟩ := exists_three_profile_seed
  let F := f ∘ threeNormalEquiv
  have hF : ContDiff ℝ ∞ F := hf.comp threeNormalEquiv.contDiff
  have h0 := linearPullbackMetric_strict (threeChartMetric threeBackgroundMetric threeProfileCenter)
    threeNormalEquiv hf 0 (by simpa using hs 0 (mem_closedBall_self hr.le))
  obtain ⟨r₁,hr₁,hs₁⟩ := exists_local_strict_ball threeNormalMetric hF h0
  have hgerm : F =ᶠ[𝓝 0] threeGlobalLog ∘ threeNormalInv := by
    have ht : Tendsto threeNormalEquiv (𝓝 (0:NormalWaveSpace)) (𝓝 (0:ThreeModel)) :=
      by simpa using (threeNormalEquiv.continuous.continuousAt (x:=0)).tendsto
    exact (he.trans threeGlobalLog_local.symm).comp_tendsto ht
  obtain ⟨r₂,hr₂,hs₂⟩ := Metric.mem_nhds_iff.mp hgerm
  let R := min r₁ (r₂/2)
  have hR : 0<R := lt_min hr₁ (half_pos hr₂)
  let C := threeEnvelopeExponent*Real.log (1/200)-1
  obtain ⟨δ,hδ,hδ1,φ,hφ,hφc,hφs,hφstrict,hφin,hφout⟩ :=
    exists_compact_signed_envelope threeNormalMetric hF hR C
      (fun y => by dsimp [C]; linarith [(threeGlobalLog_bounds (threeNormalInv y)).1])
      (fun y hy => hs₂ (closedBall_subset_ball
        ((min_le_right _ _).trans_lt (half_lt_self hr₂)) hy))
      (fun y hy => hs₁ y (closedBall_subset_closedBall (min_le_left _ _) hy))
  exact ⟨C,R,δ,hR,hδ,hδ1,φ,hφ,hφc,hφs,hφstrict,hφin,hφout,
    fun p => by dsimp [C]; linarith [(threeGlobalLog_bounds p).1]⟩
end


section
open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff InnerProductSpace
local instance threeGlobalProfileNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
local instance threeGlobalProfileContinuousSMul : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul

theorem exists_three_global_profile_family :
    ∃ C R δ : ℝ, 0<R ∧ 0<δ ∧ ∃ I : Box (Fin 3),
      normalWaveEquiv '' Box.Icc I ⊆ closedBall 0 (R/8) ∧
      ∀ T : ℝ, ∃ Φ : ThreeManifold → ℝ,
        ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ Φ ∧
        ContDiff ℝ ∞ (Φ ∘ threeNormalInv) ∧
        tsupport (fun p => Φ p-C) ⊆ threeNormalInv '' closedBall 0 (3*R/4) ∧
        (∀ y ∈ closedBall 0 (R/3),
          coordinateMetricGradient threeNormalMetric (Φ ∘ threeNormalInv) y ≠ 0 ∧
          actualProfileStrict threeNormalMetric (Φ ∘ threeNormalInv) y) ∧
        (∀ y ∈ normalWaveEquiv '' Box.Icc I,
          threeGlobalLog (threeNormalInv y)+δ/2 < Φ (threeNormalInv y)) ∧
        (∀ p ∉ threeNormalInv '' closedBall 0 (R/3), Φ p≤threeGlobalLog p-δ) ∧
        T < ∫ x in Box.Icc I, profileFrequencyScale threeNormalMetric
          (Φ ∘ threeNormalInv) (normalWaveEquiv x) := by
  obtain ⟨C,R,δ,hR,hδ,hδ1,φ,hφ,hφc,hφs,hstrict,hin,hout,hmin⟩ :=
    exists_three_normal_envelope
  have hne : (normalWaveEquiv ⁻¹' ball (0:NormalWaveSpace) (R/8)).Nonempty := by
    refine ⟨0,?_⟩
    simpa only [mem_preimage,map_zero,mem_ball,dist_self] using (show 0<R/8 by positivity)
  obtain ⟨I,hI⟩ := exists_box_Icc_subset_open
    (isOpen_ball.preimage normalWaveEquiv.continuous) hne
  have hIs : normalWaveEquiv '' Box.Icc I ⊆ closedBall 0 (R/8) := by
    rintro y ⟨x,hx,rfl⟩
    exact ball_subset_closedBall (hI hx)
  have hIK : normalWaveEquiv '' Box.Icc I ⊆ closedBall 0 (R/3) :=
    hIs.trans (closedBall_subset_closedBall (by linarith))
  refine ⟨C,R,δ,hR,hδ,I,hIs,?_⟩
  intro T
  obtain ⟨ψ,hψ,hψc,hψs,hclose,hinside,hmass⟩ := exists_box_amplified_profile
    threeNormalMetric I hφ (fun y hy => (hstrict y (hIK hy)).1)
    (fun y hy => (hstrict y (hIK hy)).2) T (half_pos hδ)
  have hd : (fun y => ψ y-C)=(fun y => ψ y-φ y)+(fun y => φ y-C) := by
    funext y; simp
  have hc : HasCompactSupport (fun y => ψ y-C) := hd ▸ hψc.add hφc
  have hsupport : tsupport (fun y => ψ y-C) ⊆ closedBall 0 (3*R/4) := by
    rw [hd]
    apply (tsupport_add _ _).trans (union_subset ?_ hφs)
    exact hψs.trans ((image_mono I.Ioo_subset_Icc).trans
      (hIs.trans (closedBall_subset_closedBall (by linarith))))
  have heoff (y : NormalWaveSpace) (hy : y ∉ normalWaveEquiv '' Box.Icc I) :
      ψ =ᶠ[𝓝 y] φ := by
    apply profile_eq_germ_of_not_tsupport
    exact fun hs => hy ((image_mono I.Ioo_subset_Icc) (hψs hs))
  have hψstrict : ∀ y ∈ closedBall 0 (R/3),
      coordinateMetricGradient threeNormalMetric ψ y ≠ 0 ∧ actualProfileStrict threeNormalMetric ψ y := by
    intro y hy
    by_cases hz : y ∈ normalWaveEquiv '' Box.Icc I
    · exact hinside y hz
    · have hj := actualJet_eventuallyEq threeNormalMetric (heoff y hz)
      rw [hj.1,hj.2.2.1]
      exact hstrict y hy
  have hψout : ∀ y ∉ closedBall 0 (R/3), ψ y≤threeGlobalLog (threeNormalInv y)-δ := by
    intro y hy
    have hz : y ∉ normalWaveEquiv '' Box.Icc I := fun hh => hy (hIK hh)
    rw [(heoff y hz).self_of_nhds]
    exact hout y hy
  let Φ := threeNormalGlue C ψ
  have hchart : Φ ∘ threeNormalInv=ψ := threeNormalGlue_chart C ψ
  refine ⟨Φ,threeNormalGlue_smooth C hψ hc,?_,threeNormalGlue_tsupport C hc hsupport,?_,?_,?_,?_⟩
  · rw [hchart]; exact hψ
  · rw [hchart]; exact hψstrict
  · intro y hy
    have hcl := (abs_lt.mp (hclose y)).1
    have hbase := hin y (hIs hy)
    have he : Φ (threeNormalInv y)=ψ y := congrFun hchart y
    rw [he]
    linarith
  · exact threeNormalGlue_exterior C δ rfl hmin hψout
  · rw [hchart]; exact hmass
end


section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff
local instance threeGapNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
local instance threeGapContinuousSMul : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
lemma productWaveFrequency_scaled_bounds {k : ℕ} (hk : 1≤k) :
    (k:ℝ)-1 ≤ productWaveFrequency k*threeEnvelopeExponent ∧
      productWaveFrequency k*threeEnvelopeExponent ≤ k := by
  have hn : (0:ℝ)≤k := Nat.cast_nonneg _
  have hb := productWaveFrequency_bounds hk
  have hs := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  have hp := Real.sqrt_pos.mpr (show (0:ℝ)<2 by norm_num)
  have he := productWaveFrequency_equation k
  dsimp [productFrequency] at he
  have hsK : (Real.sqrt 2*(k:ℝ))^2=2*(k:ℝ)^2 := by rw [mul_pow,hs]
  have hupper : productWaveFrequency k≤Real.sqrt 2*(k:ℝ) := by
    have hv : productWaveFrequency k ^ 2 ≤ 2*(k:ℝ)^2 := by nlinarith [hb.1]
    exact (sq_le_sq₀ (hn.trans hb.1) (mul_nonneg hp.le hn)).mp (by simpa only [hsK] using hv)
  have hlower : Real.sqrt 2*(k:ℝ)≤productWaveFrequency k+1 := by
    have hh := Real.sq_sqrt (add_nonneg (productFrequency_nonneg k) zero_le_one)
    have hz := Real.sqrt_nonneg (productFrequency k+1)
    dsimp [productWaveFrequency,productFrequency] at hh hz ⊢
    nlinarith [sq_nonneg (Real.sqrt (2*(k:ℝ)^2+(k:ℝ)+1)-Real.sqrt 2*(k:ℝ))]
  have hc := threeEnvelopeExponent_pos
  have hc1 := threeEnvelopeExponent_lt
  have hmul := threeEnvelopeExponent_mul
  constructor
  · have hh := mul_le_mul_of_nonneg_right hlower hc.le
    nlinarith
  · have hh := mul_le_mul_of_nonneg_right hupper hc.le
    nlinarith

lemma three_radius_pow_eq_exp (p : ThreeManifold) (k : ℕ) :
    threeGlobalRadius p^k=Real.exp ((k:ℝ)*Real.log (threeGlobalRadius p)) := by
  rw [Real.exp_nat_mul,Real.exp_log (threeGlobalRadius_pos p)]

lemma three_positive_envelope_gap (p : ThreeManifold) {k : ℕ} (hk : 1≤k)
    {φ δ : ℝ} (hgap : threeGlobalLog p+δ≤φ) :
    threeGlobalRadius p^k ≤ Real.exp (productWaveFrequency k*(φ-δ)) := by
  have hc := (productWaveFrequency_scaled_bounds hk).2
  have hn := (Nat.cast_nonneg k).trans (productWaveFrequency_bounds hk).1
  have hl := Real.log_nonpos (threeGlobalRadius_pos p).le (threeGlobalRadius_le_one p)
  rw [three_radius_pow_eq_exp]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonpos_right hc hl
  have hg := mul_le_mul_of_nonneg_left hgap hn
  dsimp [threeGlobalLog] at hg
  nlinarith

lemma three_negative_envelope_gap (p : ThreeManifold) {k : ℕ} (hk : 1≤k)
    {φ δ : ℝ} (hδ : 0≤δ) (hgap : φ≤threeGlobalLog p-δ) :
    Real.exp (productWaveFrequency k*φ) ≤
      200*(threeGlobalRadius p)^k*Real.exp (-(k:ℝ)*δ) := by
  have hc := (productWaveFrequency_scaled_bounds hk).1
  have hb := productWaveFrequency_bounds hk
  have hn := (Nat.cast_nonneg k).trans hb.1
  have hl := Real.log_nonpos (threeGlobalRadius_pos p).le (threeGlobalRadius_le_one p)
  have hlb := Real.log_le_log (show (0:ℝ)<1/200 by norm_num) (threeGlobalRadius_lower p)
  have hlog : -Real.log (threeGlobalRadius p) ≤ Real.log 200 := by
    have he : Real.log (1/200:ℝ) = -Real.log 200 := by rw [one_div,Real.log_inv]
    rw [he] at hlb
    linarith
  have hex : productWaveFrequency k*φ ≤ Real.log 200+(k:ℝ)*Real.log (threeGlobalRadius p)-(k:ℝ)*δ := by
    have h1 := mul_le_mul_of_nonpos_right hc hl
    have h2 := mul_le_mul_of_nonneg_left hgap hn
    have h3 := mul_le_mul_of_nonneg_right hb.1 hδ
    dsimp [threeGlobalLog] at h2
    nlinarith
  calc
    _ ≤ Real.exp (Real.log 200+(k:ℝ)*Real.log (threeGlobalRadius p)-(k:ℝ)*δ) := Real.exp_le_exp.mpr hex
    _ = _ := by
      rw [show Real.log 200+(k:ℝ)*Real.log (threeGlobalRadius p)-(k:ℝ)*δ =
        (Real.log 200+(k:ℝ)*Real.log (threeGlobalRadius p))+(-(k:ℝ)*δ) by ring,
        Real.exp_add,Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<200),←three_radius_pow_eq_exp]
end


section
open Set Filter Manifold Metric
open scoped Topology ContDiff Matrix.Norms.Elementwise
local instance threeNeighborNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
local instance threeNeighborContinuousSMul : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
local instance threeNbDualNorm : NormedAddCommGroup (ThreeModel →L[ℝ] ℝ) := inferInstance
local instance threeNbDualSpace : NormedSpace ℝ (ThreeModel →L[ℝ] ℝ) := inferInstance
local instance threeNbFormNorm : NormedAddCommGroup (CoordinateForm ThreeModel) := inferInstance
local instance threeNbFormSpace : NormedSpace ℝ (CoordinateForm ThreeModel) := inferInstance
local instance threeNbDerivNorm : NormedAddCommGroup (ThreeModel →L[ℝ] CoordinateForm ThreeModel) := inferInstance
local instance threeNbDerivSpace : NormedSpace ℝ (ThreeModel →L[ℝ] CoordinateForm ThreeModel) := inferInstance
lemma three_metricCoefficients_smooth (g : SmoothMetric (ThreeModel) (ThreeManifold))
    (p : ThreeManifold) : ContDiff ℝ ∞ (metricCoefficients g p) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  exact contDiffOn_univ.mp (by
    simpa only [three_chart_target] using contDiffOn_metricCoefficient g p i j)

theorem three_metric_first_jet_neighborhood (g₀ : SmoothMetric (ThreeModel) (ThreeManifold))
    (p : ThreeManifold) {K : Set (ThreeModel)} (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ) :
    IsSmoothNeighborhood g₀ {g | ∀ x ∈ K,
      ‖selfMetricFlat (threeChartMetric g p) x-selfMetricFlat (threeChartMetric g₀ p) x‖ < δ ∧
      ‖fderiv ℝ (selfMetricFlat (threeChartMetric g p)) x-
        fderiv ℝ (selfMetricFlat (threeChartMetric g₀ p)) x‖ < δ} := by
  let : NormedAddCommGroup
      (Matrix (CoordIndex ThreeModel) (CoordIndex ThreeModel) ℝ →L[ℝ] CoordinateForm ThreeModel) :=
    inferInstanceAs (NormedAddCommGroup
      ((CoordIndex ThreeModel → CoordIndex ThreeModel → ℝ) →L[ℝ]
        (ThreeModel →L[ℝ] ThreeModel →L[ℝ] ℝ)))
  let L := metricMatrixFormCLM (E := ThreeModel)
  let ε := δ/(‖L‖+1)
  have hden : 0 < ‖L‖+1 := by positivity
  have hε : 0 < ε := div_pos hδ hden
  have hmul : ‖L‖*ε < δ := by
    calc
      ‖L‖*ε < (‖L‖+1)*ε := mul_lt_mul_of_pos_right (by linarith) hε
      _ = δ := by dsimp [ε]; field_simp
  let test : Fin 2 × CoordIndex (ThreeModel) × CoordIndex (ThreeModel) →
      CoordinateTest (ThreeModel) (ThreeManifold) := fun q =>
    { center := p, compactSet := K, isCompact := hK,
      inTarget := by rw [three_chart_target]; exact subset_univ K,
      order := q.1.val, row := q.2.1, column := q.2.2 }
  let tests := (Finset.univ : Finset (Fin 2 × CoordIndex (ThreeModel) × CoordIndex (ThreeModel))).toList.map test
  refine ⟨tests,ε,hε,?_⟩
  intro g hg x hx
  have htest (k : Fin 2) (i j : CoordIndex (ThreeModel)) : test (k,i,j) ∈ tests := by
    exact List.mem_map.mpr ⟨(k,i,j),by simp,rfl⟩
  have h₀ (i j : CoordIndex (ThreeModel)) :
      |metricCoefficients g p x i j-metricCoefficients g₀ p x i j| ≤ ε := by
    have hh := hg (test (0,i,j)) (htest 0 i j) x hx
    simpa only [test,Fin.val_zero,norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hh.le
  have h₁ (i j : CoordIndex (ThreeModel)) :
      ‖fderiv ℝ (fun y => metricCoefficients g p y i j-metricCoefficients g₀ p y i j) x‖ ≤ ε := by
    have hh := hg (test (1,i,j)) (htest 1 i j) x hx
    simpa only [test,Fin.val_one,norm_iteratedFDeriv_one] using hh.le
  have hb := metricMatrixForm_first_jet_bound
    ((three_metricCoefficients_smooth g p).differentiable (by simp) x)
    ((three_metricCoefficients_smooth g₀ p).differentiable (by simp) x) hε.le h₀ h₁
  have he (g : SmoothMetric (ThreeModel) (ThreeManifold)) :
      selfMetricFlat (threeChartMetric g p) = fun y => metricMatrixForm (metricCoefficients g p y) :=
    by
      ext y v w
      rw [threeChartMetric_selfFlat]
      rfl
  rw [he g,he g₀]
  exact ⟨hb.1.trans_lt hmul,hb.2.trans_lt hmul⟩

end


section
open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff InnerProductSpace
local instance threeRobustNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
local instance threeRobustContinuousSMul : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul

def threeNormalMetricOf (g : SmoothMetric ThreeModel ThreeManifold) :
    SmoothMetric NormalWaveSpace NormalWaveSpace :=
  linearPullbackMetric (threeChartMetric g threeProfileCenter) threeNormalEquiv

def ThreeCleanBall (R : ℝ) : Prop := ∀ y∈closedBall (0:NormalWaveSpace) R,
  1/2≤‖productA (threeNormalInv y).1‖ ∧ ‖productA (threeNormalInv y).1‖≤3/4
lemma threeNormalInv_clean_eventually : ∀ᶠ y : NormalWaveSpace in 𝓝 0,
    1/2≤‖productA (threeNormalInv y).1‖ ∧ ‖productA (threeNormalInv y).1‖≤3/4 := by
  have hA : Continuous (fun y : NormalWaveSpace => ‖productA (threeNormalInv y).1‖) :=
    ((planarLinear _ _).continuous.comp (continuous_subtype_val.comp
      (continuous_fst.comp ((three_chart_symm_continuous _).comp threeNormalEquiv.continuous)))).norm
  have h0 : ‖productA (threeNormalInv 0).1‖=3/5 := by
    have he : productA threeProfileCenter.1=(3/5:ℂ) := by
      apply Complex.ext <;> simp [productA_re,productA_im,threeProfileCenter,threeProfilePoint_zero,threeProfilePoint_one]
    simp only [threeNormalInv,Function.comp_apply,map_zero,three_chart_symm_zero,he]
    norm_num
  filter_upwards [hA.continuousAt.eventually_lt_const (show ‖productA (threeNormalInv 0).1‖<3/4 by rw [h0]; norm_num),
    hA.continuousAt.eventually_const_lt (show (1/2:ℝ)<‖productA (threeNormalInv 0).1‖ by rw [h0]; norm_num)] with y hu hl
  exact ⟨hl.le,hu.le⟩

theorem exists_three_robust_seed :
    ∃ C R : ℝ, 0<R ∧ ThreeCleanBall R ∧ ∃ F : NormalWaveSpace → ℝ,
      ContDiff ℝ ∞ F ∧ (∀ y ∈ closedBall 0 R, F y=threeGlobalLog (threeNormalInv y)) ∧
      (∀ p, C+1≤threeGlobalLog p) ∧
      ∃ N : Set (SmoothMetric ThreeModel ThreeManifold),
        IsSmoothNeighborhood threeBackgroundMetric N ∧ threeBackgroundMetric ∈ N ∧
        ∀ g ∈ N, ∀ y ∈ closedBall 0 R,
          coordinateMetricGradient (threeNormalMetricOf g) F y ≠ 0 ∧
          actualProfileStrict (threeNormalMetricOf g) F y := by
  obtain ⟨f,hf,hfc,he,r,hr,hs⟩ := exists_three_profile_seed
  obtain ⟨δ,hδ,hstable⟩ := compact_actual_strict_metric_stability
    (threeChartMetric threeBackgroundMetric threeProfileCenter) hf
    (isCompact_closedBall 0 r) hs
  let N : Set (SmoothMetric ThreeModel ThreeManifold) := {g | ∀ x ∈ closedBall 0 r,
    coordinateMetricGradient (threeChartMetric g threeProfileCenter) f x ≠ 0 ∧
    actualProfileStrict (threeChartMetric g threeProfileCenter) f x}
  have hN : IsSmoothNeighborhood threeBackgroundMetric N := by
    obtain ⟨tests,ε,hε,ht⟩ := three_metric_first_jet_neighborhood threeBackgroundMetric
      threeProfileCenter (isCompact_closedBall 0 r) hδ
    exact ⟨tests,ε,hε,fun g hg => hstable (threeChartMetric g threeProfileCenter) (ht g hg)⟩
  let F := f ∘ threeNormalEquiv
  have hF : ContDiff ℝ ∞ F := hf.comp threeNormalEquiv.contDiff
  have ht : Tendsto threeNormalEquiv (𝓝 (0:NormalWaveSpace)) (𝓝 (0:ThreeModel)) :=
    by simpa using (threeNormalEquiv.continuous.continuousAt (x:=0)).tendsto
  have hgerm : F =ᶠ[𝓝 0] threeGlobalLog ∘ threeNormalInv :=
    (he.trans threeGlobalLog_local.symm).comp_tendsto ht
  have hm : ∀ᶠ y : NormalWaveSpace in 𝓝 0, threeNormalEquiv y ∈ ball 0 r :=
    ht (Metric.ball_mem_nhds 0 hr)
  obtain ⟨s,hs0,hss⟩ := Metric.mem_nhds_iff.mp (hgerm.and (hm.and threeNormalInv_clean_eventually))
  let R := s/2
  let C := threeEnvelopeExponent*Real.log (1/200)-1
  refine ⟨C,R,half_pos hs0,?_,F,hF,?_,?_,N,hN,hs,?_⟩
  · intro y hy
    exact (hss (closedBall_subset_ball (half_lt_self hs0) hy)).2.2
  · intro y hy
    exact (hss (closedBall_subset_ball (half_lt_self hs0) hy)).1
  · intro p
    dsimp [C]
    linarith [(threeGlobalLog_bounds p).1]
  · intro g hg y hy
    exact linearPullbackMetric_strict (threeChartMetric g threeProfileCenter)
      threeNormalEquiv hf y (hg _ (ball_subset_closedBall
        (hss (closedBall_subset_ball (half_lt_self hs0) hy)).2.1))

theorem exists_three_robust_exhaustible_envelopes :
    ∃ C R : ℝ, 0<R ∧ ThreeCleanBall R ∧ ∃ N : Set (SmoothMetric ThreeModel ThreeManifold),
      IsSmoothNeighborhood threeBackgroundMetric N ∧ threeBackgroundMetric ∈ N ∧
      ∀ g ∈ N, ∀ a b : ℝ, 0<a → a<b → b<R/2 →
      ∃ δ>0, δ≤1/2 ∧ ∃ φ : NormalWaveSpace → ℝ,
        ContDiff ℝ ∞ φ ∧ HasCompactSupport (fun y => φ y-C) ∧
        tsupport (fun y => φ y-C) ⊆ closedBall 0 (3*R/4) ∧
        (∀ y ∈ closedBall 0 b,
          coordinateMetricGradient (threeNormalMetricOf g) φ y ≠ 0 ∧
          actualProfileStrict (threeNormalMetricOf g) φ y) ∧
        (∀ y ∈ closedBall 0 a, φ y=threeGlobalLog (threeNormalInv y)+δ) ∧
        (∀ y ∉ closedBall 0 b, φ y≤threeGlobalLog (threeNormalInv y)-δ) ∧
        (∀ p, C≤threeGlobalLog p-δ) := by
  obtain ⟨C,R,hR,hclean,F,hF,he,hmin,N,hN,h0N,hs⟩ := exists_three_robust_seed
  refine ⟨C,R,hR,hclean,N,hN,h0N,?_⟩
  intro g hg a b ha hab hb
  obtain ⟨δ,hδ,hδ1,φ,hφ,hφc,hφs,hstrict,hin,hout⟩ :=
    exists_exhaustible_signed_envelope (threeNormalMetricOf g) hF hR a b ha hab hb C
      (fun y => hmin (threeNormalInv y)) he (hs g hg)
  exact ⟨δ,hδ,hδ1,φ,hφ,hφc,hφs,hstrict,hin,hout,fun p => by linarith [hmin p]⟩
end


open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff InnerProductSpace
local instance threeRobustProfileNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
local instance threeRobustProfileContinuousSMul : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul

theorem exists_three_robust_global_profile_family :
    ∃ C R : ℝ, 0<R ∧ ThreeCleanBall R ∧ ∃ N : Set (SmoothMetric ThreeModel ThreeManifold),
      IsSmoothNeighborhood threeBackgroundMetric N ∧ threeBackgroundMetric ∈ N ∧
      ∀ g ∈ N, ∀ a b : ℝ, 0<a → a<b → b<R/2 →
      ∃ δ>0, ∃ I : Box (Fin 3),
        normalWaveEquiv '' Box.Icc I ⊆ closedBall 0 a ∧
        ∀ T : ℝ, ∃ Φ : ThreeManifold → ℝ,
          ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ Φ ∧
          ContDiff ℝ ∞ (Φ ∘ threeNormalInv) ∧
          tsupport (fun p => Φ p-C) ⊆ threeNormalInv '' closedBall 0 (3*R/4) ∧
          (∀ y ∈ closedBall 0 b,
            coordinateMetricGradient (threeNormalMetricOf g) (Φ ∘ threeNormalInv) y ≠ 0 ∧
            actualProfileStrict (threeNormalMetricOf g) (Φ ∘ threeNormalInv) y) ∧
          (∀ y ∈ closedBall 0 a,
            threeGlobalLog (threeNormalInv y)+δ/2 < Φ (threeNormalInv y)) ∧
          (∀ p ∉ threeNormalInv '' closedBall 0 b, Φ p≤threeGlobalLog p-δ) ∧
          T < ∫ x in Box.Icc I, profileFrequencyScale (threeNormalMetricOf g)
            (Φ ∘ threeNormalInv) (normalWaveEquiv x) := by
  obtain ⟨C,R,hR,hclean,N,hN,h0N,hprod⟩ := exists_three_robust_exhaustible_envelopes
  refine ⟨C,R,hR,hclean,N,hN,h0N,?_⟩
  intro g hg a b ha hab hbR
  obtain ⟨δ,hδ,hδ1,φ,hφ,hφc,hφs,hstrict,hin,hout,hmin⟩ := hprod g hg a b ha hab hbR
  have hne : (normalWaveEquiv ⁻¹' ball (0:NormalWaveSpace) a).Nonempty := by
    refine ⟨0,?_⟩
    simpa only [mem_preimage,map_zero,mem_ball,dist_self] using (show 0<a from ha)
  obtain ⟨I,hI⟩ := exists_box_Icc_subset_open
    (isOpen_ball.preimage normalWaveEquiv.continuous) hne
  have hIs : normalWaveEquiv '' Box.Icc I ⊆ closedBall 0 a := by
    rintro y ⟨x,hx,rfl⟩
    exact ball_subset_closedBall (hI hx)
  have hIK : normalWaveEquiv '' Box.Icc I ⊆ closedBall 0 b :=
    hIs.trans (closedBall_subset_closedBall (by linarith))
  refine ⟨δ,hδ,I,hIs,?_⟩
  intro T
  obtain ⟨ψ,hψ,hψc,hψs,hclose,hinside,hmass⟩ := exists_box_amplified_profile
    (threeNormalMetricOf g) I hφ (fun y hy => (hstrict y (hIK hy)).1)
    (fun y hy => (hstrict y (hIK hy)).2) T (half_pos hδ)
  have hd : (fun y => ψ y-C)=(fun y => ψ y-φ y)+(fun y => φ y-C) := by
    funext y; simp
  have hc : HasCompactSupport (fun y => ψ y-C) := hd ▸ hψc.add hφc
  have hsupport : tsupport (fun y => ψ y-C) ⊆ closedBall 0 (3*R/4) := by
    rw [hd]
    apply (tsupport_add _ _).trans (union_subset ?_ hφs)
    exact hψs.trans ((image_mono I.Ioo_subset_Icc).trans
      (hIs.trans (closedBall_subset_closedBall (by linarith))))
  have heoff (y : NormalWaveSpace) (hy : y ∉ normalWaveEquiv '' Box.Icc I) :
      ψ =ᶠ[𝓝 y] φ := by
    apply profile_eq_germ_of_not_tsupport
    exact fun hs => hy ((image_mono I.Ioo_subset_Icc) (hψs hs))
  have hψstrict : ∀ y ∈ closedBall 0 b,
      coordinateMetricGradient (threeNormalMetricOf g) ψ y ≠ 0 ∧ actualProfileStrict (threeNormalMetricOf g) ψ y := by
    intro y hy
    by_cases hz : y ∈ normalWaveEquiv '' Box.Icc I
    · exact hinside y hz
    · have hj := actualJet_eventuallyEq (threeNormalMetricOf g) (heoff y hz)
      rw [hj.1,hj.2.2.1]
      exact hstrict y hy
  have hψout : ∀ y ∉ closedBall 0 b, ψ y≤threeGlobalLog (threeNormalInv y)-δ := by
    intro y hy
    have hz : y ∉ normalWaveEquiv '' Box.Icc I := fun hh => hy (hIK hh)
    rw [(heoff y hz).self_of_nhds]
    exact hout y hy
  let Φ := threeNormalGlue C ψ
  have hchart : Φ ∘ threeNormalInv=ψ := threeNormalGlue_chart C ψ
  refine ⟨Φ,threeNormalGlue_smooth C hψ hc,?_,threeNormalGlue_tsupport C hc hsupport,?_,?_,?_,?_⟩
  · rw [hchart]; exact hψ
  · rw [hchart]; exact hψstrict
  · intro y hy
    have hcl := (abs_lt.mp (hclose y)).1
    have hbase := hin y hy
    have he : Φ (threeNormalInv y)=ψ y := congrFun hchart y
    rw [he]
    linarith
  · exact threeNormalGlue_exterior C δ rfl hmin hψout
  · rw [hchart]; exact hmass

end YauCounterexamples
end

end OAI
