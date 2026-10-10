import OAI.Analysis.LienardCycles.ScaledDerivative

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter Metric
open scoped Topology ENNReal
open scoped Topology
open Set Filter MeasureTheory
open Set Filter Asymptotics
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.QuinticFit
open ScaledProfile
noncomputable def lambda (a : Fin 6 → ℝ) (q : ℝ × ℝ) : ℝ := PositiveFit.d (QuinticProfile.profile a) q.1 q.2 0
noncomputable def kappa (a : Fin 6 → ℝ) (q : ℝ × ℝ) : ℝ := PositiveFit.k (QuinticProfile.profile a) q.1 q.2 0
lemma scaled_fit {a : Fin 6 → ℝ} {c u r : ℝ} (hc : 0<c) (hr : 0<r) :
    fitSlope a c ((u,r),r^5)=r*lambda a (c+u^2+r^2,r) ∧
    fitCurvature a c ((u,r),r^5)=r^3*kappa a (c+u^2+r^2,r) := by
  have hh : 0<c+u^2+r^2 := by positivity
  have he (x : ℝ) (hx : 0<x) : QuinticProfile.profile a (0,c+u^2+r^2*x) =
      poly a (root (c+u^2+r^2))+r*Φ a c (((u,r),r^5),x) := by
    have hs := actual_scaling a (u:=u) hc hr hx
    change _-_=_ at hs
    dsimp [QuinticProfile.profile,root]
    linarith only [hs]
  have hm := PositiveWidth.fixed_width_scaling (Φ a c) (fun _ h => analytic hc h) (local_flow a hc)
    (QuinticProfile.profile a) (fun _ h => QuinticProfile.analytic a h) (QuinticProfile.local_flow a)
    (p:=((u,r),r^5)) (q:=0) (b:=1) (H:=c+u^2) (c:=r) (r:=1) (C:=poly a (root (c+u^2+r^2)))
    (by norm_num) (by simpa using hh) hr (by norm_num) (by simpa using he)
  have hn := PositiveWidth.fixed_width_derivative_scaling (Φ a c) (fun _ h => analytic hc h) (local_flow a hc)
    (QuinticProfile.profile a) (fun _ h => QuinticProfile.analytic a h) (QuinticProfile.local_flow a)
    (p:=((u,r),r^5)) (q:=0) (b:=1) (H:=c+u^2) (c:=r) (r:=1) (C:=poly a (root (c+u^2+r^2)))
    (by norm_num) (by simpa using hh) hr (by norm_num) (by simpa using he)
  simp only [mul_one] at hm hn
  have hM := PositiveFit.m_abs_lt (QuinticProfile.profile a) (fun _ h => QuinticProfile.analytic a h)
    (QuinticProfile.local_flow a) (p:=0) hh hr
  have hv := PositiveFit.n_abs_lt (QuinticProfile.profile a) (fun _ h => QuinticProfile.analytic a h)
    (QuinticProfile.local_flow a) (p:=0) hh hr
  have hs := QuadraticFit.fit_scaled hr hM hv
  have hm' : PositiveFit.m (QuinticProfile.profile a) (c+u^2+r^2) (0,r)/r =
      PositiveFit.m (Φ a c) 1 (((u,r),r^5),1) := by
    change PositiveWidth.midpointAtWidth _ _ /r = PositiveWidth.midpointAtWidth _ _
    rw [hm]
    field_simp
  rw [hm',hn] at hs
  simpa only [fitSlope,fitCurvature,lambda,kappa,PositiveFit.d,PositiveFit.k,hn] using hs
noncomputable def pull (_a : Fin 6 → ℝ) (c : ℝ) (q : SmallWidth.Space) : ScaledProfile.Params :=
  ((Real.sqrt (q.1.1-c-q.1.2^2),q.1.2),q.2)
lemma pull_analytic (a : Fin 6 → ℝ) {c h r e : ℝ} (hh : c+r^2<h) :
    ContDiffAt ℝ ω (pull a c) ((h,r),e) := by
  have hp : 0<h-c-r^2 := by linarith
  exact (((contDiffAt_fst.fst.sub contDiffAt_const).sub
    (contDiffAt_fst.snd.pow 2)).sqrt (ne_of_gt hp)).prodMk contDiffAt_fst.snd |>.prodMk contDiffAt_snd
noncomputable def pulledSlope (a : Fin 6 → ℝ) (c : ℝ) : SmallWidth.Space → ℝ := fitSlope a c ∘ pull a c
noncomputable def pulledCurvature (a : Fin 6 → ℝ) (c : ℝ) : SmallWidth.Space → ℝ := fitCurvature a c ∘ pull a c
lemma pulledSlope_analytic {a : Fin 6 → ℝ} {c h r e : ℝ} (hc : 0<c) (hh : c+r^2<h) :
    ContDiffAt ℝ ω (pulledSlope a c) ((h,r),e) :=
  (fitSlope_analytic hc _).comp _ (pull_analytic a hh)
lemma pulledCurvature_analytic {a : Fin 6 → ℝ} {c h r e : ℝ} (hc : 0<c) (hh : c+r^2<h) :
    ContDiffAt ℝ ω (pulledCurvature a c) ((h,r),e) :=
  (fitCurvature_analytic hc _).comp _ (pull_analytic a hh)
lemma pull_height {c h r : ℝ} (hh : c+r^2≤h) : c+(Real.sqrt (h-c-r^2))^2+r^2=h := by
  rw [Real.sq_sqrt (by linarith)]
  ring
lemma pulled_zero {a : Fin 6 → ℝ} {c h r : ℝ} (hc : 0<c) (hh : c+r^2≤h) :
    pulledSlope a c ((h,r),0)=r*slope a h ∧ pulledCurvature a c ((h,r),0)=r^3*curvature a h := by
  have hs := fit_epsilon_zero (a:=a) hc (Real.sqrt (h-c-r^2)) r
  rw [pull_height hh] at hs
  exact hs
lemma pulled_actual {a : Fin 6 → ℝ} {c h r : ℝ} (hc : 0<c) (hh : c+r^2≤h) (hr : 0<r) :
    pulledSlope a c ((h,r),r^5)=r*lambda a (h,r) ∧
    pulledCurvature a c ((h,r),r^5)=r^3*kappa a (h,r) := by
  have hs := scaled_fit (a:=a) (u:=Real.sqrt (h-c-r^2)) hc hr
  rw [pull_height hh] at hs
  exact hs
lemma kappa_correction {a : Fin 6 → ℝ} {c h r : ℝ} (hc : 0<c) (hh : c+r^2≤h) (hr : 0<r) :
    kappa a (h,r)=curvature a h+SmallWidth.correction (pulledCurvature a c) (h,r) := by
  dsimp only [SmallWidth.correction]
  rw [(pulled_actual hc hh hr).2,(pulled_zero hc hh).2]
  field_simp
  ring
end QuinticLienard.QuinticFit

end OAI
