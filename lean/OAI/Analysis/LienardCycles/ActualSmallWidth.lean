import OAI.Analysis.LienardCycles.ScaledActual

namespace OAI

universe uι

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
open ScaledProfile SmallWidth PartialCalculus
lemma pulled_fiber {a : Fin 6 → ℝ} {c h : ℝ} (hc : 0<c) (hh : c<h) :
    fiber (pulledCurvature a c) ((h,0),0)=2*third a h/7 := by
  have hs := (pulledCurvature_analytic (a:=a) (h:=h) (r:=0) (e:=0) hc (by simpa using hh)).differentiableAt (by simp)
  have hd : HasDerivAt (fun e => pulledCurvature a c ((h,0),e))
      (fiber (pulledCurvature a c) ((h,0),0)) 0 :=
    hs.hasFDerivAt.comp_hasDerivAt 0 ((hasDerivAt_const 0 (h,0)).prodMk (hasDerivAt_id 0))
  have hcub := (fit_cubic (a:=a) hc (Real.sqrt (h-c))).2
  have hh' : c+(Real.sqrt (h-c))^2=h := by rw [Real.sq_sqrt (by linarith)]; ring
  rw [hh'] at hcub
  apply hd.unique
  simpa only [pulledCurvature,Function.comp_def,pull,zero_pow (by norm_num : (2:ℕ)≠0),sub_zero] using! hcub
lemma kappa_deriv_correction {a : Fin 6 → ℝ} {c h r : ℝ}
    (hc : 0<c) (hh : c+r^2<h) (hr : 0<r) :
    deriv (fun s => kappa a (h,s)) r=deriv (fun s => correction (pulledCurvature a c) (h,s)) r := by
  have hev : (fun s => kappa a (h,s)) =ᶠ[𝓝 r]
      (fun s => curvature a h+correction (pulledCurvature a c) (h,s)) := by
    filter_upwards [continuousAt_const.eventually_lt continuousAt_id hr,
      (continuousAt_const.add (continuousAt_id.pow 2)).eventually_lt continuousAt_const hh] with s hs hh'
    exact kappa_correction hc hh'.le hs
  rw [hev.deriv_eq,deriv_const_add]
lemma kappa_deriv_limit {a : Fin 6 → ℝ} {h₀ : ℝ} (hh₀ : 0<h₀)
    {ι : Type uι} {l : Filter ι} {h r : ι → ℝ}
    (hh : Tendsto h l (𝓝 h₀)) (hr : Tendsto r l (𝓝 0)) (hp : ∀ᶠ z in l, 0<r z) :
    Tendsto (fun z => deriv (fun s => kappa a (h z,s)) (r z)/r z) l (𝓝 (4*third a h₀/7)) := by
  let c := h₀/2
  have hc : 0<c := by dsimp [c]; linarith
  have hch : c<h₀ := by dsimp [c]; linarith
  have ha := pulledCurvature_analytic (a:=a) (h:=h₀) (r:=0) (e:=0) hc (by simpa using hch)
  have hl := correction_derivative_limit ha hh hr (hp.mono (fun _ hz => hz.ne'))
  rw [pulled_fiber hc hch] at hl
  have he : 2*(2*third a h₀/7)=4*third a h₀/7 := by ring
  rw [he] at hl
  apply hl.congr'
  have hlim : Tendsto (fun z => h z-c-(r z)^2) l (𝓝 (h₀-c)) := by
    simpa using (hh.sub tendsto_const_nhds).sub (hr.pow 2)
  filter_upwards [hp,hlim.eventually (eventually_gt_nhds (sub_pos.mpr hch))] with z hz hh'
  rw [kappa_deriv_correction hc (by linarith) hz]
end QuinticLienard.QuinticFit

end OAI
