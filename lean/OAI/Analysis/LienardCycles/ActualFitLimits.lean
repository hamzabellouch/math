import OAI.Analysis.LienardCycles.CurvatureTransport

namespace OAI

universe uι

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter Metric
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.QuinticFit
open ScaledProfile SmallWidth QuadraticCoordinates
lemma fit_limits {a : Fin 6 → ℝ} {h₀ : ℝ} (hh₀ : 0<h₀)
    {ι : Type uι} {l : Filter ι} {h r : ι → ℝ}
    (hh : Tendsto h l (𝓝 h₀)) (hr : Tendsto r l (𝓝 0)) (hp : ∀ᶠ z in l, 0<r z) :
    Tendsto (fun z => lambda a (h z,r z)) l (𝓝 (slope a h₀)) ∧
    Tendsto (fun z => kappa a (h z,r z)) l (𝓝 (curvature a h₀)) := by
  let c := h₀/2
  have hc : 0<c := by dsimp [c]; linarith
  have hch : c<h₀ := by dsimp [c]; linarith
  have hF := pulledSlope_analytic (a:=a) (h:=h₀) (r:=0) (e:=0) hc (by simpa using hch)
  have hG := pulledCurvature_analytic (a:=a) (h:=h₀) (r:=0) (e:=0) hc (by simpa using hch)
  have he : Tendsto (fun z => (r z)^5) l (𝓝 0) := by simpa using hr.pow 5
  have hn : ∀ᶠ z in l, (r z)^5≠0 := hp.mono (fun _ hz => pow_ne_zero _ hz.ne')
  have hqF := fiber_quotient_tendsto (hF.hasStrictFDerivAt (by simp)) (hh.prodMk_nhds hr) he hn
  have hqG := fiber_quotient_tendsto (hG.hasStrictFDerivAt (by simp)) (hh.prodMk_nhds hr) he hn
  have hlF := (hr.pow 4).mul hqF
  have hlG := (hr.pow 2).mul hqG
  have hb : ∀ᶠ z in l, c+(r z)^2<h z := by
    have ht : Tendsto (fun z => h z-c-(r z)^2) l (𝓝 (h₀-c)) := by
      simpa using (hh.sub tendsto_const_nhds).sub (hr.pow 2)
    filter_upwards [ht.eventually (eventually_gt_nhds (sub_pos.mpr hch))] with z hz
    linarith
  constructor
  · have ht := ((slope_analytic a hh₀).continuousAt.tendsto.comp hh).add hlF
    simp only [zero_pow (by norm_num : (4:ℕ)≠0),zero_mul,add_zero] at ht
    apply ht.congr'
    filter_upwards [hp,hb] with z hz hbz
    dsimp
    rw [(pulled_actual hc hbz.le hz).1,(pulled_zero hc hbz.le).1]
    field_simp
    ring
  · have ht := ((curvature_analytic a hh₀).continuousAt.tendsto.comp hh).add hlG
    simp only [zero_pow (by norm_num : (2:ℕ)≠0),zero_mul,add_zero] at ht
    apply ht.congr'
    filter_upwards [hp,hb] with z hz hbz
    dsimp
    rw [(pulled_actual hc hbz.le hz).2,(pulled_zero hc hbz.le).2]
    field_simp
    ring
lemma normalized_limits {a : Fin 6 → ℝ} {h₀ : ℝ} (hh₀ : 0<h₀)
    {ι : Type uι} {l : Filter ι} {h r : ι → ℝ}
    (hh : Tendsto h l (𝓝 h₀)) (hr : Tendsto r l (𝓝 0)) (hp : ∀ᶠ z in l, 0<r z) :
    Tendsto (fun z => M a (h z,r z)/r z) l (𝓝 0) ∧
    Tendsto (fun z => V a (h z,r z)) l (𝓝 0) := by
  have hf := fit_limits (a:=a) hh₀ hh hr hp
  have hd : Tendsto (fun z => r z*lambda a (h z,r z)) l (𝓝 0) := by simpa using hr.mul hf.1
  have hk : Tendsto (fun z => (r z)^3*kappa a (h z,r z)) l (𝓝 0) := by simpa using (hr.pow 3).mul hf.2
  have ht := (hd.prodMk_nhds hk).prodMk_nhds (tendsto_const_nhds (x:=(1:ℝ)))
  have hM := (H_analytic (d:=0) (k:=0) (by norm_num : (0:ℝ)<1)).continuousAt.tendsto.comp ht
  have hV := (Hr_analytic (d:=0) (k:=0) (by norm_num : (0:ℝ)<1)).continuousAt.tendsto.comp ht
  rw [(zero_data (by norm_num : (0:ℝ)<1)).2] at hM
  rw [Hr_zero (by norm_num : (0:ℝ)<1)] at hV
  constructor
  · apply hM.congr'
    filter_upwards [hp,hh.eventually (eventually_gt_nhds hh₀)] with z hz hhz
    have he := scaling (lambda a (h z,r z)) (kappa a (h z,r z)) hz
    rw [show H ((lambda a (h z,r z),kappa a (h z,r z)),r z)=M a (h z,r z) from (spec a hhz hz).1] at he
    exact (eq_div_iff hz.ne').mpr (by simpa only [Function.comp_apply,mul_comm] using he.symm)
  · apply hV.congr'
    filter_upwards [hp,hh.eventually (eventually_gt_nhds hh₀)] with z hz hhz
    have he := Hr_scaling (lambda a (h z,r z)) (kappa a (h z,r z)) hz (by norm_num : (0:ℝ)<1)
    simpa only [Function.comp_apply,mul_one,show Hr ((lambda a (h z,r z),kappa a (h z,r z)),r z)=V a (h z,r z) from (spec a hhz hz).2] using he.symm
end QuinticLienard.QuinticFit

end OAI
