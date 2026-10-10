import OAI.Analysis.LienardCycles.AxisZeroCount

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter Metric
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.AxisFlow
open ScalarArcs PositiveWidth ScaledProfile PartialCalculus QuadraticCoordinates
noncomputable def heightWidth (a : Fin 6 → ℝ) (t h : ℝ) : ℝ := widthFamily (QuinticProfile.profile a) ((0,t),h)
lemma heightWidth_pos (a : Fin 6 → ℝ) {t h : ℝ} (hh : 0<h) (ht : h<t) : 0<heightWidth a t h :=
  width_pos _ (fun _ h=>QuinticProfile.analytic a h) hh ht
lemma heightWidth_limit (a : Fin 6 → ℝ) {t : ℝ} (ht : 0<t) :
    Tendsto (heightWidth a t) (𝓝[>] 0) (𝓝 (axisWidth a t)) := by
  exact ((upper_axis_tendsto (φ_smooth a) (φ_continuous a).continuousOn ht).sub
    (lower_axis_tendsto (φ_smooth a) (φ_continuous a).continuousOn ht)).div_const 2
lemma heightWidth_midpoint (a : Fin 6 → ℝ) {t h : ℝ} (hh : 0<h) (ht : h<t) :
    QuinticFit.M a (h,heightWidth a t h)=midpointFamily (QuinticProfile.profile a) ((0,t),h) := by
  have he := peak_eq (QuinticProfile.profile a) (fun _ h=>QuinticProfile.analytic a h)
    (QuinticProfile.local_flow a) (p:=(0:ℝ)) (heightWidth_pos a hh ht) hh ht rfl
  exact congrArg (fun t=>midpointFamily (QuinticProfile.profile a) ((0,t),h)) he
lemma heightWidth_deriv (a : Fin 6 → ℝ) {t h : ℝ} (hh : 0<h) (ht : h<t) :
    HasDerivAt (heightWidth a t) (-QuinticFit.α a (h,heightWidth a t h)) h := by
  have hd := width_base_deriv (QuinticProfile.profile a) (fun _ h=>QuinticProfile.analytic a h)
    (QuinticProfile.local_flow a) (p:=(0:ℝ)) hh ht
  change HasDerivAt (heightWidth a t) (-(heightWidth a t h/(heightWidth a t h^2-QuinticFit.M a (h,heightWidth a t h)^2))) h
  rw [heightWidth_midpoint a hh ht]
  change HasDerivAt (fun s=>widthFamily (QuinticProfile.profile a) ((0,t),s))
    (-(widthFamily (QuinticProfile.profile a) ((0,t),h)/(widthFamily (QuinticProfile.profile a) ((0,t),h)^2-midpointFamily (QuinticProfile.profile a) ((0,t),h)^2))) h
  simpa only [neg_div] using hd
lemma along_height_deriv {a : Fin 6 → ℝ} {t h : ℝ} (hh : 0<h) (ht : h<t)
    {f : ℝ×ℝ → ℝ} (hf : DifferentiableAt ℝ f (h,heightWidth a t h)) :
    HasDerivAt (fun u=>f (u,heightWidth a t u)) (QuinticFit.D a f (h,heightWidth a t h)) h := by
  have hd := hf.hasFDerivAt.comp_hasDerivAt h ((hasDerivAt_id h).prodMk (heightWidth_deriv a hh ht))
  simpa only [Function.comp_def,fderiv_pair,one_mul,QuinticFit.D,id_eq,neg_mul,sub_eq_add_neg] using hd
lemma intercept_height_deriv {a : Fin 6 → ℝ} {t h d : ℝ} (hh : 0<h) (ht : h<t) :
    HasDerivAt (fun u=>QuinticFit.intercept a d (u,heightWidth a t u))
      ((S (QuinticFit.fit a (h,heightWidth a t h))+h*R (QuinticFit.fit a (h,heightWidth a t h)))/
        G (QuinticFit.fit a (h,heightWidth a t h))*
        (QuinticFit.lambda a (h,heightWidth a t h)-slope a h)) h := by
  have hr := heightWidth_pos a hh ht
  have hl := along_height_deriv hh ht ((QuinticFit.lambda_analytic a hh hr).differentiableAt (by simp))
  have hk := along_height_deriv hh ht ((QuinticFit.kappa_analytic a hh hr).differentiableAt (by simp))
  have hd := (hl.sub ((hasDerivAt_id h).mul hk)).sub_const d
  have hg := QuinticFit.fit_transport a hh hr
  have hL : QuinticFit.D a (QuinticFit.lambda a) (h,heightWidth a t h)=
      QuinticFit.kappa a (h,heightWidth a t h)+S (QuinticFit.fit a (h,heightWidth a t h))/G (QuinticFit.fit a (h,heightWidth a t h))*
        (QuinticFit.lambda a (h,heightWidth a t h)-slope a h) := by linarith only [hg.2.2]
  rw [hg.2.1,hL] at hd
  convert! hd using 1
  simp only [id_eq]
  ring

lemma axisLambda_lt {a : Fin 6 → ℝ} {r d : ℝ} (hr : r ∈ axisWidths a)
    (hp : ∀ u,0<u → 0<u*curvature a u-slope a u+d)
    (hs : Tendsto (slope a) (𝓝[>] 0) atBot) : axisLambda a r<d := by
  let t := axisPeak a r
  have ht := axisPeak_spec a hr
  have hw : Tendsto (heightWidth a t) (𝓝[>] 0) (𝓝 r) := by
    rw [←ht.2]
    exact heightWidth_limit a ht.1.1
  have hl := joint_limits a hr (l:=𝓝[>] (0:ℝ)) (h:=id) (r:=heightWidth a t)
    self_mem_nhdsWithin (tendsto_id.mono_left inf_le_left) hw
  have hI : Tendsto (fun u=>QuinticFit.intercept a d (u,heightWidth a t u)) (𝓝[>] 0) (𝓝 (axisLambda a r-d)) := by
    simpa only [QuinticFit.intercept,zero_mul,sub_zero,id_eq] using
      (hl.2.2.1.sub ((tendsto_id.mono_left inf_le_left).mul hl.2.2.2.1)).sub_const d
  have hev : ∀ᶠ u in 𝓝[>] (0:ℝ), u<t ∧ slope a u<QuinticFit.lambda a (u,heightWidth a t u) := by
    filter_upwards [(eventually_lt_nhds ht.1.1).filter_mono inf_le_left,
      hs.eventually (eventually_lt_atBot (axisLambda a r-1)),
      hl.2.2.1.eventually (eventually_gt_nhds (show axisLambda a r-1<axisLambda a r by linarith))] with u hut hsu hlu
    exact ⟨hut,hsu.trans hlu⟩
  obtain ⟨ε,hε,hεprop⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).mp hev
  have hεt : ε/2<t := (hεprop ⟨half_pos hε,half_lt_self hε⟩).1
  have hm : MonotoneOn (fun u=>QuinticFit.intercept a d (u,heightWidth a t u)) (Ioo 0 ε) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioo 0 ε)
      (fun u hu=>(intercept_height_deriv hu.1 (hεprop hu).1).continuousAt.continuousWithinAt)
      (fun u hu=>(intercept_height_deriv (interior_subset hu).1 (hεprop (interior_subset hu)).1).differentiableAt.differentiableWithinAt)
    intro u hu
    have hu' := interior_subset hu
    rw [(intercept_height_deriv (d:=d) hu'.1 (hεprop hu').1).deriv]
    have hru := heightWidth_pos a hu'.1 (hεprop hu').1
    exact (mul_pos (div_pos (add_pos (S_pos hru) (mul_pos hu'.1 (R_pos hru))) (G_pos hru))
      (sub_pos.mpr (hεprop hu').2)).le
  have hle : axisLambda a r-d≤QuinticFit.intercept a d (ε/2,heightWidth a t (ε/2)) := by
    apply le_of_tendsto hI
    filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds (half_pos hε)).filter_mono inf_le_left] with u hu hue
    exact hm ⟨hu,hue.trans (half_lt_self hε)⟩ ⟨half_pos hε,half_lt_self hε⟩ hue.le
  have hi := QuinticFit.intercept_negative (half_pos hε) (heightWidth_pos a (half_pos hε) hεt) hp
  dsimp only [QuinticFit.intercept] at hle
  linarith
end QuinticLienard.AxisFlow

end OAI
