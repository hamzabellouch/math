import OAI.Analysis.LienardCycles.AxisWidthRegularity

namespace OAI

universe uι

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
open ScalarArcs ScaledProfile PartialCalculus PositiveWidth QuadraticCoordinates
noncomputable def axisLambda (a : Fin 6 → ℝ) (r : ℝ) : ℝ := QuadraticFit.fitD ((r,axisM a r),axisV a r)
noncomputable def axisKappa (a : Fin 6 → ℝ) (r : ℝ) : ℝ := QuadraticFit.fitK ((r,axisM a r),axisV a r)
lemma axisLambda_analytic (a : Fin 6 → ℝ) {r : ℝ} (hr : r ∈ axisWidths a) :
    ContDiffAt ℝ ω (axisLambda a) r :=
  (QuadraticFit.fitD_analytic (axisM_abs_lt a hr).1 (axisM_abs_lt a hr).2 (axisV_abs_lt a hr)).comp r
    ((contDiffAt_id.prodMk (axisM_analytic a hr)).prodMk (axisV_analytic a hr))
lemma axisKappa_analytic (a : Fin 6 → ℝ) {r : ℝ} (hr : r ∈ axisWidths a) :
    ContDiffAt ℝ ω (axisKappa a) r :=
  (QuadraticFit.fitK_analytic (axisM_abs_lt a hr).1 (axisM_abs_lt a hr).2 (axisV_abs_lt a hr)).comp r
    ((contDiffAt_id.prodMk (axisM_analytic a hr)).prodMk (axisV_analytic a hr))
lemma axisFit_spec (a : Fin 6 → ℝ) {r : ℝ} (hr : r ∈ axisWidths a) :
    H ((axisLambda a r,axisKappa a r),r)=axisM a r ∧
    Hr ((axisLambda a r,axisKappa a r),r)=axisV a r :=
  QuadraticFit.fit_spec (axisM_abs_lt a hr).1 (axisM_abs_lt a hr).2 (axisV_abs_lt a hr)

theorem joint_limits (a : Fin 6 → ℝ) {r₀ : ℝ} (hr₀ : r₀ ∈ axisWidths a)
    {ι : Type uι} {l : Filter ι} {h r : ι → ℝ}
    (hh : ∀ᶠ i in l, 0<h i) (hh0 : Tendsto h l (𝓝 0)) (hrr : Tendsto r l (𝓝 r₀)) :
    Tendsto (fun i=>QuinticFit.M a (h i,r i)) l (𝓝 (axisM a r₀)) ∧
    Tendsto (fun i=>QuinticFit.V a (h i,r i)) l (𝓝 (axisV a r₀)) ∧
    Tendsto (fun i=>QuinticFit.lambda a (h i,r i)) l (𝓝 (axisLambda a r₀)) ∧
    Tendsto (fun i=>QuinticFit.kappa a (h i,r i)) l (𝓝 (axisKappa a r₀)) ∧
    Tendsto (fun i=>peakAtWidth (QuinticProfile.profile a) ((0,h i),r i)) l (𝓝 (axisPeak a r₀)) := by
  have ht := axisPeak_spec a hr₀
  obtain ⟨Y,G,hY,hG,hY0,_,hes,hep⟩ := width_germ a ht.1
  rw [ht.2] at hY hG hY0 hes hep
  have hG0 : G (0,r₀)=axisM a r₀ := hes.self_of_nhds.2.2
  have hGD0 : second G (0,r₀)=axisV a r₀ := width_germ_axis_derivative a hG (hes.mono fun _ he=>he.2.2)
  have heD := width_germ_derivative a (axisM_abs_lt a hr₀).1 hG (hep.mono fun _ he hx=>(he hx).2)
  have hx0 : Tendsto (fun i=>root (h i)) l (𝓝 0) := by
    have hc : Continuous (fun s : ℝ=>root s) := by unfold root; fun_prop
    simpa [root,Function.comp_def] using hc.continuousAt.tendsto.comp hh0
  have hq := hx0.prodMk_nhds hrr
  have hx : ∀ᶠ i in l, 0<root (h i) := hh.mono fun _ hi=>Real.sqrt_pos.mpr (mul_pos (by norm_num) hi)
  have hEq : ∀ᶠ i in l,
      G (root (h i),r i)=QuinticFit.M a (h i,r i) ∧
      second G (root (h i),r i)=QuinticFit.V a (h i,r i) ∧
      Y (root (h i),r i)=peakAtWidth (QuinticProfile.profile a) ((0,h i),r i) := by
    filter_upwards [hq.eventually hep,hq.eventually heD,hh,hx] with i he hd hi hxi
    have hs : root (h i)^2/2=h i := by rw [root_sq hi.le]; ring
    have hm := (he hxi).2
    have hv := hd hxi
    have hy := (he hxi).1
    rw [hs] at hm hv hy
    exact ⟨hm,hv,hy⟩
  have hm : Tendsto (fun i=>QuinticFit.M a (h i,r i)) l (𝓝 (axisM a r₀)) := by
    have hg := hG.continuousAt.tendsto.comp hq
    rw [hG0] at hg
    exact hg.congr' (hEq.mono fun _ he=>he.1)
  have hv : Tendsto (fun i=>QuinticFit.V a (h i,r i)) l (𝓝 (axisV a r₀)) := by
    have hg := (second_contDiffAt hG).continuousAt.tendsto.comp hq
    rw [hGD0] at hg
    exact hg.congr' (hEq.mono fun _ he=>he.2.1)
  have hyp : Tendsto (fun i=>peakAtWidth (QuinticProfile.profile a) ((0,h i),r i)) l (𝓝 (axisPeak a r₀)) := by
    have hy := hY.continuousAt.tendsto.comp hq
    rw [hY0] at hy
    exact hy.congr' (hEq.mono fun _ he=>he.2.2)
  have hr : ∀ᶠ i in l, 0<r i := hrr.eventually (eventually_gt_nhds (axisM_abs_lt a hr₀).1)
  have hf := (hrr.prodMk_nhds hm).prodMk_nhds hv
  have hld := (QuadraticFit.fitD_analytic (axisM_abs_lt a hr₀).1 (axisM_abs_lt a hr₀).2 (axisV_abs_lt a hr₀)).continuousAt.tendsto.comp hf
  have hkd := (QuadraticFit.fitK_analytic (axisM_abs_lt a hr₀).1 (axisM_abs_lt a hr₀).2 (axisV_abs_lt a hr₀)).continuousAt.tendsto.comp hf
  refine ⟨hm,hv,?_,?_,hyp⟩
  · apply hld.congr'
    filter_upwards [hh,hr] with i hi hri
    exact (QuinticFit.fit_eq a hi hri).1.symm
  · apply hkd.congr'
    filter_upwards [hh,hr] with i hi hri
    exact (QuinticFit.fit_eq a hi hri).2.symm
end QuinticLienard.AxisFlow

end OAI
