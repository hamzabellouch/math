import OAI.Analysis.LienardCycles.AxisWidthGerm

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
open ScalarArcs ScaledProfile PartialCalculus PositiveWidth
lemma axisWidths_open (a : Fin 6 → ℝ) : IsOpen (axisWidths a) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro r ⟨t,ht,rfl⟩
  obtain ⟨Y,G,_,_,_,_,he,_⟩ := width_germ a ht
  exact he.mono fun _ h=>h.1
lemma axisWidths_ordConnected (a : Fin 6 → ℝ) : OrdConnected (axisWidths a) := by
  have hc : IsPreconnected (transversePeaks a) := (convex_iff_ordConnected.mpr (transversePeaks_ordConnected a)).isPreconnected
  exact (hc.image (axisWidth a) (fun t ht=>(axisWidth_analytic a ht).continuousAt.continuousWithinAt)).ordConnected
lemma axisPeak_analytic (a : Fin 6 → ℝ) {r : ℝ} (hr : r ∈ axisWidths a) : ContDiffAt ℝ ω (axisPeak a) r := by
  obtain ⟨t,ht,rfl⟩ := hr
  obtain ⟨Y,G,hY,_,_,_,he,_⟩ := width_germ a ht
  exact (hY.comp _ (contDiffAt_const.prodMk contDiffAt_id)).congr_of_eventuallyEq (he.mono fun _ h=>h.2.1.symm)
lemma axisM_analytic (a : Fin 6 → ℝ) {r : ℝ} (hr : r ∈ axisWidths a) : ContDiffAt ℝ ω (axisM a) r := by
  obtain ⟨t,ht,rfl⟩ := hr
  obtain ⟨Y,G,_,hG,_,_,he,_⟩ := width_germ a ht
  exact (hG.comp _ (contDiffAt_const.prodMk contDiffAt_id)).congr_of_eventuallyEq (he.mono fun _ h=>h.2.2.symm)
noncomputable def axisV (a : Fin 6 → ℝ) (r : ℝ) : ℝ := deriv (axisM a) r
lemma axisV_analytic (a : Fin 6 → ℝ) {r : ℝ} (hr : r ∈ axisWidths a) : ContDiffAt ℝ ω (axisV a) r :=
  ((axisM_analytic a hr).fderiv_right (m:=ω) (by simp)).clm_apply contDiffAt_const
lemma axisV_ratio (a : Fin 6 → ℝ) {r : ℝ} (hr : r ∈ axisWidths a) :
    axisV a r=deriv (axisCenter a) (axisPeak a r)/deriv (axisWidth a) (axisPeak a r) := by
  have ht := (axisPeak_spec a hr).1
  have hpd := (axisPeak_analytic a hr).differentiableAt (by simp)
  have hd := ((axisWidth_analytic a ht).differentiableAt (by simp)).hasDerivAt.comp r hpd.hasDerivAt
  have he : (axisWidth a ∘ axisPeak a) =ᶠ[𝓝 r] (fun s=>s) := by
    filter_upwards [(axisWidths_open a).mem_nhds hr] with s hs
    exact (axisPeak_spec a hs).2
  have hdp : deriv (axisWidth a) (axisPeak a r)*deriv (axisPeak a) r=1 :=
    (hd.congr_of_eventuallyEq he.symm).unique (hasDerivAt_id r)
  have hc := ((axisCenter_analytic a ht).differentiableAt (by simp)).hasDerivAt.comp r hpd.hasDerivAt
  have hdc : axisV a r=deriv (axisCenter a) (axisPeak a r)*deriv (axisPeak a) r := hc.deriv
  rw [hdc]
  apply (eq_div_iff (axisWidth_pos_deriv a ht).2.1.ne').mpr
  calc
    _ = deriv (axisCenter a) (axisPeak a r)*(deriv (axisWidth a) (axisPeak a r)*deriv (axisPeak a) r) := by ring
    _ = _ := by rw [hdp,mul_one]
lemma axisV_abs_lt (a : Fin 6 → ℝ) {r : ℝ} (hr : r ∈ axisWidths a) : |axisV a r|<1 := by
  rw [axisV_ratio a hr]
  exact (axisWidth_pos_deriv a (axisPeak_spec a hr).1).2.2.2

lemma width_germ_derivative (a : Fin 6 → ℝ) {r : ℝ} {G : ℝ×ℝ → ℝ}
    (hr : 0<r) (hG : ContDiffAt ℝ ω G (0,r))
    (he : ∀ᶠ q in 𝓝 ((0:ℝ),r), 0<q.1 → G q=QuinticFit.M a (q.1^2/2,q.2)) :
    ∀ᶠ q in 𝓝 ((0:ℝ),r), 0<q.1 → second G q=QuinticFit.V a (q.1^2/2,q.2) := by
  filter_upwards [hG.eventually (by simp),eventually_eventually_nhds.2 he,
    continuousAt_snd.eventually (eventually_gt_nhds hr)] with q hqa hqe hqr hqx
  have hslice : (fun s=>G (q.1,s)) =ᶠ[𝓝 q.2] (fun s=>QuinticFit.M a (q.1^2/2,s)) := by
    filter_upwards [(continuousAt_const.prodMk continuousAt_id).eventually hqe] with s hs
    exact hs hqx
  have hh : 0<q.1^2/2 := div_pos (sq_pos_of_pos hqx) (by norm_num)
  exact ((second_hasDerivAt (hqa.differentiableAt (by simp))).congr_of_eventuallyEq hslice.symm).unique
    (second_hasDerivAt ((QuinticFit.M_analytic a hh hqr).differentiableAt (by simp)))
lemma width_germ_axis_derivative (a : Fin 6 → ℝ) {r : ℝ} {G : ℝ×ℝ → ℝ}
    (hG : ContDiffAt ℝ ω G (0,r))
    (he : ∀ᶠ s in 𝓝 r, G (0,s)=axisM a s) : second G (0,r)=axisV a r :=
  ((second_hasDerivAt (hG.differentiableAt (by simp))).congr_of_eventuallyEq (he.mono fun _ h=>h.symm)).deriv.symm
end QuinticLienard.AxisFlow

end OAI
