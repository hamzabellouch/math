import OAI.Analysis.LienardCycles.CurvatureRange

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
open ScaledProfile PositiveWidth PartialCalculus
lemma kappa_monotone_height {a : Fin 6 → ℝ} {h : ℝ} (hh : 0<h)
    (hp : ∀ u,0<u → 0<third a u) : MonotoneOn (fun r=>QuinticFit.kappa a (h,r)) (Ioi 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
    (fun r hr=>((QuinticFit.kappa_analytic a hh hr).comp r (contDiffAt_const.prodMk contDiffAt_id)).continuousAt.continuousWithinAt)
    (fun r hr=>((QuinticFit.kappa_analytic a hh (interior_subset hr)).comp r (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp) |>.differentiableWithinAt)
  intro r hr
  have hr' : 0<r := interior_subset hr
  change 0≤deriv (fun s=>QuinticFit.kappa a (h,s)) r
  rw [(second_hasDerivAt ((QuinticFit.kappa_analytic a hh hr').differentiableAt (by simp))).deriv]
  exact (QuinticFit.kappa_width_pos hh hr' hp).le
lemma kappa_antitone_height {a : Fin 6 → ℝ} {h : ℝ} (hh : 0<h)
    (hp : ∀ u,0<u → third a u<0) : AntitoneOn (fun r=>QuinticFit.kappa a (h,r)) (Ioi 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    (fun r hr=>((QuinticFit.kappa_analytic a hh hr).comp r (contDiffAt_const.prodMk contDiffAt_id)).continuousAt.continuousWithinAt)
    (fun r hr=>((QuinticFit.kappa_analytic a hh (interior_subset hr)).comp r (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp) |>.differentiableWithinAt)
  intro r hr
  have hr' : 0<r := interior_subset hr
  change deriv (fun s=>QuinticFit.kappa a (h,s)) r≤0
  rw [(second_hasDerivAt ((QuinticFit.kappa_analytic a hh hr').differentiableAt (by simp))).deriv]
  exact (QuinticFit.kappa_width_neg hh hr' hp).le
lemma axisKappa_monotone {a : Fin 6 → ℝ} (hp : ∀ u,0<u → 0<third a u) :
    MonotoneOn (axisKappa a) (axisWidths a) := by
  intro r hr s hs hrs
  have hlr := (joint_limits a hr (l:=𝓝[>] (0:ℝ)) (h:=id) (r:=fun _ : ℝ=>r) self_mem_nhdsWithin
    (tendsto_id.mono_left inf_le_left) tendsto_const_nhds).2.2.2.1
  have hls := (joint_limits a hs (l:=𝓝[>] (0:ℝ)) (h:=id) (r:=fun _ : ℝ=>s) self_mem_nhdsWithin
    (tendsto_id.mono_left inf_le_left) tendsto_const_nhds).2.2.2.1
  exact le_of_tendsto_of_tendsto hlr hls ((show ∀ᶠ h : ℝ in 𝓝[>] 0, 0<h from self_mem_nhdsWithin).mono fun h hh=>
    kappa_monotone_height hh hp (axisM_abs_lt a hr).1 (axisM_abs_lt a hs).1 hrs)
lemma axisKappa_antitone {a : Fin 6 → ℝ} (hp : ∀ u,0<u → third a u<0) :
    AntitoneOn (axisKappa a) (axisWidths a) := by
  intro r hr s hs hrs
  have hlr := (joint_limits a hr (l:=𝓝[>] (0:ℝ)) (h:=id) (r:=fun _ : ℝ=>r) self_mem_nhdsWithin
    (tendsto_id.mono_left inf_le_left) tendsto_const_nhds).2.2.2.1
  have hls := (joint_limits a hs (l:=𝓝[>] (0:ℝ)) (h:=id) (r:=fun _ : ℝ=>s) self_mem_nhdsWithin
    (tendsto_id.mono_left inf_le_left) tendsto_const_nhds).2.2.2.1
  exact le_of_tendsto_of_tendsto hls hlr ((show ∀ᶠ h : ℝ in 𝓝[>] 0, 0<h from self_mem_nhdsWithin).mono fun h hh=>
    kappa_antitone_height hh hp (axisM_abs_lt a hr).1 (axisM_abs_lt a hs).1 hrs)
lemma kappa_range_height {a : Fin 6 → ℝ} {h r T C D : ℝ} (hh : 0<h) (hr : 0<r)
    (ht : peakAtWidth (QuinticProfile.profile a) ((0,h),r)<T)
    (hc : ∀ u ∈ Ioo 0 T, C≤curvature a u ∧ curvature a u≤D) :
    C≤QuinticFit.kappa a (h,r) ∧ QuinticFit.kappa a (h,r)≤D := by
  let t := peakAtWidth (QuinticProfile.profile a) ((0,h),r)
  have hs := peak_spec (QuinticProfile.profile a) (fun _ h=>QuinticProfile.analytic a h)
    (QuinticProfile.local_flow a) (p:=0) hh hr
  have he : ActualCharacteristic.Adm a t r := ⟨h,hh,hs.1,hs.2⟩
  have hb : ActualCharacteristic.b a t r=h := base_eq _
    (fun _ h=>QuinticProfile.analytic a h) (QuinticProfile.local_flow a) hh hs.1 hs.2
  have hl := ActualCharacteristic.curvature_lower he (C:=C) (fun u hu=>
    (hc u ⟨(show 0<ActualCharacteristic.b a t r by rw [hb]; exact hh).trans_le hu.1,hu.2.trans_lt ht⟩).1)
  have hu := ActualCharacteristic.curvature_upper he (C:=D) (fun u hu=>
    (hc u ⟨(show 0<ActualCharacteristic.b a t r by rw [hb]; exact hh).trans_le hu.1,hu.2.trans_lt ht⟩).2)
  simpa only [ActualCharacteristic.point,hb,id_eq] using (show C≤QuinticFit.kappa a (ActualCharacteristic.point a t r) ∧ QuinticFit.kappa a (ActualCharacteristic.point a t r)≤D from ⟨hl,hu⟩)
lemma axisKappa_lower {a : Fin 6 → ℝ} {r T C : ℝ} (hr : r ∈ axisWidths a)
    (ht : axisPeak a r<T) (hc : ∀ u ∈ Ioo 0 T, C≤curvature a u) : C≤axisKappa a r := by
  have hl := joint_limits a hr (l:=𝓝[>] (0:ℝ)) (h:=id) (r:=fun _ : ℝ=>r) self_mem_nhdsWithin
    (tendsto_id.mono_left inf_le_left) tendsto_const_nhds
  apply ge_of_tendsto hl.2.2.2.1
  filter_upwards [self_mem_nhdsWithin,hl.2.2.2.2.eventually (eventually_lt_nhds ht)] with h hh hht
  let t := peakAtWidth (QuinticProfile.profile a) ((0,h),r)
  have hs := peak_spec (QuinticProfile.profile a) (fun _ h=>QuinticProfile.analytic a h)
    (QuinticProfile.local_flow a) (p:=0) hh (axisM_abs_lt a hr).1
  have he : ActualCharacteristic.Adm a t r := ⟨h,hh,hs.1,hs.2⟩
  have hb : ActualCharacteristic.b a t r=h := base_eq _
    (fun _ h=>QuinticProfile.analytic a h) (QuinticProfile.local_flow a) hh hs.1 hs.2
  have hh' : 0<ActualCharacteristic.b a t r := by rw [hb]; exact hh
  simpa only [ActualCharacteristic.point,hb,id_eq] using ActualCharacteristic.curvature_lower he
    (fun u hu=>hc u ⟨hh'.trans_le hu.1,hu.2.trans_lt hht⟩)
lemma axisKappa_upper {a : Fin 6 → ℝ} {r T C : ℝ} (hr : r ∈ axisWidths a)
    (ht : axisPeak a r<T) (hc : ∀ u ∈ Ioo 0 T, curvature a u≤C) : axisKappa a r≤C := by
  have hl := joint_limits a hr (l:=𝓝[>] (0:ℝ)) (h:=id) (r:=fun _ : ℝ=>r) self_mem_nhdsWithin
    (tendsto_id.mono_left inf_le_left) tendsto_const_nhds
  apply le_of_tendsto hl.2.2.2.1
  filter_upwards [self_mem_nhdsWithin,hl.2.2.2.2.eventually (eventually_lt_nhds ht)] with h hh hht
  let t := peakAtWidth (QuinticProfile.profile a) ((0,h),r)
  have hs := peak_spec (QuinticProfile.profile a) (fun _ h=>QuinticProfile.analytic a h)
    (QuinticProfile.local_flow a) (p:=0) hh (axisM_abs_lt a hr).1
  have he : ActualCharacteristic.Adm a t r := ⟨h,hh,hs.1,hs.2⟩
  have hb : ActualCharacteristic.b a t r=h := base_eq _
    (fun _ h=>QuinticProfile.analytic a h) (QuinticProfile.local_flow a) hh hs.1 hs.2
  have hh' : 0<ActualCharacteristic.b a t r := by rw [hb]; exact hh
  simpa only [ActualCharacteristic.point,hb,id_eq] using ActualCharacteristic.curvature_upper he
    (fun u hu=>hc u ⟨hh'.trans_le hu.1,hu.2.trans_lt hht⟩)
end QuinticLienard.AxisFlow

end OAI
