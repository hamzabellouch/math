import OAI.Geometry.SurfaceImmersion.Atlas.IntrinsicPhaseChartGeometry
import OAI.Geometry.SurfaceImmersion.Atlas.ChartSecondFormBounds

namespace OAI

/-! A normal-curvature margin in a phase chart gives a fixed margin in
the original coordinates, uniformly for every smooth immersion. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

lemma phase_chart_normal_transport
    (e : OpenPartialHomeomorph Base Base) (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {W V : RField 4} (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V)
    (hrel : ∀ x ∈ e.source, W x = V (e x)) {x : Base} (hx : x ∈ e.source)
    (hI : Function.Injective (fderiv ℝ V (e x))) :
    Function.Injective (fderiv ℝ W x) ∧
      ‖realSecondTensor V (e x)‖ ≤
        4*‖realSecondTensor W x‖*‖fderiv ℝ e.symm (e x)‖^2 := by
  have hR : W =ᶠ[𝓝 x] V ∘ e := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact hrel y hy
  have hIx : Function.Injective (fderiv ℝ W x) := by
    rw [hR.fderiv_eq,fderiv_comp x (hV.differentiable (by simp) _) (he.differentiable (by simp) _)]
    exact hI.comp (inverse_chart_derivative_injective e.symm hi he hx)
  refine ⟨hIx,?_⟩
  have hVrel : V =ᶠ[𝓝 (e x)] W ∘ e.symm := by
    filter_upwards [e.open_target.mem_nhds (e.map_source hx)] with y hy
    simpa only [Function.comp_apply,e.right_inv hy] using (hrel (e.symm y) (e.map_target hy)).symm
  have hD : coordDet (fderiv ℝ e.symm (e x)) ≠ 0 :=
    coordDet_fderiv_ne_zero_of_local_inverse e.open_target e.open_source hi.contDiffOn he.contDiffOn
      (fun _ hy => e.map_target hy) (fun y hy => e.right_inv hy) (e.map_source hx)
  have hh := norm_realSecondTensor_comp_smooth hW hi (e x)
    (by simpa only [e.left_inv hx,coordDeriv] using gramDet_ne_zero_of_injective _ hIx) hD
  rw [← (realSecondTensor_eventuallyEq hVrel).eq_of_nhds,e.left_inv hx] at hh
  exact hh

theorem compact_phase_chart_normal_margin
    (e : OpenPartialHomeomorph Base Base) (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {K : Set Base} (hK : IsCompact K) (hKS : K ⊆ e.source) :
    ∃ D : ℝ, 0 < D ∧ ∀ (W V : RField 4), ContDiff ℝ ∞ W → ContDiff ℝ ∞ V →
      (∀ x ∈ e.source, W x = V (e x)) →
      ∀ x ∈ K, Function.Injective (fderiv ℝ V (e x)) →
      ∀ c : ℝ, c < ‖realSecondTensor V (e x)‖ →
        Function.Injective (fderiv ℝ W x) ∧ c/D < ‖realSecondTensor W x‖ := by
  have hd : Continuous (fun x => fderiv ℝ e.symm (e x)) :=
    ((hi.fderiv_right (m := ∞) (by simp)).continuous).comp he.continuous
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn hd.continuousOn
  let D : ℝ := 4*(1+|B|)^2
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D,hD,?_⟩
  intro W V hW hV hrel x hx hI c hc
  obtain ⟨hIx,hbound⟩ := phase_chart_normal_transport e he hi hW hV hrel (hKS hx) hI
  refine ⟨hIx,(div_lt_iff₀ hD).mpr ?_⟩
  have hnorm : ‖fderiv ℝ e.symm (e x)‖ ≤ 1+|B| := (hB x hx).trans (by linarith [le_abs_self B])
  have hb : 4*‖realSecondTensor W x‖*‖fderiv ℝ e.symm (e x)‖^2 ≤
      ‖realSecondTensor W x‖*D := by
    dsimp [D]
    calc
      _ ≤ 4*‖realSecondTensor W x‖*(1+|B|)^2 := by gcongr
      _ = _ := by ring
  exact hc.trans_le (hbound.trans hb)

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
