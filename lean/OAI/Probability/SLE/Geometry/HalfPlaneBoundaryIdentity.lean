import OAI.Probability.SLE.Geometry.HolomorphicAcrossReal
import OAI.Probability.SLE.Geometry.HalfPlaneBoundaryExtension
import Mathlib.Topology.Piecewise

namespace OAI

/-! A holomorphic upper-half-plane function continuous at a real interval
and constant there is constant on an adjacent upper half disk. -/
noncomputable section
open Complex Set Filter Metric
open scoped Topology

namespace SLEExactGauge

theorem halfPlane_boundary_identity {f : ℂ → ℂ}
    (hC : ContinuousOn f {z : ℂ | 0≤z.im})
    (hf : DifferentiableOn ℂ f upperHalfPlane) (x : ℝ) {r : ℝ} (hr : 0<r) (c : ℂ)
    (hb : ∀ z∈ball (x:ℂ) r, z.im=0 → f z=c) :
    ∀ z∈ball (x:ℂ) r, 0<z.im → f z=c := by
  let g : ℂ → ℂ := fun z => if 0≤z.im then f z-c else 0
  have hclosed : IsClosed {z : ℂ | 0≤z.im} := isClosed_le continuous_const continuous_im
  have hgC : ContinuousOn g (ball (x:ℂ) r) := by
    apply ContinuousOn.if
    · intro z hz
      have he : z.im=0 := (frontier_le_subset_eq continuous_const continuous_im hz.2).symm
      exact sub_eq_zero.mpr (hb z hz.1 he)
    · exact (hC.sub continuousOn_const).mono (fun _ hz => hclosed.closure_eq ▸ hz.2)
    · exact continuousOn_const
  have hgD : DifferentiableOn ℂ g (ball (x:ℂ) r) := by
    apply differentiableOn_of_continuousOn_off_real isOpen_ball hgC
    intro z _ hz
    rcases lt_or_gt_of_ne hz with hn | hp
    · apply (differentiableAt_const (c := (0:ℂ))).congr_of_eventuallyEq
      filter_upwards [continuous_im.isOpen_preimage _ isOpen_Iio |>.mem_nhds hn] with w hw
      simp only [g,ite_eq_right (not_le_of_gt (show w.im<0 from hw))]
    · apply ((hf.differentiableAt (isOpen_upperHalfPlane.mem_nhds hp)).sub_const c).congr_of_eventuallyEq
      filter_upwards [isOpen_upperHalfPlane.mem_nhds hp] with w hw
      simp only [g,ite_eq_left (show 0<w.im from hw).le]
  let a : ℂ := (x:ℂ)-((r/2:ℝ):ℂ)*I
  have ha : a∈ball (x:ℂ) r := by
    rw [mem_ball,dist_eq_norm]
    have he : a-(x:ℂ)=-(((r/2:ℝ):ℂ)*I) := by dsimp [a]; ring
    rw [he,norm_neg,norm_mul,norm_I,mul_one,norm_real,Real.norm_eq_abs,abs_of_pos (half_pos hr)]
    linarith
  have haim : a.im<0 := by
    dsimp [a]
    simp only [ofReal_im,mul_im,ofReal_re,I_im,mul_one,I_re,mul_zero,add_zero,zero_sub]
    linarith
  have hga : g =ᶠ[𝓝 a] 0 := by
    filter_upwards [continuous_im.isOpen_preimage _ isOpen_Iio |>.mem_nhds haim] with w hw
    simp only [g,ite_eq_right (not_le_of_gt (show w.im<0 from hw)),Pi.zero_apply]
  have hzero := (hgD.analyticOnNhd isOpen_ball).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball (x:ℂ) r).isPreconnected ha hga
  intro z hz hp
  have he := hzero hz
  simpa only [g,ite_eq_left hp.le,Pi.zero_apply,sub_eq_zero] using he

end SLEExactGauge

end

end OAI
