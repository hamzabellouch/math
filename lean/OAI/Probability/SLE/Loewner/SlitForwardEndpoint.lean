import OAI.Probability.SLE.Loewner.SlitForwardBoundaryHeight
import OAI.Probability.SLE.Geometry.ComplexEndpointLimit
import OAI.Probability.SLE.Loewner.SlitBoundaryFiber

namespace OAI

/-! A continuous curve in a slit domain approaching its boundary has a
real forward-chart limit. No uniqueness of arbitrary boundary fibers is
assumed: the connected cluster set and noncollapse of intervals suffice. -/
noncomputable section
open Set Filter Function Metric Complex
open scoped Topology

namespace SLEExactGauge

theorem SimpleSlitChart.exists_forward_endpoint_limit {p : C(unitInterval,ℂ)}
    (P : SimpleSlitChart p) {z : ℝ → ℂ} {b : ℂ} {D : ℝ}
    (hD : 0<D) (hzC : ContinuousOn z (Ioo 0 D))
    (hz : Tendsto z (𝓝[>] (0:ℝ)) (𝓝 b))
    (hzD : MapsTo z (Ioo 0 D) (upperHalfPlane \ range p))
    (hb : b∉upperHalfPlane \ range p) :
    ∃ a : ℝ, Tendsto (fun t => P.forward (z t)) (𝓝[>] (0:ℝ)) (𝓝 (a:ℂ)) := by
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ), t∈Ioo 0 D :=
    Ioo_mem_nhdsGT hD
  have hvalid : ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ), z t∈upperHalfPlane \ range p :=
    hsmall.mono hzD
  have hnorm : ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ), ‖z t‖≤‖b‖+1 := by
    exact (hz.norm.eventually (gt_mem_nhds (by linarith : ‖b‖<‖b‖+1))).mono
      (fun _ h => h.le)
  obtain ⟨M,hM⟩ := P.forward_bounded_over_ball (‖b‖+1)
  have hbound : ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ), ‖P.forward (z t)‖≤M := by
    filter_upwards [hvalid,hnorm] with t ht htn
    exact hM _ ht htn
  obtain ⟨B,hBC,hBe⟩ := P.exists_boundary_extension
  have himage : Tendsto (fun t => B (P.forward (z t))) (𝓝[>] (0:ℝ)) (𝓝 b) := by
    apply hz.congr'
    filter_upwards [hvalid] with t ht
    exact (hBe _ (P.bijOn.mapsTo ht)).trans (P.left_inverse _ ht) |>.symm
  obtain ⟨a,ha,_⟩ := exists_complex_endpoint_limit hD
    (P.forward_differentiable.continuousOn.comp hzC hzD) hbound
    (hvalid.mono fun _ ht => (show 0<(P.forward _).im from P.bijOn.mapsTo ht).le)
    (P.forward_height_tendsto_zero_filter hz hvalid hb) hBC himage (by
      intro a d had hconst
      apply P.boundary_not_constant_on_interval hBC hBe ((a+d)/2)
        (show 0<(d-a)/2 by linarith) b
      intro y hy
      exact hconst y ⟨by linarith [hy.1],by linarith [hy.2]⟩)
  exact ⟨a,ha⟩

end SLEExactGauge

end

end OAI
