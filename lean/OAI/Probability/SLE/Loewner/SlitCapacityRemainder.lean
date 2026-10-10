import OAI.Probability.SLE.Geometry.ExteriorCapacityRemainder
import OAI.Probability.SLE.Loewner.ReflectedExteriorHeight

namespace OAI

/-! The local Loewner kernel estimate for an arbitrary simple attached
slit, with error proportional to its exact capacity. -/
noncomputable section
open Set Filter Function Complex Metric
open scoped Topology

namespace SLEExactGauge

lemma reflectedArcSet_norm_lt {p : C(unitInterval,ℂ)} {R : ℝ}
    (hp : ∀ t : unitInterval, ‖p t‖<R) {z : ℂ} (hz : z∈reflectedArcSet p) : ‖z‖<R := by
  rcases hz with ⟨t,rfl⟩|⟨w,⟨t,rfl⟩,rfl⟩
  · exact hp t
  · simpa only [Complex.norm_conj] using hp t

theorem SimpleSlitChart.forward_kernel_remainder {p : C(unitInterval,ℂ)}
    (P : SimpleSlitChart p) (hi : Injective p) (h0 : p 0=0)
    (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {R : ℝ} (hR : 0<R) (hp : ∀ t : unitInterval, ‖p t‖<R)
    {z : ℂ} (hzH : z∈upperHalfPlane) (hz : 2*R≤‖z‖) :
    ‖P.forward z-z-(P.capacity:ℂ)/z‖≤10*P.capacity*R/‖z‖^2 := by
  obtain ⟨Q⟩ := exists_reflectedCapacityChart p hi h0 hH
  have hK : IsCompact (reflectedArcSet p) := (isCompact_range p.continuous).union
    ((isCompact_range p.continuous).image Complex.continuous_conj)
  have hnot (w : ℂ) (hw : R≤‖w‖) : w∉reflectedArcSet p :=
    fun h => (not_lt_of_ge hw) (reflectedArcSet_norm_lt hp h)
  have hG (w : ℂ) (hw : R≤‖w‖) : DifferentiableAt ℂ Q.chart.forward w :=
    (Q.forward_differentiable h0).differentiableAt (hK.isClosed.isOpen_compl.mem_nhds (hnot w hw))
  have hs (w : ℂ) (hw : R≤‖w‖) : w.im*(Q.chart.forward w-w).im≤0 :=
    Q.height_displacement_sign (hnot w hw)
  have hb := exterior_capacity_remainder hR Q.chart.capacity_pos hG Q.chart.coefficient hs hz
  have hnorm : R≤‖z‖ := by linarith
  have hzP : z∈upperHalfPlane \ range p := ⟨hzH,fun h => hnot z hnorm (Or.inl h)⟩
  obtain ⟨he,_,hc⟩ := P.unique_on_domain Q.chart
  rwa [← he hzP,← hc] at hb

end SLEExactGauge

end

end OAI
