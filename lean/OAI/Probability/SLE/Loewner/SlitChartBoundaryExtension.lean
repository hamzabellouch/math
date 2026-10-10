import OAI.Probability.SLE.Loewner.SlitChartBoundaryShrink
import OAI.Probability.SLE.Geometry.HalfPlaneBoundaryExtension

namespace OAI

/-! Continuous finite boundary values of the normalized static slit inverse. -/
noncomputable section
open Set Filter Metric Function
open scoped Topology

namespace SLEExactGauge

lemma SimpleSlitChart.finite_real_boundary_limit
    {arc : C(unitInterval,ℂ)} (P : SimpleSlitChart arc) (x : ℝ) :
    ∃ z : ℂ, Tendsto (P.inverse) (𝓝[upperHalfPlane] (x:ℂ)) (𝓝 z) := by
  have hx : (x:ℂ)∈closure upperHalfPlane :=
    closedHalfPlane_subset_closure_upperHalfPlane (by simp)
  have : NeBot (𝓝[upperHalfPlane] (x:ℂ)) := mem_closure_iff_nhdsWithin_neBot.mp hx
  apply cauchy_map_iff_exists_tendsto.mp
  apply Metric.cauchy_iff.mpr
  refine ⟨inferInstance,fun ε hε => ?_⟩
  obtain ⟨r,hr,z,hsmall⟩ := P.small_boundary_halfdisk x (ε/3) (by positivity)
  refine ⟨P.inverse '' (upperHalfPlane∩ball (x:ℂ) r),?_,?_⟩
  · change (P.inverse) ⁻¹' (P.inverse '' (upperHalfPlane∩ball (x:ℂ) r))∈𝓝[upperHalfPlane] (x:ℂ)
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (x:ℂ) hr)] with w hwH hwr
    exact ⟨w,⟨hwH,hwr⟩,rfl⟩
  · rintro a ⟨u,hu,rfl⟩ b ⟨v,hv,rfl⟩
    have hsu := hsmall u hu.1 hu.2
    have hsv := hsmall v hv.1 hv.2
    have htri := dist_triangle (P.inverse u) z (P.inverse v)
    rw [dist_comm z (P.inverse v)] at htri
    linarith

theorem SimpleSlitChart.exists_boundary_extension
    {arc : C(unitInterval,ℂ)} (P : SimpleSlitChart arc) :
    ∃ Fbar : ℂ → ℂ, ContinuousOn Fbar {z : ℂ | 0≤z.im} ∧
      ∀ z∈upperHalfPlane, Fbar z=P.inverse z :=
  exists_halfPlane_boundary_extension P.inverse_differentiable.continuousOn
    P.finite_real_boundary_limit

end SLEExactGauge

end

end OAI
