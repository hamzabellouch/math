import Mathlib
import OAI.Geometry.WeakMTW.Coordinates.NormalRigidity
import OAI.Geometry.WeakMTW.Coordinates.NormalMetricSpeed

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace RiemannianLocal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]
open NormalNeighborhood NormalFlow ChartMetric CoordinateGeometry

 theorem intrinsic_curve_normal (x : M) {U : Set ℝ} (hU : IsOpen U)
    {c : ℝ → E} (hc : ContDiffOn ℝ ∞ c U)
    (hct : ∀ t ∈ U, c t ∈ (chartAt E x).target)
    {a C : ℝ} (ha : a ∈ U) (hC : 0 ≤ C)
    (hdist : ∀ s ∈ U, ∀ t ∈ U,
      dist ((chartAt E x).symm (c s)) ((chartAt E x).symm (c t)) = C * |s - t|)
    {y₀ : E} (N : NormalFlow (metric x) (chartAt E x).target y₀)
    (hzero : (0 : E) ∈ (N.normalAt (c a)).source) :
    ∃ δ : ℝ, 0 < δ ∧ Metric.ball a δ ⊆ U ∧
      ∀ t ∈ Metric.ball a δ, c t = N.normalAt (c a) (((t - a) / N.time) • deriv c a) := by
  let e := chartAt E x
  let z := e.symm (c a)
  have hz : z ∈ e.source := e.map_target (hct a ha)
  have hcz : e z = c a := e.right_inv (hct a ha)
  have hca := (hc a ha).contDiffAt (hU.mem_nhds ha)
  have hγc : ContinuousAt (fun t => e.symm (c t)) a :=
    (e.symm.continuousAt (hct a ha)).comp hca.continuousAt
  have hn := hγc (eventually_dist_normal x z N hz (by
    change (0 : E) ∈ (N.normalAt (e z)).source
    rw [hcz]
    exact hzero))
  have hNcenter : c a ∈ (N.normalAt (c a)).target := by
    simpa only [N.normalAt_zero e.open_target (metric_smooth x)
      (fun z hz v hv => metric_positive x hz hv) hzero] using
        (N.normalAt (c a)).map_source hzero
  have hNt := hca.continuousAt.preimage_mem_nhds
    ((N.normalAt (c a)).open_target.mem_nhds hNcenter)
  obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (hU.mem_nhds ha) (inter_mem hNt hn))
  have hsub : Metric.ball a δ ⊆ U := fun t ht => (hδs ht).1
  have hnt : ∀ t ∈ Metric.ball a δ, c t ∈ (N.normalAt (c a)).target :=
    fun t ht => (hδs ht).2.1
  have hsp : ∀ t ∈ Metric.ball a δ,
      metric x (c t) (deriv c t) (deriv c t) = C ^ 2 := by
    intro t ht
    apply coordinate_speed_of_local_distance x
      (((hc t (hsub ht)).contDiffAt (hU.mem_nhds (hsub ht))).differentiableAt (by simp)).hasDerivAt
      (hct t (hsub ht)) hC
    filter_upwards [hU.mem_nhds (hsub ht)] with r hr
    rw [hdist t (hsub ht) r hr, abs_sub_comm t r]
  have hr : ∀ t ∈ Metric.ball a δ, N.time ^ 2 * metric x (c a)
      ((N.normalAt (c a)).symm (c t)) ((N.normalAt (c a)).symm (c t)) =
      C ^ 2 * (t - a) ^ 2 := by
    intro t ht
    have hd := (hδs ht).2.2
    change dist z (e.symm (c t)) = N.time * Real.sqrt (metric x (e z)
      ((N.normalAt (e z)).symm (e (e.symm (c t))))
      ((N.normalAt (e z)).symm (e (e.symm (c t))))) at hd
    rw [hcz, e.right_inv (hct t (hsub ht))] at hd
    have heq := hdist a ha t (hsub ht)
    change dist z (e.symm (c t)) = C * |a - t| at heq
    rw [heq] at hd
    have hh := congrArg (fun r : ℝ => r ^ 2) hd
    rw [mul_pow, mul_pow, Real.sq_sqrt (RadialCoordinates.metric_nonneg
      (fun v hv => metric_positive x (hct a ha) hv) _), sq_abs] at hh
    simpa only [sub_sq_comm a t] using hh.symm
  refine ⟨δ, hδ, hsub, ?_⟩
  exact N.normal_radial_curve e.open_target (metric_smooth x)
    (fun y _ => metric_symmetric x y) (fun y hy v hv => metric_positive x hy hv) hzero
    Metric.isOpen_ball (convex_ball a δ) ((hc.mono hsub).differentiableOn (by simp)) hnt
    (Metric.mem_ball_self hδ) rfl hsp hr
end
end RiemannianLocal
end

end WeakMTWGlobalSupport

end OAI
