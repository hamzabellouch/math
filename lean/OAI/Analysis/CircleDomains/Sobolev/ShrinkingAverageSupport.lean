import OAI.Analysis.CircleDomains.Sobolev.PositiveLocalAverages
import Mathlib.Topology.MetricSpace.HausdorffDistance

namespace OAI

/-! The geometric shrinking condition on the sampling radius implies the
pointwise support property used for band-preserving positive averages. -/

open Set Filter MeasureTheory Metric
open scoped Topology

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

theorem localAverageSupport_of_tendsto_radius
    (G : Set X) (μ : X → Measure X) (r : X → ℝ) {s : X}
    (hr : Tendsto r (𝓝[G] s) (𝓝 0))
    (hsample : ∀x ∈ G, ∀ᵐ y ∂μ x, y ∈ G ∧ dist y x ≤ r x) :
    LocalAverageSupport G μ s := by
  intro V hV
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV
  have hr' : ∀ᶠ x in 𝓝[G] s, r x < ε / 2 :=
    (tendsto_order.mp hr).2 _ (half_pos hε)
  have hx' : ∀ᶠ x in 𝓝[G] s, dist x s < ε / 2 :=
    nhdsWithin_le_nhds (Metric.ball_mem_nhds s (half_pos hε))
  filter_upwards [self_mem_nhdsWithin, hr', hx'] with x hx hrx hxs
  exact (hsample x hx).mono fun y hy => ⟨hy.1, hball (by
    change dist y s < ε
    have ht := dist_triangle y x s
    linarith [hy.2])⟩

theorem localAverageSupport_of_dust_distance
    (G B : Set X) (μ : X → Measure X) {C : ℝ} {s : X} (hs : s ∈ B)
    (hsample : ∀x ∈ G, ∀ᵐ y ∂μ x,
      y ∈ G ∧ dist y x ≤ C * infDist x B) :
    LocalAverageSupport G μ s := by
  apply localAverageSupport_of_tendsto_radius G μ (fun x => C * infDist x B) _ hsample
  have h : Tendsto (fun x => infDist x B) (𝓝[G] s) (𝓝 (infDist s B)) :=
    ((continuous_infDist_pt B).tendsto s).mono_left nhdsWithin_le_nhds
  simpa only [infDist_zero_of_mem hs, mul_zero] using tendsto_const_nhds.mul h

end CircleDomainRigidity

end OAI
