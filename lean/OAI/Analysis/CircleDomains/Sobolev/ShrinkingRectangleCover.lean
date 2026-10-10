import OAI.Analysis.CircleDomains.Topology.EuclideanPlaneCoordinates
import OAI.Analysis.CircleDomains.Topology.RectangleNeighborhoods
import Mathlib.Topology.MetricSpace.HausdorffDistance

namespace OAI

/-! Compact coordinate rectangles whose images have diameter controlled
by the distance to the dust. These are the sampling patches for smoothing. -/

open Set Metric

namespace CircleDomainRigidity

theorem dist_le_infDist_of_small_ball
    {X : Type*} [MetricSpace X] (B : Set X) {c x y : X}
    (hx : x ∈ ball c (infDist c B / 4)) (hy : y ∈ ball c (infDist c B / 4)) :
    dist y x ≤ infDist x B := by
  have hxc : dist c x < infDist c B / 4 := by simpa only [mem_ball, dist_comm] using hx
  have hyc : dist y c < infDist c B / 4 := hy
  have hi := infDist_le_infDist_add_dist (x := c) (y := x) (s := B)
  have ht := dist_triangle y c x
  linarith [infDist_nonneg (x := c) (s := B)]

theorem exists_small_closed_coordinate_rectangle
    {X : Type*} [MetricSpace X] {Ω : Set EuclideanPlane} (hΩ : IsOpen Ω)
    (q : EuclideanPlane → X) (hq : ContinuousOn q Ω)
    (B : Set X) (hB : IsClosed B) (hne : B.Nonempty)
    {x : EuclideanPlane} (hx : x ∈ Ω) (hqx : q x ∉ B) :
    ∃a b c d : ℝ, a < b ∧ c < d ∧
      euclideanPlaneCoordinates x ∈ Ioo a b ×ˢ Ioo c d ∧
      (euclideanPlaneCoordinates ⁻¹' (Icc a b ×ˢ Icc c d) ⊆ Ω) ∧
      (∀y ∈ euclideanPlaneCoordinates ⁻¹' (Icc a b ×ˢ Icc c d),
        ∀z ∈ euclideanPlaneCoordinates ⁻¹' (Icc a b ×ˢ Icc c d),
          dist (q y) (q z) ≤ infDist (q z) B) := by
  let V := Ω ∩ q ⁻¹' ball (q x) (infDist (q x) B / 4)
  have hδ : 0 < infDist (q x) B / 4 := div_pos
    ((hB.notMem_iff_infDist_pos hne).1 hqx) (by norm_num)
  have hV : IsOpen V := hq.isOpen_inter_preimage hΩ isOpen_ball
  have hxV : x ∈ V := ⟨hx, mem_ball_self hδ⟩
  have hVe : IsOpen (euclideanPlaneCoordinates '' V) :=
    euclideanPlaneCoordinates.toHomeomorph.isOpenMap V hV
  obtain ⟨a, b, c, d, hab, hcd, hpoint, hrect⟩ := exists_closed_rectangle_inside_open hVe
    (mem_image_of_mem euclideanPlaneCoordinates hxV)
  have hsub : euclideanPlaneCoordinates ⁻¹' (Icc a b ×ˢ Icc c d) ⊆ V := by
    intro y hy
    obtain ⟨z, hz, heq⟩ := hrect hy
    exact euclideanPlaneCoordinates.injective heq ▸ hz
  refine ⟨a, b, c, d, hab, hcd, hpoint, hsub.trans inter_subset_left, ?_⟩
  intro y hy z hz
  exact dist_le_infDist_of_small_ball B (hsub hz).2 (hsub hy).2

end CircleDomainRigidity

end OAI
