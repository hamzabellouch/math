import OAI.Analysis.CircleDomains.Sobolev.SmoothRealSphereMaps
import OAI.Analysis.CircleDomains.Topology.SphereNeighborhoods

namespace OAI

/-!
# Trapping the bounded side of a circle-model image

A compact exterior piece has closed image. Its open interior has open
image, and their difference is the image of the boundary circle. A
connected set avoiding that boundary and meeting the open image must
lie entirely in the image. This supplies the topological part of the
uniform bound for finite circle models.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem IsSmoothSphereEquivalence.isOpen_image
    {f fi : Sphere → Sphere} {U V : Set Sphere} (hf : IsSmoothSphereEquivalence f fi U V)
    (hV : IsOpen V) {S : Set Sphere} (hS : IsOpen S) (hSU : S ⊆ U) : IsOpen (f '' S) := by
  have heq : f '' S = V ∩ fi ⁻¹' S := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨hf.mapsTo (hSU hx), ?_⟩
      change fi (f x) ∈ S
      rwa [hf.left_inv x (hSU hx)]
    · rintro ⟨hy, hiy⟩
      exact ⟨fi y, hiy, hf.right_inv y hy⟩
  rw [heq]
  have hc : ContinuousOn fi V := fun y hy => (hf.smooth_inv y hy).1.continuousWithinAt
  exact hc.isOpen_inter_preimage hV hS

theorem connected_set_subset_image_of_boundary_avoidance
    {f fi : Sphere → Sphere} {U V E S A : Set Sphere}
    (hf : IsSmoothSphereEquivalence f fi U V) (hV : IsOpen V)
    (hE : IsCompact E) (hEU : E ⊆ U) (hS : IsOpen S) (hSE : S ⊆ E)
    (hA : IsPreconnected A) (hmeet : (A ∩ f '' S).Nonempty)
    (havoid : Disjoint A (f '' (E \ S))) : A ⊆ f '' S := by
  have hES : f '' S ⊆ f '' E := image_mono hSE
  have hclosed : IsClosed (f '' E) := (hE.image_of_continuousOn
    (fun x hx => (hf.smooth x (hEU hx)).1.continuousWithinAt)).isClosed
  have hcover : A ⊆ f '' S ∪ (f '' E)ᶜ := by
    intro y hy
    by_cases he : y ∈ f '' E
    · obtain ⟨x, hx, rfl⟩ := he
      by_cases hs : x ∈ S
      · exact Or.inl ⟨x, hs, rfl⟩
      · exact (Set.disjoint_left.mp havoid hy ⟨x, ⟨hx, hs⟩, rfl⟩).elim
    · exact Or.inr he
  have hdisj : Disjoint (f '' S) (f '' E)ᶜ := by
    exact disjoint_compl_right.mono_left hES
  exact hA.subset_left_of_subset_union (hf.isOpen_image hV hS (hSE.trans hEU))
    hclosed.isOpen_compl hdisj hcover hmeet

/-- A geometric boundary inclusion traps every exterior target point in
an exterior source image. The coefficient bound will supply the inclusion. -/
theorem sphere_exterior_subset_image
    {f fi : Sphere → Sphere} {U V : Set Sphere} (hf : IsSmoothSphereEquivalence f fi U V)
    (hV : IsOpen V) {r L : ℝ} (_hr : 0 < r) (hL : 0 ≤ L)
    (hEU : ((((↑) : ℂ → Sphere) '' Metric.ball 0 r)ᶜ) ⊆ U)
    (hfix : f OnePoint.infty = OnePoint.infty)
    (hboundary : ∀ z : ℂ, ‖z‖ = r → f (z : Sphere) ∈
      ((↑) : ℂ → Sphere) '' Metric.closedBall 0 L) :
    ((((↑) : ℂ → Sphere) '' Metric.closedBall 0 L)ᶜ) ⊆
      f '' ((((↑) : ℂ → Sphere) '' Metric.closedBall 0 r)ᶜ) := by
  let E : Set Sphere := (((↑) : ℂ → Sphere) '' Metric.ball 0 r)ᶜ
  let S : Set Sphere := (((↑) : ℂ → Sphere) '' Metric.closedBall 0 r)ᶜ
  let A : Set Sphere := (((↑) : ℂ → Sphere) '' Metric.closedBall 0 L)ᶜ
  have hE : IsCompact E := (OnePoint.isOpen_image_coe.mpr Metric.isOpen_ball).isClosed_compl.isCompact
  have hS : IsOpen S := ((isCompact_closedBall (0 : ℂ) r).image OnePoint.continuous_coe).isClosed.isOpen_compl
  have hSE : S ⊆ E := compl_subset_compl.mpr (image_mono Metric.ball_subset_closedBall)
  have hinfS : OnePoint.infty ∈ S := by simp [S]
  have hmeet : (A ∩ f '' S).Nonempty := by
    refine ⟨OnePoint.infty, ?_, OnePoint.infty, hinfS, hfix⟩
    simp [A]
  apply connected_set_subset_image_of_boundary_avoidance hf hV hE hEU hS hSE
    (isConnected_sphere_exterior_closedBall (0 : ℂ) hL).isPreconnected hmeet
  apply Set.disjoint_left.mpr
  rintro y hy ⟨x, hx, rfl⟩
  cases x using OnePoint.rec with
  | infty => exact hx.2 hinfS
  | coe z =>
    have hnlo : r ≤ ‖z‖ := by
      have hz : z ∉ Metric.ball (0 : ℂ) r := by
        intro hz
        exact hx.1 ⟨z, hz, rfl⟩
      simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hz
    have hnhi : ‖z‖ ≤ r := by
      have hz : (z : Sphere) ∈ ((↑) : ℂ → Sphere) '' Metric.closedBall 0 r :=
        not_not.mp hx.2
      obtain ⟨w, hw, hwz⟩ := hz
      have heq : w = z := OnePoint.coe_injective hwz
      simpa only [heq, Metric.mem_closedBall, dist_zero_right] using hw
    exact hy (hboundary z (le_antisymm hnhi hnlo))

end CircleDomainRigidity

end

end OAI
