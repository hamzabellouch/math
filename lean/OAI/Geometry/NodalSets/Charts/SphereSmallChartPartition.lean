import OAI.Geometry.NodalSets.Charts.SphereFiniteSmoothPartition

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set Metric
open scoped Topology ContDiff
noncomputable section

theorem finite_sphere_coordinate_cover_radius (r : ℝ) (hr : 0 < r) :
    ∃ P : Finset Base, ∀ x : Base, ∃ p ∈ P, ∃ z ∈ ball (0 : Yau.Jets.Coord) r,
      sphereChartCoordMap p z = x := by
  have hcover : (univ : Set Base) ⊆ ⋃ p : Base, sphereChartCoordMap p '' ball (0 : Yau.Jets.Coord) r := by
    intro x _
    exact mem_iUnion.mpr ⟨x,0,mem_ball_self hr,sphereChartCoordMap_zero x⟩
  obtain ⟨P,hP⟩ := isCompact_univ.elim_finite_subcover
    (fun p : Base ↦ sphereChartCoordMap p '' ball (0 : Yau.Jets.Coord) r)
    (fun p ↦ sphereChartCoordMap_isOpenMap p _ isOpen_ball) hcover
  refine ⟨P,?_⟩
  intro x
  obtain ⟨p,hp,z,hz,hzx⟩ := mem_iUnion₂.mp (hP (mem_univ x))
  exact ⟨p,hp,z,hz,hzx⟩

theorem sphere_finite_smooth_partition_radius (r : ℝ) (hr : 0 < r) :
    ∃ (P : Finset Base) (theta : {p // p ∈ P} → Base → ℝ),
      (∀ p, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (theta p)) ∧
      (∀ p x, 0 ≤ theta p x) ∧ (∀ x, ∑ p, theta p x=1) ∧
      (∀ p, tsupport (theta p) ⊆ sphereChartCoordMap p.val '' ball (0 : Yau.Jets.Coord) r) ∧
      (∀ p, tsupport (theta p ∘ sphereChartCoordMap p.val) ⊆ closedBall (0 : Yau.Jets.Coord) r) ∧
      (∀ p, HasCompactSupport (theta p ∘ sphereChartCoordMap p.val)) := by
  classical
  obtain ⟨P,hP⟩ := finite_sphere_coordinate_cover_radius r hr
  let U : {p // p ∈ P} → Set Base := fun p ↦ sphereChartCoordMap p.val '' ball (0 : Yau.Jets.Coord) r
  have hcover : (univ : Set Base) ⊆ ⋃ p, U p := by
    intro x _
    obtain ⟨p,hp,z,hz,hzx⟩ := hP x
    exact mem_iUnion.mpr ⟨⟨p,hp⟩,z,hz,hzx⟩
  obtain ⟨theta,hsub⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓡 4) isClosed_univ U
    (fun p ↦ sphereChartCoordMap_isOpenMap p.val _ isOpen_ball) hcover
  have hs (p : {p // p ∈ P}) :
      tsupport (theta p ∘ sphereChartCoordMap p.val) ⊆ closedBall (0 : Yau.Jets.Coord) r := by
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    obtain ⟨y,hy,he⟩ := hsub p (subset_closure hx)
    have hxy : y=x := sphereChartCoordMap_injective p.val he
    exact hxy ▸ ball_subset_closedBall hy
  refine ⟨P,(fun p ↦ theta p),(fun p ↦ (theta p).contMDiff),theta.nonneg,?_,hsub,hs,?_⟩
  · intro x
    have h := theta.sum_eq_one (mem_univ x)
    rw [finsum_eq_sum_of_support_subset _ (s := Finset.univ) (by simp)] at h
    exact h
  · intro p
    exact (isCompact_closedBall (0 : Yau.Jets.Coord) r).of_isClosed_subset isClosed_closure (hs p)

end
end Yau.Target

end OAI
