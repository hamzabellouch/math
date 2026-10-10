import Mathlib.Geometry.Manifold.PartitionOfUnity
import OAI.Geometry.NodalSets.Charts.SphereChartOpenMap
import OAI.Geometry.NodalSets.Coefficients.FiniteSphereCoefficientAtlas

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set Metric
open scoped Topology ContDiff
noncomputable section

theorem sphere_finite_smooth_partition :
    ∃ (P : Finset Base) (theta : {p // p ∈ P} → Base → ℝ),
      (∀ p, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (theta p)) ∧
      (∀ p x, 0 ≤ theta p x) ∧ (∀ x, ∑ p, theta p x=1) ∧
      (∀ p, tsupport (theta p) ⊆ sphereChartCoordMap p.val '' ball (0 : Yau.Jets.Coord) 1) ∧
      (∀ p, tsupport (theta p ∘ sphereChartCoordMap p.val) ⊆ closedBall (0 : Yau.Jets.Coord) 1) ∧
      (∀ p, HasCompactSupport (theta p ∘ sphereChartCoordMap p.val)) := by
  classical
  obtain ⟨P,hP⟩ := finite_sphere_coordinate_cover
  let U : {p // p ∈ P} → Set Base := fun p ↦ sphereChartCoordMap p.val '' ball (0 : Yau.Jets.Coord) 1
  have hcover : (univ : Set Base) ⊆ ⋃ p, U p := by
    intro x _
    obtain ⟨p,hp,z,hz,hzx⟩ := hP x
    exact mem_iUnion.mpr ⟨⟨p,hp⟩,z,hz,hzx⟩
  obtain ⟨theta,hsub⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓡 4) isClosed_univ U
    (fun p ↦ sphereChartCoordMap_isOpenMap p.val _ isOpen_ball) hcover
  have hs (p : {p // p ∈ P}) :
      tsupport (theta p ∘ sphereChartCoordMap p.val) ⊆ closedBall (0 : Yau.Jets.Coord) 1 := by
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
    exact (isCompact_closedBall (0 : Yau.Jets.Coord) 1).of_isClosed_subset isClosed_closure (hs p)

end
end Yau.Target

end OAI
