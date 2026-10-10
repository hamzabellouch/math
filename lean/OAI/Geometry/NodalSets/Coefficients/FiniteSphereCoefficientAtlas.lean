import OAI.Geometry.NodalSets.Charts.SphereChartTransition

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set Metric
open scoped ContDiff
noncomputable section
local instance sphereCoefficientAtlasDim : Fact (Module.finrank ℝ AmbientBase = 4+1) := ⟨by simp [AmbientBase]⟩

lemma finiteAtlas_sphereChartCoordMap_isOpenMap (p : Base) : IsOpenMap (sphereChartCoordMap p) := by
  intro U hU
  have he : sphereChartCoordMap p '' U =
      (extChartAt (𝓡 4) p).symm '' (seedCoordEquiv '' U) := (image_image ((extChartAt (𝓡 4) p).symm) seedCoordEquiv U).symm
  rw [he]
  change IsOpen ((stereographic' 4 (-p)).symm '' (seedCoordEquiv '' U))
  exact (stereographic' 4 (-p)).isOpen_image_symm_of_subset_target
    (seedCoordEquiv.isOpenMap U hU) (by simp)

lemma finiteAtlas_sphereChartCoordMap_zero (p : Base) : sphereChartCoordMap p 0 = p := by
  simp only [sphereChartCoordMap,map_zero,centeredSphereChart_inverse_zero]

theorem finite_sphere_coordinate_cover :
    ∃ P : Finset Base, ∀ x : Base, ∃ p ∈ P, ∃ z ∈ ball (0 : Yau.Jets.Coord) 1,
      sphereChartCoordMap p z = x := by
  have hcover : (univ : Set Base) ⊆ ⋃ p : Base, sphereChartCoordMap p '' ball (0 : Yau.Jets.Coord) 1 := by
    intro x _
    exact mem_iUnion.mpr ⟨x,0,mem_ball_self (by norm_num),finiteAtlas_sphereChartCoordMap_zero x⟩
  obtain ⟨P,hP⟩ := isCompact_univ.elim_finite_subcover
    (fun p : Base ↦ sphereChartCoordMap p '' ball (0 : Yau.Jets.Coord) 1)
    (fun p ↦ finiteAtlas_sphereChartCoordMap_isOpenMap p _ isOpen_ball) hcover
  refine ⟨P,?_⟩
  intro x
  obtain ⟨p,hp,z,hz,hzx⟩ := mem_iUnion₂.mp (hP (mem_univ x))
  exact ⟨p,hp,z,hz,hzx⟩

end
end Yau.Target

end OAI
