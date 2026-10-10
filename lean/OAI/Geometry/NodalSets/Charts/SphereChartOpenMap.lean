import OAI.Geometry.NodalSets.Charts.SphereMeasureChartGeometry

namespace OAI

namespace Yau.Target
open Manifold Set Topology
noncomputable section
local instance sphereChartOpenMapLocal1 : Fact (Module.finrank ℝ AmbientBase = 4+1) := ⟨by simp [AmbientBase]⟩

lemma sphereChartCoordMap_isOpenMap (p : Base) : IsOpenMap (sphereChartCoordMap p) := by
  intro U hU
  have he : sphereChartCoordMap p '' U =
      (chartAt BaseModel p).symm '' (seedCoordEquiv '' U) := by
    rw [Set.image_image]
    rfl
  rw [he]
  apply (chartAt BaseModel p).symm.isOpen_image_of_subset_source
    (seedCoordEquiv.toHomeomorph.isOpenMap _ hU)
  intro z hz
  change z ∈ (stereographic' 4 (-p)).target
  simp

lemma sphereChartCoordMap_isOpenEmbedding (p : Base) : IsOpenEmbedding (sphereChartCoordMap p) :=
  .of_continuous_injective_isOpenMap (sphereChartCoordMap_smooth p).continuous
    (sphereChartCoordMap_injective p) (sphereChartCoordMap_isOpenMap p)

lemma sphereChartCoordMap_zero (p : Base) : sphereChartCoordMap p 0 = p := by
  unfold sphereChartCoordMap
  rw [map_zero,centeredSphereChart_inverse_zero]

end
end Yau.Target

end OAI
