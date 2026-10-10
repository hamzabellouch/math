import OAI.Geometry.SurfaceImmersion.Geometry.SphericalJets
import OAI.Geometry.Immersion.ClosedSurface.SecondForms
import OAI.Geometry.Immersion.ClosedSurface.ChartModel

namespace OAI

/-! The coordinate normal projection is the Euclidean orthogonal projection
onto the complement of the actual tangent image. -/
noncomputable section
open Set
open scoped Matrix
namespace ClosedSurfaceR4
open RealModes SmallModes

lemma realNormalPart_starProjection (L : SmallModes.Base →L[ℝ] Space) (W : Space)
    (hD : NormalFrame.gramDet (spaceCoordinates (L dx)) (spaceCoordinates (L dy)) ≠ 0) :
    realNormalPart (spaceCoordinates (L dx)) (spaceCoordinates (L dy)) (spaceCoordinates W) =
      spaceCoordinates ((LinearMap.range L.toLinearMap)ᗮ.starProjection W) := by
  let X := spaceCoordinates (L dx)
  let Y := spaceCoordinates (L dy)
  let Z := spaceCoordinates W
  let a := ((Y ⬝ᵥ Y)*(X ⬝ᵥ Z)-(X ⬝ᵥ Y)*(Y ⬝ᵥ Z))/NormalFrame.gramDet X Y
  let b := ((X ⬝ᵥ X)*(Y ⬝ᵥ Z)-(X ⬝ᵥ Y)*(X ⬝ᵥ Z))/NormalFrame.gramDet X Y
  let V := W-a • L dx-b • L dy
  have hV : spaceCoordinates V = realNormalPart X Y Z := by
    simp only [V,map_sub,map_smul,realNormalPart]
    rfl
  have hperp := realNormalPart_perp X Y Z hD
  have hinnerx : inner ℝ (L dx) V = 0 := by
    rw [← spaceCoordinates_dot,hV]
    exact hperp.1
  have hinnery : inner ℝ (L dy) V = 0 := by
    rw [← spaceCoordinates_dot,hV]
    exact hperp.2
  have hm : V ∈ (LinearMap.range L.toLinearMap)ᗮ := by
    rw [Submodule.mem_orthogonal]
    rintro _ ⟨v,rfl⟩
    change inner ℝ (L v) V = 0
    rw [base_eq_basis v,map_add,map_smul,map_smul,inner_add_left,
      real_inner_smul_left,real_inner_smul_left,hinnerx,hinnery]
    ring
  have ht : W-V ∈ LinearMap.range L.toLinearMap := by
    refine ⟨a • dx+b • dy,?_⟩
    change L (a • dx+b • dy) = W-V
    simp only [map_add,map_smul,V]
    module
  have hp : W-V ∈ ((LinearMap.range L.toLinearMap)ᗮ)ᗮ :=
    (LinearMap.range L.toLinearMap).le_orthogonal_orthogonal ht
  have he := Submodule.eq_starProjection_of_mem_orthogonal hm hp
  exact hV.symm.trans (congrArg spaceCoordinates he.symm)

end ClosedSurfaceR4

end

end OAI
