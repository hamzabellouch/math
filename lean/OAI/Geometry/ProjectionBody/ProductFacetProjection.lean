import OAI.Geometry.ProjectionBody.ProductFacetGraphs
import OAI.Geometry.ProjectionBody.GraphProjection

namespace OAI

noncomputable section
open scoped RealInnerProductSpace

namespace ProjectionCounterexample

/-- The true projected area scale of each product facet chart. -/
theorem productFacetProjection_normDet (i : Bool × Option (Fin 10))
    {u : E 20} (hu : ‖u‖ = 1) :
    ((project u).toLinearMap.comp (productFacetLinear i)).normDet =
      |productFunctional i u| := by
  rcases i with ⟨b, i⟩
  cases b
  · cases i with
    | none =>
      rw [productFacetLinear_first_sum, graphProjection_normDet _ _ hu,
        firstSumGraph_normal_inner]
      rfl
    | some i =>
      rw [productFacetLinear_first_coordinate, coordinateProjection_normDet _ hu]
      simp [firstBlock]
  · cases i with
    | none =>
      rw [productFacetLinear_second_sum, graphProjection_normDet _ _ hu,
        secondSumGraph_normal_inner]
      rfl
    | some i =>
      rw [productFacetLinear_second_coordinate, coordinateProjection_normDet _ hu]
      simp [secondBlock]

end ProjectionCounterexample

end

end OAI
