import OAI.Geometry.SurfaceImmersion.Atlas.TransverseSheetCoordinates

namespace OAI

/-! A regular transverse double point of the actual surface map has
simultaneous smooth source charts and transverse target coordinate planes. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]

theorem regular_double_point_normal_form {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    {x y : M} (hxy : x ≠ y) (heq : f x = f y)
    (hreg : Function.Surjective (surfacePairDerivative f x y))
    (hx : Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x))
    (hy : Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f y)) :
    Nonempty (TransverseSheetCoordinates f x y) := by
  let p : surfaceDoublePairs f := ⟨(x,y),hxy,heq⟩
  obtain ⟨c,hpc⟩ := exists_smooth_double_chart hf p hreg
  have hback : c.coord.symm (c.coord p) = p := c.coord.left_inv hpc
  have hreg' : Function.Surjective (surfacePairDerivative f
      (c.coord.symm (c.coord p)).val.1 (c.coord.symm (c.coord p)).val.2) := by
    rw [hback]
    exact hreg
  have hx' : Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f
      (c.coord.symm (c.coord p)).val.1) := by
    rw [hback]
    exact hx
  have hy' : Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f
      (c.coord.symm (c.coord p)).val.2) := by
    rw [hback]
    exact hy
  obtain ⟨m⟩ := c.adapted_sheet_models hf (c.coord.map_source hpc) hreg' hx' hy'
  have hm := m.simultaneous_coordinates
  rw [hback] at hm
  exact hm

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
