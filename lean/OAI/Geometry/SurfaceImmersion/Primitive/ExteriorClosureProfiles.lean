import OAI.Geometry.SurfaceImmersion.Geometry.ExteriorClosureBounds
import OAI.Geometry.SurfaceImmersion.Primitive.ExteriorProfileBounds

namespace OAI

/-! The unscaled profile bound includes the closure of the open exterior. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial RealModes SmallModes GeometryPreservation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem exterior_profile_bound_closure (j : A.centers) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ F G V W : M → Space,
      ContMDiff planeModel spaceModel ∞ F → ContMDiff planeModel spaceModel ∞ G →
      ContMDiff planeModel spaceModel ∞ V → ContMDiff planeModel spaceModel ∞ W →
      ∀ b c : ℝ, 0 ≤ b → 0 ≤ c →
      A.WeightedBound 1 2 b (G-F) → A.WeightedBound 1 2 c (W-V) →
      ∀ O : Set M, (∀ q ∈ O, V =ᶠ[𝓝 q] G) →
      ∀ p ∈ closure O, p ∈ tsupport (A.weight j) →
      ‖realBoundaryProfile (spaceCoordinates ∘ A.vectorPlaneRead j W) 1
        (planeCoordinateIsometry (chart (j : M) p))-
        realBoundaryProfile (spaceCoordinates ∘ A.vectorPlaneRead j F) 1
        (planeCoordinateIsometry (chart (j : M) p))‖ ≤ D*(b+c) := by
  obtain ⟨D,hD,hbound⟩ := A.exterior_read_C2_bound_closure j
  refine ⟨D,hD,?_⟩
  intro F G V W hF hG hV hW b c hb hc hGF hWV O hext p hpO hp
  have hF' := spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth j hF)
  have hW' := spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth j hW)
  rw [← realBoundaryProfile_sub hF' hW']
  have heq : (spaceCoordinates ∘ A.vectorPlaneRead j W)-(spaceCoordinates ∘ A.vectorPlaneRead j F) =
      spaceCoordinates ∘ A.vectorPlaneRead j (W-F) := by
    rw [A.vectorPlaneRead_sub]
    funext y
    exact (map_sub spaceCoordinates _ _).symm
  rw [heq]
  exact realBoundaryProfile_one_bound
    (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth j (hW.sub hF))) _
    (mul_nonneg hD (add_nonneg hb hc)) (hbound F G V W hF hG hV hW b c hb hc hGF hWV O hext p hpO hp)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
