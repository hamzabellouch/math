import OAI.Geometry.SurfaceImmersion.Atlas.AtlasFiniteCancellation
import OAI.Geometry.SurfaceImmersion.Geometry.VectorReadBounds

namespace OAI

/-! Weighted bounds for the exact coordinate maps entering the polynomial metric. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem jetPlaneRead_bound (i : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (F : M → Space), ContMDiff planeModel spaceModel ∞ F →
      ∀ τ C : ℝ, 0 < τ → τ ≤ 1 → 0 ≤ C → A.WeightedBound τ m C F →
      WeightedEstimates.WeightedBound univ τ m (D*C)
        (A.jetChartMap i F ∘ planeCoordinateIsometry.symm) := by
  obtain ⟨D,hD,hd⟩ := A.vectorPlaneRead_bound (V := Space) i m
  refine ⟨‖spaceCoordinates.toContinuousLinearMap‖*D,mul_nonneg (norm_nonneg _) hD,?_⟩
  intro F hF τ C hτ hτ1 hC hb
  rw [A.jetChartMap_plane]
  have hh := (hd F τ C hτ hτ1 hC hF hb).linear uniqueDiffOn_univ hτ.le
    (A.vectorPlaneRead_smooth i hF).contDiffOn spaceCoordinates.toContinuousLinearMap
  simpa only [mul_assoc,ContinuousLinearEquiv.coe_coe] using hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
