import OAI.Geometry.SurfaceImmersion.Correction.AdaptiveExactCorrection
import OAI.Geometry.SurfaceImmersion.Correction.AtlasCorrectionBudget

namespace OAI

/-! The constructed exact correction retains the C² geometry budget. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open ExactCorrection
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
variable {g : SmoothMetric M} {F : M → Space} {d : CorrectionGeometry g F}
namespace PreparedCorrection

/-- The same, concretely constructed limit is isometric and close in C² to
both the initial stage and the fixed reference immersion. -/
theorem exact_correction_with_control (c : PreparedCorrection d)
    (hF : ContMDiff planeModel spaceModel ∞ F) {t : ℝ} (ht : 0 < t) (htsmall : t ≤ 1/32)
    (seed : c.Stage t 0) :
    ∃ G : M → Space, IsSmoothIsometricImmersion M g G ∧
      d.A.WeightedBound 1 2 (2*c.ρ*t) (G-seed.map) ∧
      d.A.WeightedBound 1 2 (c.ρ/4) (G-F) := by
  exact ⟨_,c.sequence_limit_isometric hF ht htsmall seed,
    c.limit_seed_displacement_bound hF ht htsmall seed,
    c.limit_reference_displacement_bound hF ht htsmall seed⟩

end PreparedCorrection
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
