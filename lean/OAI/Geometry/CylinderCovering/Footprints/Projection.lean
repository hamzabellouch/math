import OAI.Geometry.CylinderCovering.Footprints.ProjectionDefinitions
import OAI.Geometry.CylinderCovering.Radial.SetProjection

namespace OAI

noncomputable section
namespace RadialFootprints
open Set MeasureTheory TriangularCovering
open scoped InnerProductSpace

theorem projectedCoordinateFootprint_area {e w : Space}
    (p₀ a b : Space) (S : Set (ℝ × ℝ)) (he : ‖e‖ = 1)
    (ha : inner ℝ e a = 0) (hb : inner ℝ e b = 0) (hw : inner ℝ e w = 0) :
    area (projectedCoordinateFootprint e w p₀ a b S) =
      (Real.sqrt (inner ℝ a a * inner ℝ b b - (inner ℝ a b)^2) /
        Real.sqrt (1 + ‖w‖^2)) * volume.real S := by
  change area (projection (unit (e + w)) ''
    (RadialProjection.coordinateAffine p₀ a b '' S)) = _
  exact RadialProjection.radial_affine_projection_area p₀ e a b w he ha hb hw S

theorem projectedCoordinateFootprint_isCompact (e w p₀ a b : Space)
    {S : Set (ℝ × ℝ)} (hS : IsCompact S) :
    IsCompact (projectedCoordinateFootprint e w p₀ a b S) :=
  RadialProjection.affine_projection_isCompact p₀ (unit (e + w)) a b hS

theorem projectedCoordinateFootprint_finite {e w : Space}
    (p₀ a b : Space) {S : Set (ℝ × ℝ)} (hS : IsCompact S)
    (he : ‖e‖ = 1) (hw : inner ℝ e w = 0) :
    Measure.euclideanHausdorffMeasure 2
      (projectedCoordinateFootprint e w p₀ a b S) ≠ ⊤ :=
  RadialProjection.affine_projection_finite p₀ (unit (e + w)) a b
    (unit_norm (RadialProjection.sideways_ne_zero he hw)) hS

theorem projectedCoordinateFootprint_perpendicular {e w : Space}
    (p₀ a b : Space) (S : Set (ℝ × ℝ)) (he : ‖e‖ = 1)
    (hw : inner ℝ e w = 0) :
    ∀ z ∈ projectedCoordinateFootprint e w p₀ a b S,
      inner ℝ (unit (e + w)) z = 0 := by
  rintro z ⟨x, hx, rfl⟩
  exact projection_perp (unit_norm (RadialProjection.sideways_ne_zero he hw)) x

end RadialFootprints

end

end OAI
