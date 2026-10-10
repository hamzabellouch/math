import OAI.Geometry.CylinderCovering.Convexity.FinitePlaneHausdorff

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace
theorem CylinderCovering.FinitePlaneHausdorff.compact_perpendicular_measure_ne_top {u : EuclideanSpace ℝ (Fin 3)} (hu : ‖u‖ = 1)
    {S : Set (EuclideanSpace ℝ (Fin 3))} (hS : IsCompact S)
    (hplane : ∀ x ∈ S, inner ℝ u x = 0) :
    Measure.euclideanHausdorffMeasure 2 S ≠ ⊤ := by
  have h := CylinderCovering.FinitePlaneHausdorff.compact_perpendicular_measure_lt_top
    hu hS hplane
  simpa using h.ne

end OAI
