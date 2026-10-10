import OAI.Geometry.ProjectionVolume.Basic
import OAI.Geometry.ProjectionVolume.SupportGeometry

namespace OAI

namespace Paper092

theorem projectionBody_eq_of_brightness_eq_support {n : ℕ}
    {K C : Set (Euclidean n)} (hC : IsCompact C) (hne : C.Nonempty)
    (hconv : Convex ℝ C)
    (h : ∀ u, brightness K u = SupportGeometry.support C (innerSL ℝ u)) :
    projectionBody K = C :=
  SupportGeometry.halfSpaces_eq_of_eq_support hC hne hconv (brightness K) h

end Paper092

end OAI
