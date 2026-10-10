import OAI.MeasureTheory.Falconer.Angular.PublishedGnomonic
import OAI.MeasureTheory.Falconer.Fourier.CoordinateIntegral

namespace OAI

/-!
# One-coordinate formula for the actual sphere integral

The sole measure input is the published gnomonic density identity. The
remaining coordinate split is an ordinary volume-preserving equivalence.
-/

namespace Falconer
open Set MeasureTheory

theorem gnomonic_sphere_iterated_integral (hpublished : PublishedGnomonicSurface)
    {n : ℕ} (hn : 1 ≤ n) (f : Sphere (n+2) → ℂ) (hf : Measurable f)
    (hfi : Integrable f (sphereMeasure (n+2)))
    (hs : ∀ w, w ∉ northHemisphere (n+1) → f w = 0) :
    (∫ w, f w ∂sphereMeasure (n+2)) =
      ∫ y : Space n, ∫ u : ℝ,
        gnomonicDensity (coordinateJoin y u) • f (gnomonicChart (coordinateJoin y u)) := by
  rw [gnomonic_sphere_integral hpublished (by omega) f hf hs]
  exact coordinate_iterated_integral _ (gnomonic_integrable hpublished (by omega) hfi)

end Falconer

end OAI
