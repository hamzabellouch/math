import OAI.Geometry.SurfaceImmersion.Geometry.CovarianceRealOperator
import OAI.Geometry.SurfaceImmersion.Correction.SmoothPeriodicCorrector

namespace OAI

/-! Explicit formulas for the canonical angular correction. -/
noncomputable section
open MeasureTheory

namespace ClosedSurfaceR4.JetPolynomial
open PeriodicCorrector CovarianceCorrector
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The right-hand side of the normal covariance equation. -/
def angularSourceFunction (Y C X₀ : E) (V : C(Period, E))
    (h K e : ℝ → ℝ) (t : ℝ) : ℝ :=
  let a := fun s : ℝ => inner ℝ (X₀ + V (s : Period)) (spanSolve Y C (h s, deriv K s))
  e t - (a t - ∫ s in 0..1, a s)

def angularCorrectionFunction (Y C X₀ : E) (V : C(Period, E)) (q : ℝ)
    (h K e : ℝ → ℝ) (t : ℝ) : E :=
  spanSolve Y C (PeriodicPrimitive.primitive h t, K t) +
    PeriodicPrimitive.primitive (realCorrector V q (angularSourceFunction Y C X₀ V h K e)) t

end ClosedSurfaceR4.JetPolynomial

end

end OAI
