import OAI.AlgebraicGeometry.StableCoordinate.ZeroFiberSpecialization
import OAI.AlgebraicGeometry.StableCoordinate.Definitions

namespace OAI

/-!
# Transporting the zero-fiber calculation through a polynomial presentation

The hypothesis of the helper below is a *proved algebra equivalence* to be
supplied by the matrix-change construction.  It does not assert or assume any
of the requested headline claims.
-/

noncomputable section
namespace StableCoordinate.ZeroFiber
open MvPolynomial

/-- Transport the already calculated zero fiber through a polynomial
presentation that takes the distinguished parameter to the exact polynomial.
This helper is instantiated by the explicit presentation construction. -/
def zeroFiberEquivOfPresentation
    (e : Hypersurface ℂ ≃ₐ[ℂ] R 4)
    (he : e (hypersurfaceMk ℂ (X 0)) = f) : FiberRing 0 ≃ₐ[ℂ] R 3 :=
  (Ideal.quotientEquivAlg (parameterIdeal ℂ) (fiberIdeal 0) e (by
    rw [parameterIdeal, Ideal.map_span, Set.image_singleton]
    change Ideal.span ({f - C (0 : ℂ)} : Set (R 4)) =
      Ideal.span ({e (hypersurfaceMk ℂ (X 0))} : Set (R 4))
    rw [he, map_zero, sub_zero])).symm.trans (sourceZeroFiberEquiv ℂ)

end StableCoordinate.ZeroFiber

end

end OAI
