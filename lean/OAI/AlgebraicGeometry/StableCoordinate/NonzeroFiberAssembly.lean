import OAI.AlgebraicGeometry.StableCoordinate.NonzeroFiberTransport
import OAI.AlgebraicGeometry.StableCoordinate.Presentation

namespace OAI

/-!
# Nonzero fibers of the four-variable polynomial

The matrix presentation identifies its distinguished element with exactly
`StableCoordinate.f`.  Composing that presentation with the nonzero-fiber calculation gives an
affine coordinate-algebra isomorphism for every nonzero complex parameter.
-/

noncomputable section

namespace StableCoordinate

/-- Every nonzero complex fiber of the exact polynomial has affine-three-space
coordinate algebra. The zero fiber is treated in `ZeroFiberExact`. -/
def exactNonzeroFiberEquiv (l : ℂ) (hl : l≠0) : FiberRing l ≃ₐ[ℂ] R 3 :=
  NonzeroFiber.transportedFiberEquiv Presentation.originalPresentation f
    Presentation.originalPresentation_p l hl

theorem isAffineThreeSpaceFiber_of_ne_zero (l : ℂ) (hl : l≠0) :
    IsAffineThreeSpaceFiber l :=
  ⟨exactNonzeroFiberEquiv l hl⟩

end StableCoordinate

end

end OAI
