import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.DiagonalCoordinateStableOrbit
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.PhysicalDiagonalCoordinates

namespace OAI

/-! # The physical modulation frame paired with its actual stable graph -/

open scoped SchwartzMap ContDiff
namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

def HasPhysicalCoordinateStableOrbits
    (a b k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Qp : E → ℂ) (hQp : ContDiff ℝ ∞ Qp)
    (π : HomogeneousY a k →L[ℝ] V) : Prop :=
  ∃ G : V →L[ℂ] V,
    ∃ hspan : (⨆ lam : ℂ, Module.End.eigenspace G.toLinearMap lam) = ⊤,
    ∃ hspec : ∀ (lam : ℂ) (v : V), v ≠ 0 → G v = lam • v →
      lam = 0 ∨ lam = 1 ∨ lam = 1 / 2,
    ∃ F : ProfileSymmetryParameters →L[ℝ] HomogeneousY a k,
      Function.Injective F ∧
      (∀ p y, homogeneousPhysicalCLM a k ha ha1 hk (F p) y =
        (p.1 : ℂ) * (Complex.I * Qp y) +
        (p.2.2 : ℂ) * (((a : ℂ) - Complex.I * (b : ℂ)) * Qp y +
          cartesianTransport Qp y) + cartesianDerivative p.2.1 Qp y) ∧
      HasPhysicalDiagonalFrame π G hspan hspec F ∧
      HasContinuousDiagonalCoordinateOrbits a b k ha ha1 hk m χ hχ Qp hQp π G hspan hspec

end DefocusingNLS

end OAI
