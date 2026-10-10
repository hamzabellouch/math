import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousDiagonalCoordinates
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffCoordinateInverse

namespace OAI

/-! # Actual torus coordinate transfer with a contracting backward map -/

open Set
open scoped SchwartzMap ContDiff NNReal

namespace DefocusingNLS

attribute [local irreducible] diagonalRealCoordinates homogeneousStableCoordinates
  homogeneousLinearizedStep homogeneousComplexLinearizedStep

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}

theorem cutoffProfile_diagonal_coordinate_transfer (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 10 < k) (m : ℕ)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (hχzero : ∀ y : E, 1 ≤ ‖y‖ → χ y = 0)
    (hχone : ∀ y : E, ‖y‖ ≤ 1 / 2 → χ y = 1)
    (Qp : E → ℂ) (hQp : ContDiff ℝ ∞ Qp) (q : HomogeneousY a k)
    (hq : ∀ y, homogeneousPhysicalCLM a k ha ha1 (by linarith) q y = Qp y)
    (Q : ℝ) (hQ : 0 ≤ Q)
    (hqb : ∀ L : Radius,
      ‖cutoffProfileCoefficient a k ha1 (by linarith) χ hχ Qp hQp L‖ ≤ Q)
    (P : (HomogeneousY a k × HomogeneousY a k) →L[ℂ] (HomogeneousY a k × HomogeneousY a k))
    [FiniteDimensional ℂ P.range]
    (hcomm : ∀ t, Commute (homogeneousComplexLinearizedStep a b k ha ha1 (by linarith) m q t) P)
    (G : P.range →L[ℂ] P.range)
    (hG : ∀ t, projectionSemigroupRestriction
      (homogeneousComplexLinearizedStep a b k ha ha1 (by linarith) m q) P hcomm t =
        NormedSpace.exp ((t : ℝ) • G))
    (hspan : (⨆ lam : ℂ, Module.End.eigenspace G.toLinearMap lam) = ⊤)
    (hspec : ∀ (lam : ℂ) (v : P.range), v ≠ 0 → G v = lam • v →
      lam = 0 ∨ lam = 1 ∨ lam = 1 / 2) (T : ℝ≥0) :
    HasContractingTorusCoordinateTransfer a k ha ha1 (by linarith) χ
      (diagonalRealCoordinates (homogeneousStableCoordinates a k ha ha1 (by linarith) P)
        G hspan hspec) T
      (cutoffProfileEndpoint a b k ha ha1 (by linarith) m χ hχ Qp hQp Q hQ hqb T) := by
  let : FiniteDimensional ℝ P.range := FiniteDimensional.trans ℝ ℂ P.range
  let : FiniteDimensional ℝ (SymmetryCoordinates G) :=
    FiniteDimensional.trans ℝ ℂ (SymmetryCoordinates G)
  have hk8 : 8 < k := by linarith
  apply cutoffProfile_coordinate_transfer_of_inverse a b k ha ha1 hk m χ hχ hχzero hχone
    Qp hQp q hq Q hQ hqb _ T
  exact homogeneousDiagonalCoordinates_inverse a b k ha ha1 hk8 m q
    P hcomm G hG hspan hspec T

end DefocusingNLS

end OAI
