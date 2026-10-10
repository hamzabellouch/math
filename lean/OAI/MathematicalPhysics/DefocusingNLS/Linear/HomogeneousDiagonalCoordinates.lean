import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.DiagonalRealCoordinates
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousRealCoordinateEvolution

namespace OAI

/-! # Diagonal real coordinates of the actual whole-space evolution -/

open Set
open scoped NNReal

namespace DefocusingNLS

attribute [local irreducible] diagonalRealCoordinates homogeneousStableCoordinates
  homogeneousLinearizedStep homogeneousComplexLinearizedStep

theorem homogeneousDiagonalCoordinates_inverse (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ) (q : HomogeneousY a k)
    (P : (HomogeneousY a k × HomogeneousY a k) →L[ℂ] (HomogeneousY a k × HomogeneousY a k))
    [FiniteDimensional ℂ P.range]
    (hcomm : ∀ t, Commute (homogeneousComplexLinearizedStep a b k ha ha1 hk m q t) P)
    (G : P.range →L[ℂ] P.range)
    (hG : ∀ t, projectionSemigroupRestriction
      (homogeneousComplexLinearizedStep a b k ha ha1 hk m q) P hcomm t =
        NormedSpace.exp ((t : ℝ) • G))
    (hspan : (⨆ lam : ℂ, Module.End.eigenspace G.toLinearMap lam) = ⊤)
    (hspec : ∀ (lam : ℂ) (v : P.range), v ≠ 0 → G v = lam • v →
      lam = 0 ∨ lam = 1 ∨ lam = 1 / 2) (T : ℝ≥0) :
    HasContractingCoordinateInverse
      (diagonalRealCoordinates (homogeneousStableCoordinates a k ha ha1 hk P) G hspan hspec)
      (homogeneousLinearizedStep a b k ha ha1 hk m q T) := by
  have hπ (u : HomogeneousY a k) :
      homogeneousStableCoordinates a k ha ha1 hk P
        (homogeneousLinearizedStep a b k ha ha1 hk m q T u) =
      NormedSpace.exp ((T : ℝ) • G) (homogeneousStableCoordinates a k ha ha1 hk P u) := by
    exact (homogeneousStableCoordinates_step a b k ha ha1 hk m q P hcomm T u).trans
      (congrArg (fun A : P.range →L[ℂ] P.range =>
        A (homogeneousStableCoordinates a k ha ha1 hk P u)) (hG T))
  exact diagonalRealCoordinates_has_inverse
    (homogeneousStableCoordinates a k ha ha1 hk P) G hspan hspec
    (homogeneousLinearizedStep a b k ha ha1 hk m q T) T T.2 hπ

end DefocusingNLS

end OAI
