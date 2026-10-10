import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalCoordinates
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.PhysicalCoordinateFrame
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.DiagonalRealCoordinates

namespace OAI

/-! # The fourteen physical parameters are coordinates on the real diagonal range -/

namespace DefocusingNLS

attribute [local irreducible] diagonalRealCoordinates homogeneousStableCoordinates
  symmetryCoordinateEquiv HasPhysicalCoordinateFrame

theorem physicalDiagonal_coordinate_equiv (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (P : (HomogeneousY a k × HomogeneousY a k) →L[ℂ]
      (HomogeneousY a k × HomogeneousY a k)) [FiniteDimensional ℂ P.range]
    (G : P.range →L[ℂ] P.range)
    (hspan : (⨆ lam : ℂ, Module.End.eigenspace G.toLinearMap lam) = ⊤)
    (hspec : ∀ (lam : ℂ) (v : P.range), v ≠ 0 → G v = lam • v →
      lam = 0 ∨ lam = 1 ∨ lam = 1 / 2)
    (F : ProfileSymmetryParameters →L[ℝ] HomogeneousY a k) (hF : Function.Injective F)
    (hfix : ∀ p, P (homogeneousComplexEmbed a k ha ha1 hk (F p)) =
      homogeneousComplexEmbed a k ha ha1 hk (F p))
    (hrange : ∀ u, ∃ p, P (homogeneousComplexEmbed a k ha ha1 hk u) =
      homogeneousComplexEmbed a k ha ha1 hk (F p)) :
    HasPhysicalDiagonalFrame (homogeneousStableCoordinates a k ha ha1 hk P) G hspan hspec F := by
  apply physicalDiagonalFrame_of_frame (homogeneousStableCoordinates a k ha ha1 hk P) G hspan hspec F
  · intro p r h
    unfold homogeneousStableCoordinates at h
    have he := congrArg (fun v : P.range =>
      homogeneousComplexReal a k ha ha1 hk (v : HomogeneousY a k × HomogeneousY a k)) h
    change homogeneousComplexReal a k ha ha1 hk
        (P (homogeneousComplexEmbed a k ha ha1 hk (F p))) =
      homogeneousComplexReal a k ha ha1 hk
        (P (homogeneousComplexEmbed a k ha ha1 hk (F r))) at he
    rw [hfix, hfix, homogeneousComplexReal_embed, homogeneousComplexReal_embed] at he
    exact hF he
  · intro u
    obtain ⟨p, hp⟩ := hrange u
    refine ⟨p, Subtype.ext ?_⟩
    unfold homogeneousStableCoordinates
    exact (hfix p).trans hp.symm

end DefocusingNLS

end OAI
