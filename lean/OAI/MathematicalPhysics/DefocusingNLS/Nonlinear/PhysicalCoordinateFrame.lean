import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalFrame
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.DiagonalRealCoordinates

namespace OAI

/-! # A physical frame gives a continuous inverse on its coordinate image -/

namespace DefocusingNLS

variable {H V : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def HasPhysicalCoordinateFrame (c : H →L[ℝ] V)
    (F : ProfileSymmetryParameters →L[ℝ] H) : Prop :=
  ∃ B : ProfileSymmetryParameters ≃L[ℝ] c.range, ∀ p, (B p : V) = c (F p)

theorem physicalCoordinateFrame_of_bijective (c : H →L[ℝ] V)
    (F : ProfileSymmetryParameters →L[ℝ] H)
    (hinj : Function.Injective (c.comp F))
    (hsurj : ∀ u, ∃ p, c (F p) = c u) :
    HasPhysicalCoordinateFrame c F := by
  let B := c.rangeRestrict.comp F
  have hi : Function.Injective B := by
    intro p q h
    exact hinj (congrArg Subtype.val h)
  have hs : Function.Surjective B := by
    rintro ⟨v, u, rfl⟩
    obtain ⟨p, hp⟩ := hsurj u
    exact ⟨p, Subtype.ext hp⟩
  let e : ProfileSymmetryParameters ≃L[ℝ] c.range :=
    (LinearEquiv.ofBijective B.toLinearMap ⟨hi, hs⟩).toContinuousLinearEquiv
  exact ⟨e, fun _ => rfl⟩

section ComplexCoordinates
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

def HasPhysicalDiagonalFrame (π : H →L[ℝ] W) (G : W →L[ℂ] W)
    (hspan : (⨆ lam : ℂ, Module.End.eigenspace G.toLinearMap lam) = ⊤)
    (hspec : ∀ (lam : ℂ) (v : W), v ≠ 0 → G v = lam • v →
      lam = 0 ∨ lam = 1 ∨ lam = 1 / 2)
    (F : ProfileSymmetryParameters →L[ℝ] H) : Prop :=
  HasPhysicalCoordinateFrame (diagonalRealCoordinates π G hspan hspec) F

theorem physicalDiagonalFrame_of_frame (π : H →L[ℝ] W) (G : W →L[ℂ] W)
    (hspan : (⨆ lam : ℂ, Module.End.eigenspace G.toLinearMap lam) = ⊤)
    (hspec : ∀ (lam : ℂ) (v : W), v ≠ 0 → G v = lam • v →
      lam = 0 ∨ lam = 1 ∨ lam = 1 / 2)
    (F : ProfileSymmetryParameters →L[ℝ] H)
    (hinj : Function.Injective (π.comp F))
    (hsurj : ∀ u, ∃ p, π (F p) = π u) :
    HasPhysicalDiagonalFrame π G hspan hspec F := by
  apply physicalCoordinateFrame_of_bijective (diagonalRealCoordinates π G hspan hspec) F
  · intro p q h
    apply hinj
    exact (symmetryCoordinateEquiv G hspan hspec).symm.injective h
  · intro u
    obtain ⟨p, hp⟩ := hsurj u
    exact ⟨p, congrArg (symmetryCoordinateEquiv G hspan hspec).symm hp⟩

end ComplexCoordinates

end DefocusingNLS

end OAI
