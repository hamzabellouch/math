import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ContinuousCoordinateStableOrbit
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.ContinuousTorusCoordinateTransfer
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.FiniteCoordinateComplete

namespace OAI

/-! # Global stable orbits in the retained diagonal coordinates -/

open scoped SchwartzMap ContDiff NNReal

namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

def HasContinuousDiagonalCoordinateOrbits
    (a b k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Qp : E → ℂ) (hQp : ContDiff ℝ ∞ Qp)
    (π : HomogeneousY a k →L[ℝ] V) (G : V →L[ℂ] V)
    (hspan : (⨆ lam : ℂ, Module.End.eigenspace G.toLinearMap lam) = ⊤)
    (hspec : ∀ (lam : ℂ) (v : V), v ≠ 0 → G v = lam • v →
      lam = 0 ∨ lam = 1 ∨ lam = 1 / 2) : Prop :=
  HasContinuousCoordinateStableOrbits
    (F := (diagonalRealCoordinates π G hspan hspec).range)
    a b k ha ha1 hk m χ hχ Qp hQp
    (expandingCoordinates a k ha ha1 hk χ (diagonalRealCoordinates π G hspan hspec).rangeRestrict)

attribute [local irreducible] HasContinuousCoordinateStableOrbits HasContinuousTorusCoordinateData

theorem continuousDiagonalCoordinateOrbits_of_linear
    (a b k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Qp : E → ℂ) (hQp : ContDiff ℝ ∞ Qp) (Q : ℝ) (hQ : 0 ≤ Q)
    (hqb : ∀ L : Radius, ‖cutoffProfileCoefficient a k ha1 hk χ hχ Qp hQp L‖ ≤ Q)
    (π : HomogeneousY a k →L[ℝ] V) (G : V →L[ℂ] V)
    (hspan : (⨆ lam : ℂ, Module.End.eigenspace G.toLinearMap lam) = ⊤)
    (hspec : ∀ (lam : ℂ) (v : V), v ≠ 0 → G v = lam • v →
      lam = 0 ∨ lam = 1 ∨ lam = 1 / 2)
    (hlinear : HasContinuousDiagonalCoordinateData a k ha ha1 hk π G hspan hspec χ
      (cutoffProfileEndpoint a b k ha ha1 hk m χ hχ Qp hQp Q hQ hqb))
    (hnonlinear : ∀ T : ℝ≥0, HasContinuousCutoffNonlinearSteps a b k ha ha1 hk m χ hχ Qp hQp Q hQ hqb T) :
    HasContinuousDiagonalCoordinateOrbits a b k ha ha1 hk m χ hχ Qp hQp π G hspan hspec := by
  obtain ⟨T₀, _, hT₀⟩ := hlinear
  let c := diagonalRealCoordinates π G hspan hspec
  let : FiniteDimensional ℝ (SymmetryCoordinates G) :=
    FiniteDimensional.trans ℝ ℂ (SymmetryCoordinates G)
  let : CompleteSpace c.range := finiteCoordinate_complete c
  obtain ⟨M₀, hM₀, hM⟩ := exists_cutoffStep_geometric_ratio a ha
  let T : ℝ≥0 := ⟨max T₀ M₀, hM₀.le.trans (le_max_right _ _)⟩
  have hT : 0 < (T : ℝ) := hM₀.trans_le (le_max_right _ _)
  have hr : 2 * Real.exp (-(2 + a) * T / 2) ≤ 1 :=
    (hM T (le_max_right _ _)).trans (by norm_num)
  have hlin := hT₀ T (le_max_left _ _)
  exact exists_continuous_coordinateStable_orbits a b k ha ha1 hk m χ hχ Qp hQp Q hQ hqb T hT hr
    (expandingCoordinates a k ha ha1 hk χ c.rangeRestrict) hlin (hnonlinear T)

end DefocusingNLS

end OAI
