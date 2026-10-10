import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.ContinuousCutoffStableOrbit
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ContinuousDiagonalLinearStep
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.FiniteCoordinateComplete

namespace OAI

/-! # Continuous finite symmetry coordinates select global stable cutoff orbits -/

open scoped SchwartzMap ContDiff NNReal

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}

attribute [local irreducible] diagonalRealCoordinates

def HasContinuousFiniteDiagonalCutoffStableOrbits {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (a b k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Qp : E → ℂ) (hQp : ContDiff ℝ ∞ Qp) (π : HomogeneousY a k →L[ℝ] V) : Prop :=
  ∃ G : V →L[ℂ] V,
    ∃ hspan : (⨆ lam : ℂ, Module.End.eigenspace G.toLinearMap lam) = ⊤,
    ∃ hspec : ∀ (lam : ℂ) (v : V), v ≠ 0 → G v = lam • v →
      lam = 0 ∨ lam = 1 ∨ lam = 1 / 2,
    HasContinuousCutoffStableOrbits (F := (diagonalRealCoordinates π G hspan hspec).range)
      a b k ha ha1 hk m χ hχ Qp hQp

theorem continuousCutoffStableOrbits_of_linear_steps {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (a b k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Qp : E → ℂ) (hQp : ContDiff ℝ ∞ Qp) (Q : ℝ) (hQ : 0 ≤ Q)
    (hqb : ∀ L : Radius, ‖cutoffProfileCoefficient a k ha1 hk χ hχ Qp hQp L‖ ≤ Q)
    (π : HomogeneousY a k →L[ℝ] V)
    (hlinear : HasContinuousFiniteDiagonalTorusLinearSteps π
      (cutoffProfileEndpoint a b k ha ha1 hk m χ hχ Qp hQp Q hQ hqb))
    (hnonlinear : ∀ T : ℝ≥0, HasContinuousCutoffNonlinearSteps a b k ha ha1 hk m χ hχ Qp hQp Q hQ hqb T) :
    HasContinuousFiniteDiagonalCutoffStableOrbits a b k ha ha1 hk m χ hχ Qp hQp π := by
  obtain ⟨G, hspan, hspec, T₀, _, hT₀⟩ := hlinear
  let : FiniteDimensional ℝ (SymmetryCoordinates G) :=
    FiniteDimensional.trans ℝ ℂ (SymmetryCoordinates G)
  let F := (diagonalRealCoordinates π G hspan hspec).range
  let : CompleteSpace F := finiteCoordinate_complete (diagonalRealCoordinates π G hspan hspec)
  obtain ⟨M₀, hM₀, hM⟩ := exists_cutoffStep_geometric_ratio a ha
  let T : ℝ≥0 := ⟨max T₀ M₀, hM₀.le.trans (le_max_right _ _)⟩
  have hT : 0 < (T : ℝ) := hM₀.trans_le (le_max_right _ _)
  have hr : 2 * Real.exp (-(2 + a) * T / 2) ≤ 1 :=
    (hM T (le_max_right _ _)).trans (by norm_num)
  refine ⟨G, hspan, hspec, ?_⟩
  exact exists_continuous_cutoffStable_orbits (F := F) a b k ha ha1 hk m χ hχ Qp hQp Q hQ hqb T hT hr
    (hT₀ T (le_max_left _ _)) (hnonlinear T)

end DefocusingNLS

end OAI
