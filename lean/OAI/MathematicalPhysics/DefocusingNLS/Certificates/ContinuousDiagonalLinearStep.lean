import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.ContinuousTorusAssembly
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.DiagonalRealCoordinates

namespace OAI

/-! # Continuous normalized linear data in the real diagonal symmetry coordinates -/

open scoped SchwartzMap NNReal

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}

def HasContinuousFiniteDiagonalTorusLinearSteps {H V : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (π : H →L[ℝ] V) (A : ℝ≥0 → Radius → FourierL2 →L[ℝ] FourierL2) : Prop :=
  ∃ G : V →L[ℂ] V,
    ∃ hspan : (⨆ lam : ℂ, Module.End.eigenspace G.toLinearMap lam) = ⊤,
    ∃ hspec : ∀ (lam : ℂ) (v : V), v ≠ 0 → G v = lam • v →
      lam = 0 ∨ lam = 1 ∨ lam = 1 / 2,
    ∃ T₀ : ℝ, 0 ≤ T₀ ∧ ∀ T : ℝ≥0, T₀ ≤ T →
      HasContinuousTorusLinearStep (F := (diagonalRealCoordinates π G hspan hspec).range) T (A T)

theorem continuous_finiteDiagonalTorusLinearSteps_of_transfer {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (a k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (χ : 𝓢(E, ℂ))
    (ρ : ℝ) (hρ : 0 < ρ) (hχ : ∀ y : E, ‖y‖ ≤ ρ → χ y = 1)
    (π : HomogeneousY a k →L[ℝ] V) (G : V →L[ℂ] V)
    (hspan : (⨆ lam : ℂ, Module.End.eigenspace G.toLinearMap lam) = ⊤)
    (hspec : ∀ (lam : ℂ) (v : V), v ≠ 0 → G v = lam • v →
      lam = 0 ∨ lam = 1 ∨ lam = 1 / 2)
    (A : ℝ≥0 → Radius → FourierL2 →L[ℝ] FourierL2)
    (hkernel : ∀ β : ℝ, 0 < β → ∃ T₀ : ℝ, 0 ≤ T₀ ∧
      ∀ T : ℝ≥0, T₀ ≤ T → ∃ L₀ : ℝ, ∀ L : Radius, L₀ ≤ L.1 →
        ∀ f : FourierL2, ‖f‖ ≤ 1 →
          π (homogeneousLocalizationCLM a k L.1 ha ha1 hk L.2 χ f) = 0 → ‖A T L f‖ < β)
    (hcoord : ∀ T, HasContractingTorusCoordinateTransfer a k ha ha1 hk χ
      (diagonalRealCoordinates π G hspan hspec) T (A T))
    (hA : ∀ T, ∃ C : ℝ, 0 ≤ C ∧ ∀ L, ‖A T L‖ ≤ C) :
    HasContinuousFiniteDiagonalTorusLinearSteps π A := by
  let : FiniteDimensional ℝ (SymmetryCoordinates G) :=
    FiniteDimensional.trans ℝ ℂ (SymmetryCoordinates G)
  refine ⟨G, hspan, hspec, ?_⟩
  apply continuous_torusLinearSteps_of_transfer a k ha ha1 hk χ ρ hρ hχ
    (diagonalRealCoordinates π G hspan hspec) A
  · intro β hβ
    obtain ⟨T₀, hT₀, hT⟩ := hkernel β hβ
    refine ⟨T₀, hT₀, fun T hTT => ?_⟩
    obtain ⟨L₀, hL₀⟩ := hT T hTT
    refine ⟨L₀, fun L hL f hf hz => ?_⟩
    exact hL₀ L hL f hf ((diagonalRealCoordinates_zero_iff π G hspan hspec _).mp hz)
  · exact hcoord
  · exact hA

end DefocusingNLS

end OAI
