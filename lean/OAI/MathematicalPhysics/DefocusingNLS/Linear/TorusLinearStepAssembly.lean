import OAI.MathematicalPhysics.DefocusingNLS.Linear.TorusLinearStep
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffCoordinateInverse
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.DiagonalRealCoordinates

namespace OAI

/-! # Combining actual stable decay and finite coordinate transfer -/

open scoped SchwartzMap NNReal

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}

def HasEventualTorusLinearSteps {H F : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (π : H →L[ℝ] F) (A : ℝ≥0 → Radius → FourierL2 →L[ℝ] FourierL2) : Prop :=
  ∃ T₀ : ℝ, 0 ≤ T₀ ∧ ∀ T : ℝ≥0, T₀ ≤ T → HasTorusLinearStep (F := π.range) T (A T)

def HasFiniteDiagonalTorusLinearSteps {H V : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (π : H →L[ℝ] V) (A : ℝ≥0 → Radius → FourierL2 →L[ℝ] FourierL2) : Prop :=
  ∃ G : V →L[ℂ] V,
    ∃ hspan : (⨆ lam : ℂ, Module.End.eigenspace G.toLinearMap lam) = ⊤,
    ∃ hspec : ∀ (lam : ℂ) (v : V), v ≠ 0 → G v = lam • v →
      lam = 0 ∨ lam = 1 ∨ lam = 1 / 2,
    HasEventualTorusLinearSteps (diagonalRealCoordinates π G hspan hspec) A

theorem torusLinearStep_of_stable_transfer {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (χ : 𝓢(E, ℂ))
    (π : HomogeneousY a k →L[ℝ] F)
    (A : ℝ≥0 → Radius → FourierL2 →L[ℝ] FourierL2)
    (hstable : HasTorusStableBlocks a k ha ha1 hk χ π A)
    (hcoord : ∀ T, HasContractingTorusCoordinateTransfer a k ha ha1 hk χ π T (A T))
    (hA : ∀ T, ∃ C : ℝ, 0 ≤ C ∧ ∀ L, ‖A T L‖ ≤ C) :
    HasEventualTorusLinearSteps π A := by
  obtain ⟨C, hC, Lf, ζ, hζ, hs⟩ := hstable
  obtain ⟨T₀, hT₀, hT⟩ := hs (1 / 8) (by norm_num)
  refine ⟨T₀, hT₀, ?_⟩
  intro T hTT
  obtain ⟨L₀, hLf, hL₀⟩ := hT T hTT
  obtain ⟨D, R, hDR, hR, hdefect⟩ := hcoord T
  obtain ⟨CA, hCA, hAb⟩ := hA T
  obtain ⟨CJ, hCJ, hJ⟩ := exists_homogeneousLocalization_bound a k ha ha1 hk χ
  let Cπ := ‖π.rangeRestrict‖ * CJ
  have hCπ : 0 ≤ Cπ := mul_nonneg (norm_nonneg π.rangeRestrict) hCJ
  apply torusLinearStep_of_frames T (A T) ζ
    (expandingCoordinates a k ha ha1 hk χ π.rangeRestrict) D R hDR hR
    L₀ C Cπ CA hC.le hCπ hCA
  · intro L hL
    obtain ⟨he, hz, hp⟩ := hζ L (hLf.trans hL)
    refine ⟨fun v => congrArg (fun B : π.range →L[ℝ] π.range => B v) he, hz, ?_, hp⟩
    exact expandingCoordinates_norm_le a k CJ ha ha1 hk hCJ χ π.rangeRestrict hJ L
  · exact hL₀
  · exact hAb
  · exact hdefect

theorem finiteDiagonalTorusLinearSteps_of_transfer {V : Type*}
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
    HasFiniteDiagonalTorusLinearSteps π A := by
  let : FiniteDimensional ℝ (SymmetryCoordinates G) :=
    FiniteDimensional.trans ℝ ℂ (SymmetryCoordinates G)
  refine ⟨G, hspan, hspec, ?_⟩
  apply torusLinearStep_of_stable_transfer a k ha ha1 hk χ
    (diagonalRealCoordinates π G hspan hspec) A
  · apply hasTorusStableBlocks_of_kernel_decay a k ha ha1 hk χ ρ hρ hχ
    intro β hβ
    obtain ⟨T₀, hT₀, hT⟩ := hkernel β hβ
    refine ⟨T₀, hT₀, fun T hTT => ?_⟩
    obtain ⟨L₀, hL₀⟩ := hT T hTT
    refine ⟨L₀, fun L hL f hf hz => ?_⟩
    exact hL₀ L hL f hf ((diagonalRealCoordinates_zero_iff π G hspan hspec _).mp hz)
  · exact hcoord
  · exact hA

end DefocusingNLS

end OAI
