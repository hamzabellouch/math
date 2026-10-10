import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffDiagonalTransfer
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.ContinuousTorusCoordinateTransfer
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ContinuousDiagonalLinearStep

namespace OAI

/-! # Actual cutoff linear data retaining the diagonal coordinates -/

open scoped SchwartzMap ContDiff NNReal

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}

attribute [local irreducible] homogeneousStableCoordinates diagonalRealCoordinates
  homogeneousComplexLinearizedStep cutoffProfileEndpoint HasContinuousFiniteDiagonalTorusLinearSteps
  HasContinuousTorusCoordinateData HasContinuousDiagonalCoordinateData
  homogeneousLocalizationCLM cutoffProfileCoefficient homogeneousPhysicalCLM

theorem cutoffProfile_continuous_coordinate_steps (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 10 < k) (m : ℕ)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (hχzero : ∀ y : E, 1 ≤ ‖y‖ → χ y = 0)
    (hχone : ∀ y : E, ‖y‖ ≤ 1 / 2 → χ y = 1)
    (Qp : E → ℂ) (hQp : ContDiff ℝ ∞ Qp) (q : HomogeneousY a k)
    (hq : ∀ y, homogeneousPhysicalCLM a k ha ha1 (show (8 : ℝ) < k from lt_trans (by norm_num) hk) q y = Qp y)
    (Q : ℝ) (hQ : 0 ≤ Q)
    (hqb : ∀ L : Radius,
      ‖cutoffProfileCoefficient a k ha1 (show (8 : ℝ) < k from lt_trans (by norm_num) hk) χ hχ Qp hQp L‖ ≤ Q)
    (P : (HomogeneousY a k × HomogeneousY a k) →L[ℂ] (HomogeneousY a k × HomogeneousY a k))
    [FiniteDimensional ℂ P.range]
    (hcomm : ∀ t, Commute (homogeneousComplexLinearizedStep a b k ha ha1 (show (8 : ℝ) < k from lt_trans (by norm_num) hk) m q t) P)
    (G : P.range →L[ℂ] P.range)
    (hG : ∀ t, projectionSemigroupRestriction
      (homogeneousComplexLinearizedStep a b k ha ha1 (show (8 : ℝ) < k from lt_trans (by norm_num) hk) m q) P hcomm t =
        NormedSpace.exp ((t : ℝ) • G))
    (hspan : (⨆ lam : ℂ, Module.End.eigenspace G.toLinearMap lam) = ⊤)
    (hspec : ∀ (lam : ℂ) (v : P.range), v ≠ 0 → G v = lam • v →
      lam = 0 ∨ lam = 1 ∨ lam = 1 / 2)
    (hkernel : ∀ β : ℝ, 0 < β → ∃ T₀ : ℝ, 0 ≤ T₀ ∧
      ∀ T : ℝ≥0, T₀ ≤ T → ∃ L₀ : ℝ, ∀ L : Radius, L₀ ≤ L.1 →
        ∀ f : FourierL2, ‖f‖ ≤ 1 →
          homogeneousStableCoordinates a k ha ha1 (show (8 : ℝ) < k from lt_trans (by norm_num) hk) P
            (homogeneousLocalizationCLM a k L.1 ha ha1 (show (8 : ℝ) < k from lt_trans (by norm_num) hk) L.2 χ f) = 0 →
          ‖cutoffProfileEndpoint a b k ha ha1 (show (8 : ℝ) < k from lt_trans (by norm_num) hk) m χ hχ Qp hQp Q hQ hqb T L f‖ < β) :
    HasContinuousDiagonalCoordinateData a k ha ha1
      (show 8 < k from lt_trans (by norm_num) hk)
      (homogeneousStableCoordinates a k ha ha1 (show 8 < k from lt_trans (by norm_num) hk) P)
      G hspan hspec χ
      (cutoffProfileEndpoint a b k ha ha1 (show 8 < k from lt_trans (by norm_num) hk)
        m χ hχ Qp hQp Q hQ hqb) := by
  have hk8 : 8 < k := by linarith
  apply continuous_diagonalCoordinateData_of_transfer a k ha ha1 hk8 χ (1 / 2)
    (by norm_num) hχone (homogeneousStableCoordinates a k ha ha1 hk8 P)
    G hspan hspec
    (cutoffProfileEndpoint a b k ha ha1 hk8 m χ hχ Qp hQp Q hQ hqb) hkernel
  · exact fun T => cutoffProfile_diagonal_coordinate_transfer a b k ha ha1 hk m χ hχ hχzero hχone
      Qp hQp q hq Q hQ hqb P hcomm G hG hspan hspec T
  · exact fun T => cutoffProfileEndpoint_uniform_bound a b k ha ha1 hk8 m χ hχ Qp hQp Q hQ hqb T

end DefocusingNLS

end OAI
