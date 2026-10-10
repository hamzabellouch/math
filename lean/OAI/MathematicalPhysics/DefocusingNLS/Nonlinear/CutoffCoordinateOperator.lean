import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffCoordinateTransfer
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingProfileOperator

namespace OAI

/-! # Operator-norm control of the exact expanding-torus coordinate defect -/

open Set
open scoped SchwartzMap ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem sampledCutoffProfile_coordinate_operator_norm (a b k T Q C₀ : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 10 < k) (hT : 0 ≤ T)
    (hQ : 0 ≤ Q) (hC₀ : 0 ≤ C₀) (m : ℕ)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (hχzero : ∀ y : E, 1 ≤ ‖y‖ → χ y = 0)
    (hχone : ∀ y : E, ‖y‖ ≤ 1 / 2 → χ y = 1)
    (Qp : E → ℂ) (hQp : ContDiff ℝ ∞ Qp) (Q₀ : HomogeneousY a k)
    (hQ₀ : ∀ y, homogeneousPhysicalCLM a k ha ha1 (by linarith) Q₀ y = Qp y)
    (hqb : ∀ L : Radius, ‖cutoffProfileCoefficient a k ha1 (by linarith) χ hχ Qp hQp L‖ ≤ Q)
    (hCb : ∀ (L : ℝ) (hL : 1 ≤ L) (f : FourierL2),
      ‖homogeneousLocalizationCLM a k L ha ha1 (by linarith) hL χ f‖ ≤ C₀ * ‖f‖)
    (π : HomogeneousY a k →L[ℝ] F) (A : F →L[ℝ] F)
    (hA : ∀ u, π (homogeneousLinearizedTrajectory a b k T ha ha1 (by linarith) hT m Q₀ u
      ⟨T, hT, le_rfl⟩) = A (π u)) :
    ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℝ, ∀ L : Radius, L₀ ≤ L.1 →
      ‖(expandingCoordinates a k ha ha1 (by linarith) χ π
          (expandingRadiusCurve L.1 T L.2 ⟨T, hT, le_rfl⟩)).comp
          (expandingProfileEndpoint a b k L.1 T ha ha1 (by linarith) L.2 hT m Q hQ
            (sampledCutoffProfilePath a k L.1 T ha ha1 (by linarith) L.2 χ hχ Qp hQp)
            (fun t => hqb (expandingRadiusCurve L.1 T L.2 t))) -
        A.comp (expandingCoordinates a k ha ha1 (by linarith) χ π L)‖ ≤ ε := by
  intro ε hε
  obtain ⟨L₀, hL₀⟩ := sampledCutoffProfile_uniform_coordinate_defect a b k T Q C₀
    ha ha1 hk hT hQ hC₀ m χ hχ hχzero hχone Qp hQp Q₀ hQ₀ hqb hCb π A hA ε hε
  refine ⟨L₀, fun L hL => ?_⟩
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hε.le
  intro f hf
  exact (hL₀ L hL f hf.le).le

end DefocusingNLS

end OAI
