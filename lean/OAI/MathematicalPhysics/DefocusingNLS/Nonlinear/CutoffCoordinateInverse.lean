import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.FiniteInvariantInverse
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffCoordinateOperator
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffProfileEndpoint
import OAI.MathematicalPhysics.DefocusingNLS.Linear.TorusStableBlocks

namespace OAI

/-! # The finite inverse and the actual torus coordinate defect -/

open scoped SchwartzMap ContDiff NNReal

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}

def HasContractingTorusCoordinateTransfer {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (χ : 𝓢(E, ℂ))
    (π : HomogeneousY a k →L[ℝ] F)
    (T : ℝ≥0) (A : Radius → FourierL2 →L[ℝ] FourierL2) : Prop :=
  ∃ D R : π.range →L[ℝ] π.range, (∀ v, D (R v) = v) ∧ ‖R‖ ≤ 1 ∧
    ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℝ, ∀ L : Radius, L₀ ≤ L.1 →
      ‖(expandingCoordinates a k ha ha1 hk χ π.rangeRestrict
          (torusEndpointRadius T L)).comp (A L) -
        D.comp (expandingCoordinates a k ha ha1 hk χ π.rangeRestrict L)‖ ≤ ε

theorem cutoffProfile_coordinate_transfer_of_inverse {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (a b k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 10 < k) (m : ℕ)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (hχzero : ∀ y : E, 1 ≤ ‖y‖ → χ y = 0)
    (hχone : ∀ y : E, ‖y‖ ≤ 1 / 2 → χ y = 1)
    (Qp : E → ℂ) (hQp : ContDiff ℝ ∞ Qp) (q : HomogeneousY a k)
    (hq : ∀ y, homogeneousPhysicalCLM a k ha ha1 (by linarith) q y = Qp y)
    (Q : ℝ) (hQ : 0 ≤ Q)
    (hqb : ∀ L : Radius,
      ‖cutoffProfileCoefficient a k ha1 (by linarith) χ hχ Qp hQp L‖ ≤ Q)
    (π : HomogeneousY a k →L[ℝ] F) (T : ℝ≥0)
    (hI : HasContractingCoordinateInverse π
      (homogeneousLinearizedStep a b k ha ha1 (by linarith) m q T)) :
    HasContractingTorusCoordinateTransfer a k ha ha1 (by linarith) χ π T
      (cutoffProfileEndpoint a b k ha ha1 (by linarith) m χ hχ Qp hQp Q hQ hqb T) := by
  obtain ⟨D, R, hDR, hR, hD⟩ := hI
  refine ⟨D, R, hDR, hR, ?_⟩
  have hk8 : 8 < k := by linarith
  obtain ⟨C₀, hC₀, hCb⟩ := exists_homogeneousLocalization_bound a k ha ha1 hk8 χ
  apply sampledCutoffProfile_coordinate_operator_norm a b k T Q C₀ ha ha1 hk T.2 hQ hC₀
    m χ hχ hχzero hχone Qp hQp q hq hqb hCb π.rangeRestrict D
  intro u
  have h := hD u
  rwa [homogeneousLinearizedStep_eq_slab a b k ha ha1 hk8 m q T T.2 T le_rfl] at h

end DefocusingNLS

end OAI
