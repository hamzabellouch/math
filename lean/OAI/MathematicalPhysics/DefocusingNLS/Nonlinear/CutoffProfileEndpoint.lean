import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffStableTransfer
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingProfileOperator

namespace OAI

/-! # Endpoint operators for the actual sampled cutoff profile -/

open scoped SchwartzMap ContDiff NNReal

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}

noncomputable def cutoffProfileEndpoint (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (m : ℕ) (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Qp : E → ℂ) (hQp : ContDiff ℝ ∞ Qp) (Q : ℝ) (hQ : 0 ≤ Q)
    (hqb : ∀ L : Radius, ‖cutoffProfileCoefficient a k ha1 hk χ hχ Qp hQp L‖ ≤ Q)
    (T : ℝ≥0) (L : Radius) : FourierL2 →L[ℝ] FourierL2 :=
  expandingProfileEndpoint a b k L.1 T ha ha1 hk L.2 T.2 m Q hQ
    (sampledCutoffProfilePath a k L.1 T ha ha1 hk L.2 χ hχ Qp hQp)
    (fun t => hqb (expandingRadiusCurve L.1 T L.2 t))

@[simp] theorem cutoffProfileEndpoint_apply (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (m : ℕ) (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Qp : E → ℂ) (hQp : ContDiff ℝ ∞ Qp) (Q : ℝ) (hQ : 0 ≤ Q)
    (hqb : ∀ L : Radius, ‖cutoffProfileCoefficient a k ha1 hk χ hχ Qp hQp L‖ ≤ Q)
    (T : ℝ≥0) (L : Radius) (f : FourierL2) :
    cutoffProfileEndpoint a b k ha ha1 hk m χ hχ Qp hQp Q hQ hqb T L f =
      expandingProfileTrajectory a b k L.1 T ha ha1 hk L.2 T.2 m Q hQ
        (sampledCutoffProfilePath a k L.1 T ha ha1 hk L.2 χ hχ Qp hQp)
        (fun t => hqb (expandingRadiusCurve L.1 T L.2 t)) f ⟨T, T.2, le_rfl⟩ := rfl

theorem cutoffProfileEndpoint_uniform_bound (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (m : ℕ) (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Qp : E → ℂ) (hQp : ContDiff ℝ ∞ Qp) (Q : ℝ) (hQ : 0 ≤ Q)
    (hqb : ∀ L : Radius, ‖cutoffProfileCoefficient a k ha1 hk χ hχ Qp hQp L‖ ≤ Q)
    (T : ℝ≥0) : ∃ C : ℝ, 0 ≤ C ∧ ∀ L : Radius,
      ‖cutoffProfileEndpoint a b k ha ha1 hk m χ hχ Qp hQp Q hQ hqb T L‖ ≤ C := by
  obtain ⟨K, hK, hb⟩ := exists_expandingProfileTrajectory_bound a b k ha ha1 hk m Q hQ
  refine ⟨(K + 1) * Real.exp ((K + 1) * T), by positivity, ?_⟩
  intro L
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  rw [cutoffProfileEndpoint_apply]
  exact ((expandingProfileTrajectory a b k L.1 T ha ha1 hk L.2 T.2 m Q hQ
    (sampledCutoffProfilePath a k L.1 T ha ha1 hk L.2 χ hχ Qp hQp)
    (fun t => hqb (expandingRadiusCurve L.1 T L.2 t)) f).norm_coe_le_norm ⟨T, T.2, le_rfl⟩).trans
      (hb L.1 T L.2 T.2 _ _ f)

end DefocusingNLS

end OAI
