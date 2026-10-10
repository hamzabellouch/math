import OAI.Analysis.OperatorAlgebra.IsometricCornerOperators

namespace OAI

/-! Operator norm transfer through an isometric inclusion. -/
noncomputable section
namespace WeakPureInfiniteness

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma isometricCornerLift_norm (V : K →ₗᵢ[ℂ] H) (T : K →L[ℂ] K) :
    ‖isometricCornerLift V T‖ = ‖T‖ :=
  NonUnitalStarAlgHom.norm_map (isometricCornerLiftHom V)
    (isometricCornerLift_injective V) T

lemma eq_isometricCornerLift_of_intertwines (V : K →ₗᵢ[ℂ] H)
    (R : H →L[ℂ] H) (T : K →L[ℂ] K)
    (hR : R * isometricCornerProjection V = R)
    (hT : ∀ x : K, R (V x) = V (T x)) :
    R = isometricCornerLift V T := by
  apply ContinuousLinearMap.ext
  intro x
  calc
    R x = R (isometricCornerProjection V x) :=
      (congrArg (fun A : H →L[ℂ] H => A x) hR).symm
    _ = R (V (V.toContinuousLinearMap.adjoint x)) := rfl
    _ = V (T (V.toContinuousLinearMap.adjoint x)) := hT _
    _ = isometricCornerLift V T x := rfl

lemma norm_eq_of_corner_intertwines (V : K →ₗᵢ[ℂ] H)
    (R : H →L[ℂ] H) (T : K →L[ℂ] K)
    (hR : R * isometricCornerProjection V = R)
    (hT : ∀ x : K, R (V x) = V (T x)) : ‖R‖ = ‖T‖ := by
  rw [eq_isometricCornerLift_of_intertwines V R T hR hT,
    isometricCornerLift_norm]

end WeakPureInfiniteness

end

end OAI
