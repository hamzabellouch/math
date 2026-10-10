import OAI.Probability.InvariantIsing.Cavity.CavityQuadraticAlgebra

namespace OAI

/-! The matrix covariance identities of `cav:q-innovations`.  These
identities apply also to zero covariance increments. -/

noncomputable section
open scoped Matrix

namespace InvariantIsing

/-- Rescaling a tilted-step covariance by `J_i` gives the innovation
covariance with the previous inverse on the left. -/
theorem cavity_rescaled_step_covariance {d : ℕ}
    (K P C S : Matrix (Fin d) (Fin d) ℝ)
    (hP : IsUnit (1 - P * K).det) (hC : IsUnit (1 - C * K).det) :
    (1 - C * K)⁻¹ * (cavityStepTransition K P C * S) *
        ((1 - C * K)⁻¹).transpose =
      (1 - P * K)⁻¹ * S * ((1 - C * K)⁻¹).transpose := by
  rw [← mul_assoc, cavity_quadratic_backward_inverse K P C hP hC]

/-- The covariance increment transforms by the resolvent difference.
This multiplication form does not require a nonzero cascade exponent. -/
theorem cavity_innovation_covariance_mul {d : ℕ}
    (K P C S : Matrix (Fin d) (Fin d) ℝ) (ζ : ℝ)
    (hK : K.transpose = K) (hC : C.transpose = C)
    (hPdet : IsUnit (1 - P * K).det) (hCdet : IsUnit (1 - C * K).det)
    (hΔ : P - C = ζ • S) :
    ζ • ((1 - P * K)⁻¹ * S * ((1 - C * K)⁻¹).transpose) =
      cavityResolvent K P - cavityResolvent K C := by
  rw [cavityResolvent_difference_symmetric K P C hK hC hPdet hCdet, hΔ]
  simp only [Matrix.mul_smul, Matrix.smul_mul]

/-- The positive-level covariance formula in `cav:q-innovations`. -/
theorem cavity_innovation_covariance {d : ℕ}
    (K P C S : Matrix (Fin d) (Fin d) ℝ) (ζ : ℝ) (hζ : ζ ≠ 0)
    (hK : K.transpose = K) (hC : C.transpose = C)
    (hPdet : IsUnit (1 - P * K).det) (hCdet : IsUnit (1 - C * K).det)
    (hΔ : P - C = ζ • S) :
    (1 - C * K)⁻¹ * (cavityStepTransition K P C * S) *
        ((1 - C * K)⁻¹).transpose =
      ζ⁻¹ • (cavityResolvent K P - cavityResolvent K C) := by
  rw [cavity_rescaled_step_covariance K P C S hPdet hCdet,
    ← cavity_innovation_covariance_mul K P C S ζ hK hC hPdet hCdet hΔ,
    smul_smul, inv_mul_cancel₀ hζ, one_smul]

end InvariantIsing

end

end OAI
