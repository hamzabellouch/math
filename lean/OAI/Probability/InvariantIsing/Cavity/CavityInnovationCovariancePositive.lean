import OAI.Probability.InvariantIsing.Cavity.CavityQuadraticCovariance
import OAI.Probability.InvariantIsing.Cavity.CavityTiltCovariance

namespace OAI

/-! Positivity of the noncommuting innovation covariance. -/

noncomputable section
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

theorem cavity_innovation_covariance_posSemidef {d : ℕ}
    (K P C S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef) (ζ : ℝ)
    (hPdet : IsUnit (1 - P * K).det) (hCdet : IsUnit (1 - C * K).det)
    (hΔ : P - C = ζ • S)
    (hQ : (cavityFactorPrecision (ζ • cavityBackwardQuadratic K C)
      (CFC.sqrt S)).PosDef) :
    ((1 - P * K)⁻¹ * S * ((1 - C * K)⁻¹).transpose).PosSemidef := by
  have hcov : cavityStepTransition K P C * S =
      cavityResolvent (ζ • cavityBackwardQuadratic K C) S := by
    unfold cavityStepTransition cavityResolvent
    rw [hΔ]
    simp only [Matrix.smul_mul, Matrix.mul_smul]
  rw [← cavity_rescaled_step_covariance K P C S hPdet hCdet, hcov]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (cavity_tilt_covariance_posSemidef (ζ • cavityBackwardQuadratic K C) S hS hQ).mul_mul_conjTranspose_same
      (1 - C * K)⁻¹

end InvariantIsing

end

end OAI
