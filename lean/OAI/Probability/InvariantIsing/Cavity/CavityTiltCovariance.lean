import OAI.Probability.InvariantIsing.Cavity.CavityMultivariateGaussian

namespace OAI

/-! The positive covariance of a quadratic Gaussian tilt. -/

noncomputable section
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_inverse_push_factor {d : ℕ}
    (K B : Matrix (Fin d) (Fin d) ℝ)
    (hQ : IsUnit (cavityFactorPrecision K B).det) :
    (1 - (B * B.transpose) * K)⁻¹ * B = B * (cavityFactorPrecision K B)⁻¹ := by
  have hA : IsUnit (1 - (B * B.transpose) * K).det := by
    rwa [← cavity_factor_det]
  have hf : (1 - (B * B.transpose) * K) * B = B * cavityFactorPrecision K B := by
    unfold cavityFactorPrecision
    noncomm_ring
  have hc : (1 - (B * B.transpose) * K) * (B * (cavityFactorPrecision K B)⁻¹) = B := by
    rw [← mul_assoc, hf, mul_assoc, Matrix.mul_nonsing_inv _ hQ, mul_one]
  calc
    _ = (1 - (B * B.transpose) * K)⁻¹ *
        ((1 - (B * B.transpose) * K) * (B * (cavityFactorPrecision K B)⁻¹)) := by rw [hc]
    _ = _ := Matrix.nonsing_inv_mul_cancel_left _ _ hA

theorem cavity_tilt_covariance_factor {d : ℕ}
    (K B : Matrix (Fin d) (Fin d) ℝ)
    (hQ : IsUnit (cavityFactorPrecision K B).det) :
    cavityResolvent K (B * B.transpose) =
      B * (cavityFactorPrecision K B)⁻¹ * B.transpose := by
  unfold cavityResolvent
  rw [← mul_assoc, cavity_inverse_push_factor K B hQ]

theorem cavity_tilt_covariance_posSemidef {d : ℕ}
    (K S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (hQ : (cavityFactorPrecision K (CFC.sqrt S)).PosDef) :
    (cavityResolvent K S).PosSemidef := by
  rw [← cavity_covariance_sqrt_factor S hS,
    cavity_tilt_covariance_factor K (CFC.sqrt S) (isUnit_iff_ne_zero.mpr hQ.det_pos.ne')]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hQ.inv.posSemidef.mul_mul_conjTranspose_same (CFC.sqrt S)

end InvariantIsing

end

end OAI
