import OAI.Probability.InvariantIsing.Cavity.CavityTiltTransport
import OAI.Probability.InvariantIsing.Cavity.CavityGaussianAffineImage
import OAI.Probability.InvariantIsing.Cavity.CavityTiltCovariance

namespace OAI

/-! The complete conditional Gaussian kernel in `cav:q-kernels`,
including degenerate covariance matrices. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

theorem cavity_gaussian_quadratic_tilt_law {d : ℕ}
    (K S : Matrix (Fin d) (Fin d) ℝ) (hK : K.IsHermitian) (hS : S.PosSemidef)
    (hQ : (cavityFactorPrecision K (CFC.sqrt S)).PosDef)
    (u : EuclideanSpace ℝ (Fin d)) :
    (multivariateGaussian u S).tilted
      (fun y => ⟪y, Matrix.toEuclideanCLM (𝕜 := ℝ) K y⟫ / 2) =
      multivariateGaussian
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - S * K)⁻¹ u)
        (cavityResolvent K S) := by
  let B := CFC.sqrt S
  let Q := cavityFactorPrecision K B
  let l := cavityFactorLinear K B u
  let F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
    fun z => u + Matrix.toEuclideanCLM (𝕜 := ℝ) B z
  let f : EuclideanSpace ℝ (Fin d) → ℝ :=
    fun y => ⟪y, Matrix.toEuclideanCLM (𝕜 := ℝ) K y⟫ / 2
  have hB : B * B.transpose = S := cavity_covariance_sqrt_factor S hS
  have hQdet : IsUnit Q.det := isUnit_iff_ne_zero.mpr hQ.det_pos.ne'
  have hf : f ∘ F = fun z => cavityPrecisionPotential Q l z +
      ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) K u⟫ / 2 := by
    funext z
    exact cavity_factor_exponent K B hK u z
  have hbase : multivariateGaussian u S =
      (stdGaussian (EuclideanSpace ℝ (Fin d))).map F := rfl
  have hmean : u + Matrix.toEuclideanCLM (𝕜 := ℝ) B
      (Matrix.toEuclideanCLM (𝕜 := ℝ) Q⁻¹ l) =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - S * K)⁻¹ u := by
    have hi := cavity_covariance_inverse K B hQdet
    rw [hB] at hi
    rw [hi]
    simp only [map_add, map_one, map_mul, add_apply, one_apply_eq_self,
      mul_apply_eq_comp, l, cavityFactorLinear, Q]
  have hcov : B * Q⁻¹ * B.transpose = cavityResolvent K S := by
    have hi := cavity_tilt_covariance_factor K B hQdet
    rw [hB] at hi
    exact hi.symm
  change (multivariateGaussian u S).tilted f = _
  rw [hbase, ← cavity_tilt_map _ F (by fun_prop) f (by fun_prop), hf,
    cavity_tilt_add_const _ (cavityPrecisionPotential Q l)
      (cavity_precision_potential_integrable Q hQ l),
    cavity_precision_tilt_law Q hQ l,
    cavity_multivariateGaussian_affine_image B Q⁻¹ hQ.inv.posSemidef _ u,
    hmean, hcov]

end InvariantIsing

end

end OAI
