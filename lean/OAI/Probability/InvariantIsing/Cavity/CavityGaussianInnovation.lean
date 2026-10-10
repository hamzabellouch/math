import OAI.Probability.InvariantIsing.Cavity.CavityGaussianTiltLaw
import OAI.Probability.InvariantIsing.Cavity.CavityGaussianRecursion
import OAI.Probability.InvariantIsing.Cavity.CavityQuadraticCovariance

namespace OAI

/-! The centered innovation of a retained quadratic Gaussian step. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_shifted_gaussian_quadratic_tilt_law {d : ℕ}
    (K S : Matrix (Fin d) (Fin d) ℝ) (hK : K.IsHermitian) (hS : S.PosSemidef)
    (hQ : (cavityFactorPrecision K (CFC.sqrt S)).PosDef)
    (u : EuclideanSpace ℝ (Fin d)) :
    ((multivariateGaussian 0 S).tilted
      (fun z => ⟪u + z, Matrix.toEuclideanCLM (𝕜 := ℝ) K (u + z)⟫ / 2)).map
        (fun z => u + z) =
      multivariateGaussian (Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - S * K)⁻¹ u)
        (cavityResolvent K S) := by
  have hbase : (multivariateGaussian 0 S).map (fun z => u + z) =
      multivariateGaussian u S := by
    simpa only [map_one, one_apply_eq_self, map_zero, add_zero, one_mul, mul_one,
      Matrix.transpose_one] using
      cavity_multivariateGaussian_affine_image (1 : Matrix (Fin d) (Fin d) ℝ) S hS 0 u
  have ht := cavity_tilt_map (multivariateGaussian 0 S) (fun z => u + z) (by fun_prop)
    (fun y => ⟪y, Matrix.toEuclideanCLM (𝕜 := ℝ) K y⟫ / 2) (by fun_prop)
  change ((multivariateGaussian 0 S).tilted
    ((fun y => ⟪y, Matrix.toEuclideanCLM (𝕜 := ℝ) K y⟫ / 2) ∘ (fun z => u + z))).map
      (fun z => u + z) = _
  rw [ht, hbase]
  exact cavity_gaussian_quadratic_tilt_law K S hK hS hQ u

/-- Under the retained quadratic weight, the rescaled increment has
an ancestor-independent centered Gaussian law. -/
theorem cavity_gaussian_step_innovation_law {d : ℕ}
    (K P C S : Matrix (Fin d) (Fin d) ℝ)
    (hK : K.transpose = K) (hC : C.transpose = C) (hS : S.PosSemidef)
    (ζ : ℝ) (hPdet : IsUnit (1 - P * K).det) (hCdet : IsUnit (1 - C * K).det)
    (hΔ : P - C = ζ • S)
    (hQ : (cavityFactorPrecision (ζ • cavityBackwardQuadratic K C)
      (CFC.sqrt S)).PosDef) (u : EuclideanSpace ℝ (Fin d)) :
    ((multivariateGaussian 0 S).tilted
      (fun z => ζ / 2 * ⟪u + z, Matrix.toEuclideanCLM (𝕜 := ℝ)
        (cavityBackwardQuadratic K C) (u + z)⟫)).map
      (fun z => Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - C * K)⁻¹ (u + z) -
        Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - P * K)⁻¹ u) =
      multivariateGaussian 0
        ((1 - P * K)⁻¹ * S * ((1 - C * K)⁻¹).transpose) := by
  let L := ζ • cavityBackwardQuadratic K C
  let J := (1 - C * K)⁻¹
  let T := cavityStepTransition K P C
  have hL : L.IsHermitian :=
    (Matrix.isHermitian_iff_isSymm.mpr
      (cavityBackwardQuadratic_transpose K C hK hC hCdet)).smul (IsSelfAdjoint.all ζ)
  have hLT : (1 - S * L)⁻¹ = T := by
    dsimp [L, T, cavityStepTransition]
    rw [hΔ, Matrix.smul_mul, Matrix.mul_smul]
  have hLS : cavityResolvent L S = T * S := by
    rw [cavityResolvent, hLT]
  have hcov : (T * S).PosSemidef := by
    rw [← hLS]
    exact cavity_tilt_covariance_posSemidef L S hS hQ
  have hpot : (fun z : EuclideanSpace ℝ (Fin d) =>
      ⟪u + z, Matrix.toEuclideanCLM (𝕜 := ℝ) L (u + z)⟫ / 2) =
      (fun z => ζ / 2 * ⟪u + z, Matrix.toEuclideanCLM (𝕜 := ℝ)
        (cavityBackwardQuadratic K C) (u + z)⟫) := by
    funext z
    simp only [L, map_smul, smul_apply, real_inner_smul_right]
    ring
  have hshift := cavity_shifted_gaussian_quadratic_tilt_law L S hL hS hQ u
  rw [hpot, hLT, hLS] at hshift
  let F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun z => u + z
  let G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun y =>
    -Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - P * K)⁻¹ u +
      Matrix.toEuclideanCLM (𝕜 := ℝ) J y
  have hmean : -Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - P * K)⁻¹ u +
      Matrix.toEuclideanCLM (𝕜 := ℝ) J (Matrix.toEuclideanCLM (𝕜 := ℝ) T u) = 0 := by
    rw [← mul_apply_eq_comp, ← map_mul,
      cavity_quadratic_backward_inverse K P C hPdet hCdet, neg_add_cancel]
  have hJcov : J * (T * S) * J.transpose =
      (1 - P * K)⁻¹ * S * ((1 - C * K)⁻¹).transpose :=
    cavity_rescaled_step_covariance K P C S hPdet hCdet
  have hfun : (fun z => Matrix.toEuclideanCLM (𝕜 := ℝ) J (u + z) -
      Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - P * K)⁻¹ u) = G ∘ F := by
    funext z
    dsimp [G, F]
    abel
  change Measure.map _ _ = _
  rw [hfun, ← Measure.map_map (by fun_prop : Measurable G) (by fun_prop : Measurable F),
    hshift, cavity_multivariateGaussian_affine_image J (T * S) hcov _
      (-Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - P * K)⁻¹ u), hmean, hJcov]

end InvariantIsing

end

end OAI
