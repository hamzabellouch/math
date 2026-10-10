import OAI.Probability.InvariantIsing.Cavity.CavityGaussianImage
import OAI.Probability.InvariantIsing.Cavity.CavityGaussianFactor

namespace OAI

/-! The square affine image needed after standard-Gaussian square completion. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix Matrix.Norms.L2Operator

namespace InvariantIsing

theorem cavity_multivariateGaussian_affine_image {d : ℕ}
    (B S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (m u : EuclideanSpace ℝ (Fin d)) :
    (multivariateGaussian m S).map (fun z => u + Matrix.toEuclideanCLM (𝕜 := ℝ) B z) =
      multivariateGaussian (u + Matrix.toEuclideanCLM (𝕜 := ℝ) B m)
        (B * S * B.transpose) := by
  let L := Matrix.toEuclideanCLM (𝕜 := ℝ) B
  have hp : (B * S * B.transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hS.mul_mul_conjTranspose_same B
  have he : (fun z => u + L z) = (fun z => u + z) ∘ L := rfl
  change (multivariateGaussian m S).map (fun z => u + L z) = _
  rw [he, ← Measure.map_map (by fun_prop) (by fun_prop)]
  apply IsGaussian.ext
  · rw [integral_map (by fun_prop) (by fun_prop)]
    change (∫ z, u + z ∂(multivariateGaussian m S).map L) = _
    have hsplit := integral_add (f := fun _ : EuclideanSpace ℝ (Fin d) => u)
      (g := fun z : EuclideanSpace ℝ (Fin d) => z)
      (μ := (multivariateGaussian m S).map L) (integrable_const _) IsGaussian.integrable_id
    rw [hsplit, integral_const,
      L.integral_id_map IsGaussian.integrable_id]
    simp only [probReal_univ, one_smul, integral_id_multivariateGaussian,
      integral_id_multivariateGaussian']
    rfl
  · rw [covarianceBilin_map_const_add]
    ext x y
    rw [covarianceBilin_map IsGaussian.memLp_two_id L,
      covarianceBilin_multivariateGaussian hS, covarianceBilin_multivariateGaussian hp]
    rw [← Matrix.inner_toEuclideanCLM S, ContinuousLinearMap.adjoint_inner_left]
    have hL : L.adjoint = Matrix.toEuclideanCLM (𝕜 := ℝ) B.transpose :=
      cavity_rectangular_adjoint B
    rw [hL, ← Matrix.inner_toEuclideanCLM (B * S * B.transpose)]
    simp only [map_mul, mul_apply_eq_comp]
    rfl

end InvariantIsing

end

end OAI
