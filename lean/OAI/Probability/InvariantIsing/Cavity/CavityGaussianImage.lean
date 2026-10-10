import OAI.Probability.InvariantIsing.Cavity.CavityFiniteGaussian

namespace OAI

/-! Rectangular Gaussian images, used for finitely many replica
projections of a fresh frame. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix

namespace InvariantIsing

lemma cavity_rectangular_adjoint {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (B : Matrix a b ℝ) :
    B.toEuclideanLin.toContinuousLinearMap.adjoint =
      B.transpose.toEuclideanLin.toContinuousLinearMap := by
  rw [← LinearMap.adjoint_toContinuousLinearMap,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  rfl

theorem cavity_standardGaussian_image {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (B : Matrix a b ℝ) :
    (stdGaussian (EuclideanSpace ℝ b)).map B.toEuclideanLin.toContinuousLinearMap =
      multivariateGaussian 0 (B * B.transpose) := by
  let L := B.toEuclideanLin.toContinuousLinearMap
  have hB : (B * B.transpose).PosSemidef := by
    simpa using
      Matrix.posSemidef_self_mul_conjTranspose B
  apply IsGaussian.ext
  · simp only [id_eq]
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id]
    simp only [integral_id_stdGaussian, map_zero, integral_id_multivariateGaussian]
  · ext u v
    rw [covarianceBilin_map IsGaussian.memLp_two_id L, covarianceBilin_stdGaussian,
      innerSL_apply_apply, ContinuousLinearMap.adjoint_inner_left,
      covarianceBilin_multivariateGaussian hB]
    have he : L (L.adjoint v) = (B * B.transpose).toEuclideanLin v := by
      rw [show L.adjoint = B.transpose.toEuclideanLin.toContinuousLinearMap from
        cavity_rectangular_adjoint B]
      ext i
      change (B *ᵥ (B.transpose *ᵥ fun j => v j)) i =
        ((B * B.transpose) *ᵥ fun j => v j) i
      rw [Matrix.mulVec_mulVec]
    rw [he]
    exact Matrix.inner_toEuclideanCLM (B * B.transpose) u v

end InvariantIsing

end

end OAI
