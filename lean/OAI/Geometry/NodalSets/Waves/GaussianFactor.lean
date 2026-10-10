import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Probability.Distributions.Gaussian.Multivariate

namespace OAI

namespace Yau.Probability
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace MatrixOrder
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

local notation "E" => EuclideanSpace ℝ ι

def covarianceMatrix (T : F →L[ℝ] E) : Matrix ι ι ℝ :=
  (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)).symm (T ∘L T.adjoint)

def covarianceFactor (T : F →L[ℝ] E) : E →L[ℝ] E :=
  (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) (CFC.sqrt (covarianceMatrix T))

lemma covarianceMatrix_posSemidef (T : F →L[ℝ] E) : (covarianceMatrix T).PosSemidef := by
  rw [← Matrix.isPositive_toEuclideanLin_iff,
    ← LinearMap.isPositive_toContinuousLinearMap_iff]
  change ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) (covarianceMatrix T)).IsPositive
  simpa [covarianceMatrix] using ContinuousLinearMap.isPositive_self_comp_adjoint T

lemma covarianceFactor_selfAdjoint (T : F →L[ℝ] E) : IsSelfAdjoint (covarianceFactor T) :=
  (CFC.sqrt_nonneg (covarianceMatrix T)).isSelfAdjoint.map (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ))

lemma covarianceFactor_sq (T : F →L[ℝ] E) :
    covarianceFactor T ∘L covarianceFactor T = T ∘L T.adjoint := by
  change (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) (CFC.sqrt (covarianceMatrix T)) *
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) (CFC.sqrt (covarianceMatrix T)) = _
  rw [← map_mul, CFC.sqrt_mul_sqrt_self _ (covarianceMatrix_posSemidef T).nonneg]
  exact (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)).apply_symm_apply _

lemma covarianceFactor_inner (T : F →L[ℝ] E) (x y : E) :
    ⟪covarianceFactor T x, covarianceFactor T y⟫ = ⟪T.adjoint x, T.adjoint y⟫ := by
  rw [← ContinuousLinearMap.adjoint_inner_right,
    (covarianceFactor_selfAdjoint T).adjoint_eq]
  change ⟪x, (covarianceFactor T ∘L covarianceFactor T) y⟫ = _
  rw [covarianceFactor_sq, ContinuousLinearMap.comp_apply,
    ← ContinuousLinearMap.adjoint_inner_left]

variable [MeasurableSpace F] [BorelSpace F]

lemma gaussian_covariance_factorization (T : F →L[ℝ] E) :
    (stdGaussian F).map T = (stdGaussian E).map (covarianceFactor T) := by
  apply IsGaussian.ext
  · simp only [id_eq]
    rw [T.integral_id_map IsGaussian.integrable_id,
      (covarianceFactor T).integral_id_map IsGaussian.integrable_id]
    simp
  · ext x y
    rw [covarianceBilin_map IsGaussian.memLp_two_id,
      covarianceBilin_map IsGaussian.memLp_two_id,
      covarianceBilin_stdGaussian,covarianceBilin_stdGaussian,
      innerSL_apply_apply,innerSL_apply_apply,
      (covarianceFactor_selfAdjoint T).adjoint_eq]
    exact (covarianceFactor_inner T x y).symm

end
end Yau.Probability

end OAI
