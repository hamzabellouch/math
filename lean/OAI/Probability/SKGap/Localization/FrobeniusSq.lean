import Mathlib
import OAI.Probability.SKGap.Matrix.OpNorm

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
namespace SKGap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma frobenius_sq (M : Matrix ι ι ℝ) : ‖M‖^2 = ∑ i,∑ k, (M i k)^2 := by
  rw [Matrix.frobenius_norm_def]
  simp only [Real.rpow_two, Real.norm_eq_abs,sq_abs]
  rw [← Real.sqrt_eq_rpow,Real.sq_sqrt]
  positivity

lemma frobenius_col_sq (M : Matrix ι ι ℝ) : ‖M‖^2 = ∑ k, ‖colVec M k‖^2 := by
  rw [frobenius_sq,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [EuclideanSpace.norm_sq_eq]
  simp [colVec,Real.norm_eq_abs,sq_abs]

lemma colVec_mul (M N : Matrix ι ι ℝ) (k : ι) :
    colVec (M*N) k = M.toEuclideanLin.toContinuousLinearMap (colVec N k) := by
  ext i
  rfl

lemma frobenius_mul_le_opNorm (M N : Matrix ι ι ℝ) : ‖M*N‖ ≤ opNorm M * ‖N‖ := by
  have hp : 0 ≤ opNorm M := norm_nonneg _
  apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg hp (norm_nonneg N))
  simp only [← sq]
  rw [frobenius_col_sq,mul_pow,frobenius_col_sq,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  rw [colVec_mul]
  have hh := M.toEuclideanLin.toContinuousLinearMap.le_opNorm (colVec N k)
  change ‖M.toEuclideanLin.toContinuousLinearMap (colVec N k)‖ ≤ opNorm M * ‖colVec N k‖ at hh
  nlinarith only [hh, norm_nonneg (M.toEuclideanLin.toContinuousLinearMap (colVec N k)),
    mul_nonneg hp (norm_nonneg (colVec N k))]

lemma opNorm_transpose (M : Matrix ι ι ℝ) : opNorm Mᵀ = opNorm M := by
  change ‖Mᵀ.toEuclideanLin.toContinuousLinearMap‖ = ‖M.toEuclideanLin.toContinuousLinearMap‖
  have he : Mᵀ.toEuclideanLin.toContinuousLinearMap =
      ContinuousLinearMap.adjoint M.toEuclideanLin.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℝ
    intro y
    rw [ContinuousLinearMap.adjoint_inner_right]
    change (∑ i, (∑ k, M k i*x k)*y i) = ∑ i, x i * (∑ k, M i k*y k)
    simp only [Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he,ContinuousLinearMap.adjoint.norm_map]

lemma frobenius_mul_le_opNorm_right (M N : Matrix ι ι ℝ) : ‖M*N‖ ≤ ‖M‖ * opNorm N := by
  rw [← Matrix.frobenius_norm_transpose (M*N),Matrix.transpose_mul]
  exact (frobenius_mul_le_opNorm Nᵀ Mᵀ).trans_eq (by rw [opNorm_transpose,Matrix.frobenius_norm_transpose,mul_comm])

end SKGap

end

end OAI
