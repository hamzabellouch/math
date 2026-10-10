import Mathlib
import OAI.Probability.SKRatio.Matrices.FrobeniusSq

namespace OAI

section
section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKRatioGaussian
namespace ComplexMatrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev lin (M : Matrix ι ι ℂ) := M.toEuclideanLin.toContinuousLinearMap
noncomputable def opNorm (M : Matrix ι ι ℂ) : ℝ := ‖lin M‖
noncomputable def colVec (M : Matrix ι ι ℂ) (k : ι) : EuclideanSpace ℂ ι := WithLp.toLp 2 (fun i => M i k)

lemma frobenius_sq (M : Matrix ι ι ℂ) : ‖M‖^2 = ∑ i,∑ k, ‖M i k‖^2 := by
  rw [Matrix.frobenius_norm_def]
  simp only [Real.rpow_two]
  rw [← Real.sqrt_eq_rpow,Real.sq_sqrt]
  positivity

lemma frobenius_col_sq (M : Matrix ι ι ℂ) : ‖M‖^2 = ∑ k, ‖colVec M k‖^2 := by
  rw [frobenius_sq,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp [EuclideanSpace.norm_sq_eq,colVec]

lemma colVec_mul (M N : Matrix ι ι ℂ) (k : ι) :
    colVec (M*N) k = lin M (colVec N k) := by ext i; rfl

lemma lin_mul (M N : Matrix ι ι ℂ) : lin (M*N) = lin M * lin N := by
  apply ContinuousLinearMap.ext
  intro x
  exact congrArg (fun T : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι => T x)
    (Matrix.toLpLin_mul 2 2 2 M N)

lemma lin_one : lin (1 : Matrix ι ι ℂ) = 1 := by
  ext x i
  change (Matrix.mulVec 1 (WithLp.ofLp x)) i = x i
  simp

lemma frobenius_mul_le_opNorm (M N : Matrix ι ι ℂ) : ‖M*N‖ ≤ opNorm M * ‖N‖ := by
  have hp : 0 ≤ opNorm M := norm_nonneg _
  apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg hp (norm_nonneg N))
  simp only [← sq]
  rw [frobenius_col_sq,mul_pow,frobenius_col_sq,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  rw [colVec_mul]
  have hh := (lin M).le_opNorm (colVec N k)
  change ‖lin M (colVec N k)‖ ≤ opNorm M * ‖colVec N k‖ at hh
  nlinarith only [hh,norm_nonneg (lin M (colVec N k)),mul_nonneg hp (norm_nonneg (colVec N k))]

lemma lin_adjoint (M : Matrix ι ι ℂ) : lin Mᴴ = (lin M).adjoint := by
  rw [lin,Matrix.toEuclideanLin_conjTranspose_eq_adjoint,LinearMap.adjoint_toContinuousLinearMap]

lemma opNorm_adjoint (M : Matrix ι ι ℂ) : opNorm Mᴴ = opNorm M := by
  rw [opNorm,lin_adjoint,ContinuousLinearMap.adjoint.norm_map]
  rfl

lemma frobenius_mul_le_opNorm_right (M N : Matrix ι ι ℂ) : ‖M*N‖ ≤ ‖M‖ * opNorm N := by
  rw [← Matrix.frobenius_norm_conjTranspose (M*N),Matrix.conjTranspose_mul]
  exact (frobenius_mul_le_opNorm Nᴴ Mᴴ).trans_eq (by rw [opNorm_adjoint,Matrix.frobenius_norm_conjTranspose,mul_comm])

lemma lin_unitary (U : Matrix ι ι ℂ) (hU : U ∈ unitary (Matrix ι ι ℂ)) :
    lin U ∈ unitary (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) := by
  change (lin U).adjoint * lin U = 1 ∧ lin U * (lin U).adjoint = 1
  rw [← lin_adjoint,← lin_mul,← lin_mul]
  constructor
  · rw [show Uᴴ * U = 1 from Unitary.star_mul_self_of_mem hU,lin_one]
  · rw [show U * Uᴴ = 1 from Unitary.mul_star_self_of_mem hU,lin_one]

lemma frobenius_unitary_mul (U M : Matrix ι ι ℂ) (hU : U ∈ unitary (Matrix ι ι ℂ)) :
    ‖U*M‖ = ‖M‖ := by
  have hh : ‖U*M‖^2 = ‖M‖^2 := by
    rw [frobenius_col_sq,frobenius_col_sq]
    apply Finset.sum_congr rfl
    intro k _
    rw [colVec_mul,ContinuousLinearMap.norm_map_of_mem_unitary (lin_unitary U hU)]
  nlinarith [norm_nonneg (U*M),norm_nonneg M]

lemma frobenius_mul_unitary (M U : Matrix ι ι ℂ) (hU : U ∈ unitary (Matrix ι ι ℂ)) :
    ‖M*U‖ = ‖M‖ := by
  rw [← Matrix.frobenius_norm_conjTranspose (M*U),Matrix.conjTranspose_mul]
  rw [frobenius_unitary_mul Uᴴ Mᴴ (Unitary.star_mem hU),Matrix.frobenius_norm_conjTranspose]

end ComplexMatrix
end SKRatioGaussian

end
end
end
end
end
end
end
end
end

end OAI
