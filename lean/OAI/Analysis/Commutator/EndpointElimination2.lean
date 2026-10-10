import Mathlib
import OAI.Analysis.Commutator.EndpointModule2

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison

variable {I : Type*} [Fintype I] [DecidableEq I]

def matrixL1 (A : Matrix I I ℂ) : ℝ :=
  (normalizedTrace (CFC.sqrt (star A * A))).re

def matrixL2 (A : Matrix I I ℂ) : ℝ :=
  Real.sqrt (normalizedTrace (star A * A)).re

lemma single_nonneg (j : I) : 0 ≤ Matrix.single j j (1 : ℂ) := by
  have h := star_mul_self_nonneg (Matrix.single j j (1 : ℂ))
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single,
    star_one, Matrix.single_mul_single_same, one_mul] using h

lemma sqrt_single (j : I) :
    CFC.sqrt (Matrix.single j j (1 : ℂ)) = Matrix.single j j (1 : ℂ) := by
  apply (CFC.sqrt_eq_iff _ _ (single_nonneg j) (single_nonneg j)).mpr
  simp only [Matrix.single_mul_single_same, one_mul]

@[simp] theorem matrixL1_single (i j : I) :
    matrixL1 (Matrix.single i j 1) = (Fintype.card I : ℝ)⁻¹ := by
  simp only [matrixL1, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single,
    star_one, Matrix.single_mul_single_same, sqrt_single,
    normalizedTrace, Matrix.trace_single_eq_same, mul_one]
  simp only [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_re]

@[simp] theorem matrixL2_single (i j : I) :
    matrixL2 (Matrix.single i j 1) = Real.sqrt (Fintype.card I : ℝ)⁻¹ := by
  simp only [matrixL2, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single,
    star_one, Matrix.single_mul_single_same,
    normalizedTrace, Matrix.trace_single_eq_same, mul_one]
  congr 1
  simp only [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_re]

end Kadison
end

end OAI
