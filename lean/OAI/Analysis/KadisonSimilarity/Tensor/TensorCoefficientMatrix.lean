import OAI.Analysis.KadisonSimilarity.Tensor.TensorMatrixAlgebra
import Mathlib.Data.Matrix.Basis

namespace OAI

/-! The trace-pairing bridge from invariant multilinear forms to the
commutant of finite tensor powers. -/

noncomputable section
namespace KadisonSimilarity

open Finset

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

omit [Fintype ι] [DecidableEq ι] [Fintype α] in
theorem tensorMatrixUnit_as_single (a b : α) :
    tensorMatrixUnit a b = Matrix.single a b (1 : ℂ) := by
  ext r c
  simp only [tensorMatrixUnit_apply, Matrix.single_apply, eq_comm]

theorem matrix_eq_sum_tensorMatrixUnit (a : Matrix α α ℂ) :
    a = ∑ r, ∑ c, a r c • tensorMatrixUnit r c := by
  simpa only [tensorMatrixUnit_as_single, Matrix.smul_single, smul_eq_mul, mul_one] using
    Matrix.matrix_eq_sum_single a

/-- Expansion in matrix units, keeping one row and column label per slot. -/
theorem multilinear_matrix_expansion
    (F : MultilinearMap ℂ (fun _ : ι => Matrix α α ℂ) ℂ)
    (v : ι → Matrix α α ℂ) :
    F v = ∑ r : ι → α, ∑ c : ι → α,
      (∏ i, v i (r i) (c i)) * F (fun i => tensorMatrixUnit (r i) (c i)) := by
  have hv : v = fun i => ∑ r, ∑ c, v i r c • tensorMatrixUnit r c := by
    funext i
    exact matrix_eq_sum_tensorMatrixUnit (v i)
  conv_lhs => rw [hv]
  rw [F.map_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [F.map_sum]
  apply Finset.sum_congr rfl
  intro c _
  exact F.map_smul_univ (fun i => v i (r i) (c i))
    (fun i => tensorMatrixUnit (r i) (c i))

/-- The transposed matrix-unit coefficients give the trace-dual matrix. -/
def tensorCoefficientMatrix
    (F : MultilinearMap ℂ (fun _ : ι => Matrix α α ℂ) ℂ) :
    Matrix (ι → α) (ι → α) ℂ :=
  Matrix.of fun f g => F (fun i => tensorMatrixUnit (g i) (f i))

theorem multilinear_eq_trace_tensorCoefficient
    (F : MultilinearMap ℂ (fun _ : ι => Matrix α α ℂ) ℂ)
    (v : ι → Matrix α α ℂ) :
    F v = Matrix.trace (tensorCoefficientMatrix F * tupleTensorMatrix v) := by
  rw [multilinear_matrix_expansion]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
    tensorCoefficientMatrix, Matrix.of_apply, tupleTensorMatrix_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro c _
  exact mul_comm _ _

omit [DecidableEq ι] [Fintype α] in
theorem tupleTensorMatrix_matrixUnits (r c : ι → α) :
    tupleTensorMatrix (fun i => tensorMatrixUnit (r i) (c i)) =
      Matrix.single r c (1 : ℂ) := by
  ext f g
  simp only [tupleTensorMatrix_apply, tensorMatrixUnit_apply, Fintype.prod_boole,
    Matrix.single_apply]
  congr 1
  apply propext
  simp only [forall_and, funext_iff, eq_comm]

/-- Tensor products of matrix units separate the trace pairing. -/
theorem eq_of_trace_tupleTensorMatrix_eq (A B : Matrix (ι → α) (ι → α) ℂ)
    (h : ∀ v : ι → Matrix α α ℂ,
      Matrix.trace (A * tupleTensorMatrix v) = Matrix.trace (B * tupleTensorMatrix v)) : A = B := by
  ext f g
  have hfg := h (fun i => tensorMatrixUnit (g i) (f i))
  rw [tupleTensorMatrix_matrixUnits] at hfg
  simpa [Matrix.trace_mul_single] using hfg

/-- An invariant form has a trace-dual matrix commuting with every tensor
power of a unitary. -/
theorem tensorCoefficientMatrix_commutes_unitary
    (F : MultilinearMap ℂ (fun _ : ι => Matrix α α ℂ) ℂ)
    (hF : UnitaryConjugationInvariant F) (u : Matrix.unitaryGroup α ℂ) :
    tensorCoefficientMatrix F * tupleTensorMatrix (fun _ : ι => (u : Matrix α α ℂ)) =
      tupleTensorMatrix (fun _ : ι => (u : Matrix α α ℂ)) * tensorCoefficientMatrix F := by
  let U := tupleTensorMatrix (fun _ : ι => (u : Matrix α α ℂ))
  let C := tensorCoefficientMatrix F
  have hU : U * star U = 1 := by
    rw [← tupleTensorMatrix_star, ← tupleTensorMatrix_mul]
    simpa only [u.property.2] using (tupleTensorMatrix_one (ι := ι) (α := α))
  have hC : star U * C * U = C := by
    apply eq_of_trace_tupleTensorMatrix_eq
    intro v
    have h := hF u v
    simp only [multilinear_eq_trace_tensorCoefficient, tupleTensorMatrix_mul,
      tupleTensorMatrix_star] at h
    change Matrix.trace (C * (U * tupleTensorMatrix v * star U)) =
      Matrix.trace (C * tupleTensorMatrix v) at h
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_cycle] at h
    simpa only [Matrix.mul_assoc] using h
  change C * U = U * C
  calc
    C * U = (U * star U) * (C * U) := by rw [hU, Matrix.one_mul]
    _ = U * (star U * C * U) := by simp only [Matrix.mul_assoc]
    _ = U * C := by rw [hC]

end KadisonSimilarity

end

end OAI
