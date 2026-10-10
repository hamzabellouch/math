import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.Polynomial.Eval.Degree

namespace OAI

/-! # Recover polynomial coefficients in a submodule from scalar evaluations -/

noncomputable section
namespace PolycyclicRecognition
open scoped Polynomial
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

def scalarMatrixVec {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (v : Fin n → V) : Fin n → V :=
  fun i => ∑ j, A i j • v j

theorem scalarMatrixVec_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) K) (v : Fin n → V) :
    scalarMatrixVec (A * B) v = scalarMatrixVec A (scalarMatrixVec B v) := by
  funext i
  simp only [scalarMatrixVec, Matrix.mul_apply, Finset.sum_smul, mul_smul, Finset.smul_sum]
  rw [Finset.sum_comm]

@[simp] theorem scalarMatrixVec_one {n : ℕ} (v : Fin n → V) :
    scalarMatrixVec (1 : Matrix (Fin n) (Fin n) K) v = v := by
  classical
  funext i
  simp [scalarMatrixVec, Matrix.one_apply]

theorem mem_submodule_of_scalarMatrixVec_mem {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (hA : A.det ≠ 0) (S : Submodule K V) (v : Fin n → V)
    (hv : ∀ i, scalarMatrixVec A v i ∈ S) (i : Fin n) : v i ∈ S := by
  have hi : scalarMatrixVec A⁻¹ (scalarMatrixVec A v) = v := by
    rw [← scalarMatrixVec_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA),
      scalarMatrixVec_one]
  rw [← hi]
  exact S.sum_mem (fun j _ => S.smul_mem _ (hv j))

variable {A : Type} [CommRing A] [Algebra K A]

theorem polynomial_coeff_mem_of_evaluations {n : ℕ} (p : A[X]) (hn : p.natDegree < n)
    (c : Fin n → K) (hc : Function.Injective c) (S : Submodule K A)
    (hv : ∀ i, p.eval (algebraMap K A (c i)) ∈ S) (i : Fin n) :
    p.coeff i.val ∈ S := by
  have he : scalarMatrixVec (Matrix.vandermonde c) (fun j => p.coeff j.val) =
      fun j => p.eval (algebraMap K A (c j)) := by
    funext j
    rw [Polynomial.eval_eq_sum_range' hn]
    simp only [scalarMatrixVec, Matrix.vandermonde_apply, Algebra.smul_def, map_pow]
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k _
    exact mul_comm _ _
  exact mem_submodule_of_scalarMatrixVec_mem (Matrix.vandermonde c)
    (Matrix.det_vandermonde_ne_zero_iff.mpr hc) S (fun j => p.coeff j.val)
    (fun j => he ▸ hv j) i

end PolycyclicRecognition

end

end OAI
