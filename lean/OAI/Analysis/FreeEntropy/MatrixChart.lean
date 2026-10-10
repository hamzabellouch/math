import OAI.Analysis.FreeEntropy.CoordinateMask

namespace OAI

noncomputable section
open scoped ComplexConjugate
open Finset
namespace FiniteEntropySeparation
 theorem hermitianMatrix_add {n d : ℕ} (a b : MatrixCoordinates n d) (i : Fin n) :
    hermitianMatrix (a+b) i = hermitianMatrix a i + hermitianMatrix b i := by
  ext j k
  simp only [hermitianMatrix, PiLp.add_apply, Matrix.add_apply]
  split_ifs <;> push_cast <;> ring
 theorem hermitianMatrix_smul {n d : ℕ} (r : ℝ) (a : MatrixCoordinates n d) (i : Fin n) :
    hermitianMatrix (r • a) i = r • hermitianMatrix a i := by
  ext j k
  simp only [hermitianMatrix, PiLp.smul_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
  split_ifs <;> push_cast <;> ring
 def hermitianChart (n d : ℕ) : MatrixCoordinates n d →ₗ[ℝ] (Fin n → Matrix (Fin d) (Fin d) ℂ) where
  toFun := hermitianMatrix
  map_add' a b := funext (hermitianMatrix_add a b)
  map_smul' r a := funext (hermitianMatrix_smul r a)
 theorem hermitianMatrix_isHermitian {n d : ℕ} (a : MatrixCoordinates n d) (i : Fin n) :
    (hermitianMatrix a i).IsHermitian := by
  ext j k
  simp only [Matrix.conjTranspose_apply, hermitianMatrix]
  by_cases h : j=k
  · subst k; simp
  · have h' : k ≠ j := Ne.symm h
    rcases lt_or_gt_of_ne h with hjk | hkj
    · simp [h,h',hjk,not_lt_of_gt hjk, Complex.conj_ofReal, sub_eq_add_neg]
    · simp [h,h',hkj,not_lt_of_gt hkj, Complex.conj_ofReal, sub_eq_add_neg]
 theorem hermitianMatrix_normSq {n d : ℕ} (a : MatrixCoordinates n d) (i : Fin n) (j k : Fin d) :
    Complex.normSq (hermitianMatrix a i j k) = (a (i,j,k)^2 + a (i,k,j)^2)/2 := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  unfold hermitianMatrix
  split_ifs with h hlt
  · subst k; simp [Complex.normSq_ofReal]; ring
  · rw [Complex.normSq_div, Complex.normSq_ofReal, hs]
    simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    ring
  · rw [Complex.normSq_div, Complex.normSq_ofReal, hs]
    simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    ring
 theorem hermitianMatrix_frobenius {n d : ℕ} (a : MatrixCoordinates n d) (i : Fin n) :
    (∑ j, ∑ k, Complex.normSq (hermitianMatrix a i j k)) = ∑ j, ∑ k, a (i,j,k)^2 := by
  simp_rw [hermitianMatrix_normSq, add_div]
  simp_rw [sum_add_distrib]
  have he : (∑ j : Fin d, ∑ k : Fin d, a (i,k,j)^2 / 2) = ∑ j : Fin d, ∑ k : Fin d, a (i,j,k)^2 / 2 := sum_comm
  rw [he]
  simp_rw [← sum_div]
  ring
 theorem hermitianChart_normSq {n d : ℕ} (a : MatrixCoordinates n d) :
    (∑ i, ∑ j, ∑ k, Complex.normSq (hermitianMatrix a i j k)) = ‖a‖^2 := by
  simp_rw [hermitianMatrix_frobenius]
  rw [EuclideanSpace.norm_sq_eq]
  simp [Fintype.sum_prod_type, Real.norm_eq_abs, sq_abs]
 theorem hermitianMatrix_continuous {n d : ℕ} (i : Fin n) :
    Continuous (fun a : MatrixCoordinates n d => hermitianMatrix a i) :=
  (continuous_apply i).comp (hermitianChart n d).continuous_of_finiteDimensional
 theorem matrixMoment_continuous {n d : ℕ} (w : List (Fin n)) :
    Continuous (fun a : MatrixCoordinates n d => matrixMoment a w) := by
  have hp : Continuous (fun a : MatrixCoordinates n d => (w.map (hermitianMatrix a)).prod) := by
    induction w with
    | nil => simpa using (continuous_const : Continuous (fun _ : MatrixCoordinates n d => (1 : Matrix (Fin d) (Fin d) ℂ)))
    | cons i w ih => simpa using (hermitianMatrix_continuous i).matrix_mul ih
  unfold matrixMoment Matrix.trace
  exact continuous_const.mul (continuous_finsetSum _ (fun i _ => hp.matrix_elem i i))
end FiniteEntropySeparation

end

end OAI
