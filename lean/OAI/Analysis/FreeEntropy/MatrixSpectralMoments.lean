import OAI.Analysis.FreeEntropy.BlockEventLower

namespace OAI

noncomputable section
open Finset
open scoped ComplexConjugate
namespace FiniteEntropySeparation
variable {n d : ℕ}
 theorem matrixWord_unitary_conjugate (U : unitary (Matrix (Fin d) (Fin d) ℂ))
    (A : Fin n → Matrix (Fin d) (Fin d) ℂ) (w : List (Fin n)) :
    (w.map (fun i => star (U:Matrix (Fin d) (Fin d) ℂ)*A i*(U:Matrix (Fin d) (Fin d) ℂ))).prod =
      star (U:Matrix (Fin d) (Fin d) ℂ)*(w.map A).prod*(U:Matrix (Fin d) (Fin d) ℂ) := by
  induction w with
  | nil => simp []
  | cons i w ih =>
    simp only [List.map_cons,List.prod_cons,ih]
    have hU : (U:Matrix (Fin d) (Fin d) ℂ)*star (U:Matrix (Fin d) (Fin d) ℂ)=1 := by simp
    calc
      _ = star (U:Matrix (Fin d) (Fin d) ℂ)*A i*((U:Matrix (Fin d) (Fin d) ℂ)*star (U:Matrix (Fin d) (Fin d) ℂ))*(w.map A).prod*(U:Matrix (Fin d) (Fin d) ℂ) := by noncomm_ring
      _ = _ := by rw [hU]; noncomm_ring
 theorem trace_unitary_conjugate (U : unitary (Matrix (Fin d) (Fin d) ℂ)) (A : Matrix (Fin d) (Fin d) ℂ) :
    Matrix.trace (star (U:Matrix (Fin d) (Fin d) ℂ)*A*(U:Matrix (Fin d) (Fin d) ℂ))=Matrix.trace A := by
  rw [Matrix.trace_mul_cycle]
  have hU : (U:Matrix (Fin d) (Fin d) ℂ)*star (U:Matrix (Fin d) (Fin d) ℂ)=1 := by simp
  rw [hU,one_mul]
 theorem matrixMoment_rotate (U : unitary (Matrix (Fin d) (Fin d) ℂ)) (a : MatrixCoordinates n d) (w : List (Fin n)) :
    matrixMoment (rotateCoordinates U a) w=matrixMoment a w := by
  unfold matrixMoment
  have he : hermitianMatrix (rotateCoordinates U a)=fun i => star (U:Matrix (Fin d) (Fin d) ℂ)*hermitianMatrix a i*U := funext (hermitianMatrix_rotate U a)
  rw [he]
  rw [matrixWord_unitary_conjugate,trace_unitary_conjugate]
 theorem matrixMoment_replicate (a : MatrixCoordinates n d) (i : Fin n) (k : ℕ) :
    matrixMoment a (List.replicate k i)=(d:ℂ)⁻¹*Matrix.trace (hermitianMatrix a i^k) := by
  simp [matrixMoment]
 theorem diagonal_eigenvalues (a : MatrixCoordinates n d) (i : Fin n) :
    hermitianMatrix (rotateCoordinates (hermitianMatrix_isHermitian a i).eigenvectorUnitary a) i =
      Matrix.diagonal (fun j => ((hermitianMatrix_isHermitian a i).eigenvalues j:ℂ)) := by
  rw [hermitianMatrix_rotate]
  simpa [Unitary.conjStarAlgAut_apply,Function.comp_def] using (hermitianMatrix_isHermitian a i).conjStarAlgAut_star_eigenvectorUnitary
 theorem matrixMoment_eigenvalues (a : MatrixCoordinates n d) (i : Fin n) (k : ℕ) :
    (matrixMoment a (List.replicate k i)).re=(d:ℝ)⁻¹*∑j,((hermitianMatrix_isHermitian a i).eigenvalues j)^k := by
  rw [← matrixMoment_rotate (hermitianMatrix_isHermitian a i).eigenvectorUnitary a,
    matrixMoment_replicate,diagonal_eigenvalues,Matrix.diagonal_pow,Matrix.trace_diagonal]
  simp only [Pi.pow_apply,← Complex.ofReal_pow,← Complex.ofReal_sum,← Complex.ofReal_natCast,← Complex.ofReal_inv,← Complex.ofReal_mul,Complex.ofReal_re]
 def matrixUnivariateMoment (q : Polynomial ℝ) (a : MatrixCoordinates n d) (i : Fin n) : ℝ :=
    ∑k∈q.support,q.coeff k*(matrixMoment a (List.replicate k i)).re
 theorem matrixUnivariateMoment_eigenvalues (q : Polynomial ℝ) (a : MatrixCoordinates n d) (i : Fin n) :
    matrixUnivariateMoment q a i=(d:ℝ)⁻¹*∑j,q.eval ((hermitianMatrix_isHermitian a i).eigenvalues j) := by
  unfold matrixUnivariateMoment
  simp_rw [matrixMoment_eigenvalues]
  simp only [mul_left_comm (q.coeff _),← mul_sum]
  congr 1
  simp only [Polynomial.eval_eq_sum,Polynomial.sum]
  rw [sum_comm]
  simp only [mul_sum]
 theorem equidiscreteAtom_injective {p : ℕ} (hp : 2≤p) : Function.Injective (equidiscreteAtom p) := by
  intro l k h
  have hd : (p:ℝ)-1≠0 := by
    have hh : (2:ℝ)≤p := by exact_mod_cast hp
    linarith
  unfold equidiscreteAtom at h
  have he : (l.val:ℝ)=(k.val:ℝ) := by field_simp [hd] at h; linarith
  exact Fin.ext (by exact_mod_cast he)
end FiniteEntropySeparation

end

end OAI
