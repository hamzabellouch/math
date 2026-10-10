import OAI.GroupTheory.PolycyclicRecognition.Geometry.ComplexNilradical
import Mathlib.RingTheory.Adjoin.Polynomial.Basic

namespace OAI

/-! # Polynomial calculus on a complex triangular flag -/

noncomputable section
namespace PolycyclicRecognition

theorem complex_matrix_aeval_upper {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsUpperTriangular) (p : Polynomial ℂ) :
    (Polynomial.aeval A p).IsUpperTriangular := by
  have hle : Algebra.adjoin ℂ {A} ≤
      Matrix.blockTriangularSubalgebra ℂ ℂ (id : Fin n → Fin n) := by
    apply Algebra.adjoin_le
    intro B hB
    obtain rfl := Set.mem_singleton_iff.mp hB
    exact hA
  exact hle (p.aeval_mem_adjoin_singleton ℂ A)

theorem complex_matrix_aeval_diagonal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsUpperTriangular) (p : Polynomial ℂ) (i : Fin n) :
    Polynomial.aeval A p i i = p.eval (A i i) := by
  induction p using Polynomial.induction_on with
  | C a => simp [Matrix.algebraMap_eq_diagonal]
  | add p q hp hq => simp only [map_add, Matrix.add_apply, Polynomial.eval_add, hp, hq]
  | monomial k a hk =>
    rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X,
      ComplexTriangularAdjoint.diagonal_mul _ _
        (complex_matrix_aeval_upper A hA _) hA,
      hk]
    simp only [Polynomial.eval_mul,Polynomial.eval_X]

theorem complex_upper_nilpotent_diagonal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsUpperTriangular) (hnil : IsNilpotent A) (i : Fin n) : A i i = 0 := by
  obtain ⟨k,hk⟩ := hnil
  apply IsNilpotent.eq_zero
  refine ⟨k,?_⟩
  rw [← ComplexTriangularAdjoint.diagonal_pow A hA k i,hk]
  rfl

end PolycyclicRecognition

end

end OAI
