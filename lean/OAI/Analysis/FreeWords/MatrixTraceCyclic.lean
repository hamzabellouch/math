import Mathlib
import OAI.Analysis.FreeWords.MatrixConditionalExpectation

namespace OAI

noncomputable section

namespace KKMatrixExpectation

noncomputable section

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

omit [StarRing A] [StarModule ℂ A] in
theorem matrixTraceMap_cyclic (τ : A →ₗ[ℂ] ℂ)
    (htr : ∀a b,τ (a*b)=τ (b*a)) (n : ℕ)
    (x y : Matrix (Fin n) (Fin n) A) : matrixTraceMap τ n (x*y)=matrixTraceMap τ n (y*x) := by
  simp only [matrixTraceMap_apply,Matrix.mul_apply,map_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact htr _ _

theorem matrixTraceMap_test_entry (τ : A →ₗ[ℂ] ℂ) {n : ℕ} (hn : 0<n)
    (x : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    τ (x i j)=(n:ℂ)*matrixTraceMap τ n (x*numericalHom n (Matrix.single j i 1)) := by
  have hsingle : numericalHom (A := A) n (Matrix.single j i 1)=Matrix.single j i 1 := by
    ext k l
    simp only [numericalHom_apply,Matrix.single_apply]
    split_ifs <;> simp
  rw [hsingle,matrixTraceMap_apply,← map_sum]
  change τ (x i j)=(n:ℂ)*((n:ℂ)⁻¹*τ (Matrix.trace (x*Matrix.single j i 1)))
  rw [Matrix.trace_mul_single]
  simp only [MulOpposite.op_one,one_smul]
  have hn0 : (n:ℂ)≠0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp

end

end KKMatrixExpectation
end

end OAI
