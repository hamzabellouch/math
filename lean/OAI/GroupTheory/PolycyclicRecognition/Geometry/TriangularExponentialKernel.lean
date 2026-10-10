import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularMatrixExponential
import OAI.GroupTheory.PolycyclicRecognition.Geometry.PositiveSizeTriangularRepresentation
import OAI.GroupTheory.PolycyclicRecognition.Geometry.AlgebraExponential
import OAI.GroupTheory.PolycyclicRecognition.Geometry.AnalyticNilpotentLogarithm

namespace OAI

/-! # Positive triangular exponentials and their kernel

A faithful triangular Lie representation exponentiates into the positive
triangular group. Nilradical exponentials are unipotent, and a real upper
triangular matrix with exponential equal to the identity is zero.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Matrix.Norms.Operator

variable {n : ℕ}

def positiveTriangularExp (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsUpperTriangular) :
    positiveTriangular n :=
  ⟨algebraExpUnit A, matrix_exp_upperTriangular A hA,
    fun i => by
      change 0 < NormedSpace.exp A i i
      rw [matrix_exp_diagonal A hA i]
      exact Real.exp_pos _⟩

@[simp] theorem positiveTriangularExp_matrix (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsUpperTriangular) :
    PositiveTriangular.matrix (positiveTriangularExp A hA) = NormedSpace.exp A := rfl

theorem triangular_nilpotent_exp_unipotent (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsUpperTriangular) (hn : IsNilpotent A) : StrictUpper (NormedSpace.exp A - 1) := by
  intro i j hji
  rcases hji.eq_or_lt with h | h
  · subst j
    rw [Matrix.sub_apply, matrix_exp_diagonal A hA, upperTriangular_nilpotent_diag A hA hn]
    simp
  · rw [Matrix.sub_apply, matrix_exp_upperTriangular A hA h,
      Matrix.one_apply_ne (ne_of_gt h), sub_self]

theorem triangular_exp_eq_one_iff (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsUpperTriangular) : NormedSpace.exp A = 1 ↔ A = 0 := by
  constructor
  · intro he
    have hdiag (i : Fin n) : A i i = 0 := by
      have hi := congrArg (fun B : Matrix (Fin n) (Fin n) ℝ => B i i) he
      rw [matrix_exp_diagonal A hA] at hi
      apply Real.exp_injective
      simpa only [Real.exp_zero, Matrix.one_apply_eq] using hi
    have hn := upperTriangular_nilpotent_of_diag_zero A hA hdiag
    obtain ⟨k, hk⟩ := hn
    let : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℝ) :=
      NormedAlgebra.restrictScalars ℚ ℝ _
    have hk' : A ^ (k + 1) = 0 := by rw [pow_succ, hk, zero_mul]
    have h := finiteNilpotentLog_analytic_exp A k hk'
    have hz : finiteNilpotentLog (k + 1) (0 : Matrix (Fin n) (Fin n) ℝ) = 0 := by
      rw [finiteNilpotentLog, ← Polynomial.coeff_zero_eq_aeval_zero']
      simp [PowerSeries.coeff_trunc, PowerSeries.coeff_log]
    have he' : NormedSpace.exp A - 1 = (0 : Matrix (Fin n) (Fin n) ℝ) :=
      (congrArg (fun B : Matrix (Fin n) (Fin n) ℝ => B - 1) he).trans (sub_self 1)
    exact h.symm.trans ((congrArg (finiteNilpotentLog (k + 1)) he').trans hz)
  · rintro rfl
    exact NormedSpace.exp_zero

end PolycyclicRecognition

end

end OAI
