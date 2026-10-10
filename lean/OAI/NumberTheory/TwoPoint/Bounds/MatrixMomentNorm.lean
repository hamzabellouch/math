import OAI.NumberTheory.TwoPoint.Bounds.MatrixClosedWords
import OAI.NumberTheory.TwoPoint.Bounds.MatrixAction
import OAI.NumberTheory.TwoPoint.Bounds.WeightedRows

namespace OAI

/-! The unnormalized matrix moment controls the operator norm used in the spectral step. -/

namespace TwoPointCorrelations

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma real_matrix_row_square (A : Matrix V V ℝ) (v : V → ℂ) (i : V) :
    ‖∑ j, (A i j : ℂ) * v j‖ ^ 2 ≤
      (∑ j, (A i j) ^ 2) * ∑ j, ‖v j‖ ^ 2 := by
  have htri : ‖∑ j, (A i j : ℂ) * v j‖ ≤ ∑ j, |A i j| * ‖v j‖ := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs] using
      norm_sum_le univ (fun j => (A i j : ℂ) * v j)
  have hcs := sum_mul_sq_le_sq_mul_sq univ (fun j => |A i j|) (fun j => ‖v j‖)
  have hsq := (sq_le_sq₀ (norm_nonneg _)
    (sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (norm_nonneg _)))).mpr htri
  exact hsq.trans (by simpa only [sq_abs] using hcs)

theorem real_matrix_operator_norm_le (A : Matrix V V ℝ) :
    ‖matrixOperator (fun i j => (A i j : ℂ))‖ ≤ Real.sqrt (matrixFrobeniusSq A) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro v
  have hsum : ‖matrixOperator (fun i j => (A i j : ℂ)) v‖ ^ 2 ≤
      matrixFrobeniusSq A * ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simp only [matrixOperator_apply]
    calc
      _ ≤ ∑ i, (∑ j, (A i j) ^ 2) * ∑ j, ‖v j‖ ^ 2 :=
        sum_le_sum (fun i _ => real_matrix_row_square A (fun j => v j) i)
      _ = _ := by rw [← sum_mul]; rfl
  have hroot := Real.sq_sqrt (matrixFrobeniusSq_nonneg A)
  have hn := norm_nonneg (matrixOperator (fun i j => (A i j : ℂ)) v)
  have hprod : 0 ≤ Real.sqrt (matrixFrobeniusSq A) * ‖v‖ := by positivity
  nlinarith

lemma matrixOperator_mul (A B : Matrix V V ℂ) :
    matrixOperator (A * B) = matrixOperator A * matrixOperator B := by
  ext v i
  change (∑ j, (A * B) i j * v j) =
    ∑ j, A i j * (∑ k, B j k * v k)
  simp only [Matrix.mul_apply]
  simp_rw [sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro k _
  ring

lemma matrixOperator_one : matrixOperator (1 : Matrix V V ℂ) = 1 := by
  ext v i
  change (∑ j, (1 : Matrix V V ℂ) i j * v j) = v i
  simp [Matrix.one_apply]

lemma matrixOperator_pow (A : Matrix V V ℂ) (k : ℕ) :
    matrixOperator (A ^ k) = matrixOperator A ^ k := by
  induction k with
  | zero => simp only [pow_zero, matrixOperator_one]
  | succ k ih => rw [pow_succ, matrixOperator_mul, ih, pow_succ]

def complexifyMatrix (A : Matrix V V ℝ) : Matrix V V ℂ := A.map Complex.ofReal

omit [DecidableEq V] in
lemma real_matrix_cast_mul (A B : Matrix V V ℝ) :
    complexifyMatrix (A * B) = complexifyMatrix A * complexifyMatrix B := by
  ext i j
  change ((∑ x, A i x * B x j : ℝ) : ℂ) = ∑ x, (A i x : ℂ) * (B x j : ℂ)
  simp only [Complex.ofReal_sum, Complex.ofReal_mul]

lemma real_matrix_cast_pow (A : Matrix V V ℝ) (k : ℕ) :
    complexifyMatrix (A ^ k) = complexifyMatrix A ^ k := by
  induction k with
  | zero =>
      ext i j
      change (((1 : Matrix V V ℝ) i j : ℝ) : ℂ) = (1 : Matrix V V ℂ) i j
      simp only [Matrix.one_apply]
      split_ifs <;> simp
  | succ k ih => rw [pow_succ, real_matrix_cast_mul, ih, pow_succ]

/-- The precise moment-to-operator inequality used by spectral transfer. -/
theorem real_matrix_operator_power_norm_le (A : Matrix V V ℝ) (k : ℕ) :
    ‖matrixOperator (fun i j => (A i j : ℂ)) ^ k‖ ≤
      Real.sqrt (matrixFrobeniusSq (A ^ k)) := by
  have hpow := matrixOperator_pow (complexifyMatrix A) k
  have hcast := congrArg matrixOperator (real_matrix_cast_pow A k)
  calc
    _ = ‖matrixOperator (fun i j => ((A ^ k) i j : ℂ))‖ :=
      congrArg norm (hpow.symm.trans hcast.symm)
    _ ≤ _ := real_matrix_operator_norm_le (A ^ k)

end TwoPointCorrelations

end OAI
