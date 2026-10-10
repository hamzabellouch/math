import OAI.Analysis.FreeEntropy.MatrixParseval

namespace OAI

universe u1

noncomputable section
open scoped ComplexConjugate
open Finset
namespace FiniteEntropySeparation
 def matrixOperator {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d) :=
  (Matrix.toEuclideanLin A).toContinuousLinearMap
 theorem matrixOperator_mul {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ) :
    matrixOperator (A*B) = matrixOperator A*matrixOperator B := by
  ext x j
  simp [matrixOperator, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
 theorem matrixOperator_one {d : ℕ} : matrixOperator (1 : Matrix (Fin d) (Fin d) ℂ) = 1 := by
  ext x j
  simp [matrixOperator]
 theorem matrixOperator_add {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ) :
    matrixOperator (A+B) = matrixOperator A+matrixOperator B := by
  ext x j
  simp [matrixOperator, Matrix.toLpLin_apply]
 theorem matrixOperator_smul {d : ℕ} (c : ℂ) (A : Matrix (Fin d) (Fin d) ℂ) :
    matrixOperator (c • A) = c • matrixOperator A := by
  ext x j
  simp [matrixOperator, Matrix.toLpLin_apply]
 theorem matrixOpNorm_nonneg {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : 0 ≤ matrixOpNorm A := norm_nonneg _
 theorem matrixOpNorm_mul {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ) :
    matrixOpNorm (A*B) ≤ matrixOpNorm A*matrixOpNorm B := by
  change ‖matrixOperator (A*B)‖ ≤ ‖matrixOperator A‖*‖matrixOperator B‖
  rw [matrixOperator_mul]
  exact norm_mul_le _ _
 theorem matrixOpNorm_one {d : ℕ} : matrixOpNorm (1 : Matrix (Fin d) (Fin d) ℂ) ≤ 1 := by
  change ‖matrixOperator (1 : Matrix (Fin d) (Fin d) ℂ)‖ ≤ 1
  rw [matrixOperator_one]
  exact ContinuousLinearMap.norm_id_le
 theorem matrixOpNorm_add {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ) :
    matrixOpNorm (A+B) ≤ matrixOpNorm A+matrixOpNorm B := by
  change ‖matrixOperator (A+B)‖ ≤ ‖matrixOperator A‖+‖matrixOperator B‖
  rw [matrixOperator_add]
  exact norm_add_le _ _
 theorem matrixOpNorm_smul {d : ℕ} (c : ℂ) (A : Matrix (Fin d) (Fin d) ℂ) :
    matrixOpNorm (c • A) = ‖c‖*matrixOpNorm A := by
  change ‖matrixOperator (c • A)‖ = ‖c‖*‖matrixOperator A‖
  rw [matrixOperator_smul, norm_smul]
 theorem matrixOpNorm_prod {d : ℕ} (L : List (Matrix (Fin d) (Fin d) ℂ)) :
    matrixOpNorm L.prod ≤ (L.map matrixOpNorm).prod := by
  induction L with
  | nil => exact matrixOpNorm_one
  | cons A L ih =>
    simpa only [List.prod_cons, List.map_cons] using (matrixOpNorm_mul A L.prod).trans
      (mul_le_mul_of_nonneg_left ih (matrixOpNorm_nonneg A))
 theorem matrixOpNorm_word {ι : Type u1} {d : ℕ} (A : ι → Matrix (Fin d) (Fin d) ℂ) (w : List ι)
    {K : ℝ} (hK : 0 ≤ K) (hA : ∀ i ∈ w, matrixOpNorm (A i) ≤ K) :
    matrixOpNorm (w.map A).prod ≤ K^w.length := by
  induction w with
  | nil => simpa using (matrixOpNorm_one (d := d))
  | cons i w ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
    rw [mul_comm (K^w.length) K]
    exact (matrixOpNorm_mul _ _).trans (mul_le_mul (hA i (by simp))
      (ih (fun j hj => hA j (by simp [hj]))) (matrixOpNorm_nonneg _) hK)
 theorem matrix_entry_bound {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (j k : Fin d) :
    ‖A j k‖ ≤ matrixOpNorm A := by
  have h := matrix_column_bound A k
  have hs := single_le_sum (fun i (_ : i ∈ (univ : Finset (Fin d))) => Complex.normSq_nonneg (A i k)) (mem_univ j)
  rw [Complex.normSq_eq_norm_sq] at hs
  have hn := (norm_nonneg (A j k))
  have hN := matrixOpNorm_nonneg A
  nlinarith
 theorem matrix_trace_bound {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    ‖Matrix.trace A‖ ≤ (d:ℝ)*matrixOpNorm A := by
  calc
    _ ≤ ∑ j, ‖A j j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin d, matrixOpNorm A := sum_le_sum (fun j _ => matrix_entry_bound A j j)
    _ = _ := by simp
 theorem matrix_normalized_trace_bound {d : ℕ} (hd : 0 < d) (A : Matrix (Fin d) (Fin d) ℂ) :
    ‖(d:ℂ)⁻¹*Matrix.trace A‖ ≤ matrixOpNorm A := by
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have h := matrix_trace_bound A
  calc
    (d:ℝ)⁻¹*‖Matrix.trace A‖ ≤ (d:ℝ)⁻¹*((d:ℝ)*matrixOpNorm A) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hd.ne'), one_mul]
end FiniteEntropySeparation

end

end OAI
