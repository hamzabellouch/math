import Mathlib
import OAI.Combinatorics.MatchingPSD.PSDEvaluation

namespace OAI

namespace AffinePSD
open Matrix Finset
open scoped BigOperators
variable {I R : Type*} [Fintype I] [Fintype R] [DecidableEq R]

lemma zero_col_of_diag_zero {A : Matrix R R ℝ} (hA : A.PosSemidef)
    (i : R) (hi : A i i = 0) (j : R) : A j i = 0 := by
  have h := (hA.dotProduct_mulVec_zero_iff (x := Pi.single i 1)).mp (by simpa using hi)
  simpa using congrFun h j

lemma zero_row_of_diag_zero {A : Matrix R R ℝ} (hA : A.PosSemidef)
    (i : R) (hi : A i i = 0) (j : R) : A i j = 0 := by
  have hs : A i j = A j i := by
    simpa using congrArg (fun M : Matrix R R ℝ => M j i) hA.isHermitian.eq
  rw [hs]
  exact zero_col_of_diag_zero hA i hi j

lemma diagonal_compression (B : I → Matrix R R ℝ) (hB : ∀ i, (B i).PosSemidef)
    (d : R → ℝ) (hs : ∑ i, B i = diagonal d) (A : Matrix R R ℝ)
    (hA : A.PosSemidef) :
    ∃ A' : Matrix R R ℝ, A'.PosSemidef ∧ evaluation B A' = evaluation B A ∧
      (∀ j, d j = 0 → A' j j = 0) := by
  classical
  let p : R → ℝ := fun j => if d j = 0 then 0 else 1
  let P := diagonal p
  have hdiag (i : I) (j : R) (hj : d j = 0) : B i j j = 0 := by
    have hle : B i j j ≤ ∑ k, B k j j :=
      Finset.single_le_sum (fun k _ => (hB k).diag_nonneg) (Finset.mem_univ i)
    have he : ∑ k, B k j j = d j := by
      simpa only [Matrix.sum_apply, Matrix.diagonal_apply_eq] using
        congrArg (fun M : Matrix R R ℝ => M j j) hs
    have hn := (hB i).diag_nonneg (i := j)
    rw [he, hj] at hle
    exact le_antisymm hle hn
  have hpB (i : I) : P * B i = B i := by
    ext j k
    simp only [P, Matrix.diagonal_mul, p]
    split_ifs with hj
    · simp [zero_row_of_diag_zero (hB i) j (hdiag i j hj) k]
    · simp
  have hBp (i : I) : B i * P = B i := by
    ext j k
    simp only [P, Matrix.mul_diagonal, p]
    split_ifs with hk
    · simp [zero_col_of_diag_zero (hB i) k (hdiag i k hk) j]
    · simp
  refine ⟨P * A * P, ?_, ?_, ?_⟩
  · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, P, Matrix.diagonal_transpose]
      using hA.conjTranspose_mul_mul_same P
  · ext i
    change (P * A * P * B i).trace = (A * B i).trace
    rw [Matrix.mul_assoc P A P, Matrix.mul_assoc P (A * P) (B i),
      Matrix.trace_mul_comm P, Matrix.mul_assoc A P (B i), hpB,
      Matrix.mul_assoc A (B i) P, hBp]
  · intro j hj
    simp [P, Matrix.mul_diagonal, Matrix.diagonal_mul, p, hj]

omit [Fintype R] in
lemma sum_diagonal_nonneg (B : I → Matrix R R ℝ) (hB : ∀ i, (B i).PosSemidef)
    (d : R → ℝ) (hs : ∑ i, B i = diagonal d) : ∀ j, 0 ≤ d j := by
  intro j
  have he : ∑ i, B i j j = d j := by
    simpa only [Matrix.sum_apply, Matrix.diagonal_apply_eq] using
      congrArg (fun M : Matrix R R ℝ => M j j) hs
  rw [← he]
  exact Finset.sum_nonneg (fun i _ => (hB i).diag_nonneg)

lemma evaluation_sum_eq (B : I → Matrix R R ℝ) (d : R → ℝ)
    (hs : ∑ i, B i = diagonal d) (A : Matrix R R ℝ) :
    ∑ i, evaluation B A i = ∑ j, A j j * d j := by
  simp only [evaluation_apply]
  rw [← Matrix.trace_sum, ← Matrix.mul_sum, hs]
  simp [Matrix.trace, Matrix.diag, Matrix.mul_diagonal]

lemma diagonal_trace_bound (B : I → Matrix R R ℝ) (hB : ∀ i, (B i).PosSemidef)
    (d : R → ℝ) (hs : ∑ i, B i = diagonal d) (A : Matrix R R ℝ)
    (hA : A.PosSemidef) (hz : ∀ j, d j = 0 → A j j = 0) :
    A.trace ≤ (∑ j, (d j)⁻¹) * ∑ i, evaluation B A i := by
  have hd := sum_diagonal_nonneg B hB d hs
  have he := evaluation_sum_eq B d hs A
  rw [he]
  change (∑ j, A j j) ≤ _
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : d j = 0
  · simp [hj, hz j hj]
  · have hp : 0 < d j := lt_of_le_of_ne (hd j) (Ne.symm hj)
    have hle : A j j * d j ≤ ∑ k, A k k * d k :=
      Finset.single_le_sum (fun k _ => mul_nonneg (hA.diag_nonneg (i := k)) (hd k)) (Finset.mem_univ j)
    calc
      A j j = (d j)⁻¹ * (A j j * d j) := by field_simp
      _ ≤ (d j)⁻¹ * ∑ k, A k k * d k := mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hp.le)

end AffinePSD

end OAI
