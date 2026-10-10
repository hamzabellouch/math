import OAI.Analysis.Laughlin.Spin.LadderMatrix

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

noncomputable def weightMatrix (A : ℕ) : Matrix (Fin (A+1)) (Fin (A+1)) ℝ :=
  Matrix.diagonal (fun i => (A : ℝ)-2*i.val)

theorem raise_mul_transpose_entry (A : ℕ) (i j : Fin (A+1)) :
    (raiseMatrix A * (raiseMatrix A)ᵀ) i j =
      if i=j then ((i.val : ℝ)+1)*(A-i.val : ℕ) else 0 := by
  change (∑ k, raiseMatrix A i k*raiseMatrix A j k) = _
  rw [raiseMatrix_row]
  by_cases hi : i.val < A
  · rw [dite_eq_left hi]
    by_cases hij : i=j
    · subst j
      simp only [raiseMatrix,ite_true]
      unfold ladder
      rw [Real.mul_self_sqrt (by positivity)]
    · have hne : j.val+1 ≠ i.val+1 := by intro h; apply hij; apply Fin.ext; omega
      simp only [raiseMatrix,ite_eq_right hne,ite_eq_right hij,mul_zero]
  · rw [dite_eq_right hi]
    have hz : i.val=A := by omega
    simp [hz]

theorem transpose_mul_raise_entry (A : ℕ) (i j : Fin (A+1)) :
    ((raiseMatrix A)ᵀ * raiseMatrix A) i j =
      if i=j then (i.val : ℝ)*((A : ℝ)-i.val+1) else 0 := by
  change (∑ k, raiseMatrix A k i*raiseMatrix A k j) = _
  have he : (∑ k, raiseMatrix A k i*raiseMatrix A k j) =
      ∑ k, raiseMatrix A k j*raiseMatrix A k i := by
    apply Finset.sum_congr rfl; intro k hk; ring
  rw [he,raiseMatrix_column]
  by_cases hi : 0 < i.val
  · rw [dite_eq_left hi]
    by_cases hij : i=j
    · subst j
      simp only [raiseMatrix,ite_eq_left (show i.val-1+1=i.val by omega),ite_true]
      unfold ladder
      rw [Real.mul_self_sqrt (by positivity)]
      rw [Nat.cast_sub (by omega : i.val-1 ≤ A),Nat.cast_sub (by omega : 1 ≤ i.val)]
      push_cast; ring
    · have hne : i.val-1+1 ≠ j.val := by intro h; apply hij; apply Fin.ext; omega
      simp only [raiseMatrix,ite_eq_right hne,ite_eq_right hij,zero_mul]
  · rw [dite_eq_right hi]
    have hz : i.val=0 := by omega
    simp [hz]

theorem raise_lower_commutator (A : ℕ) :
    raiseMatrix A * (raiseMatrix A)ᵀ - (raiseMatrix A)ᵀ * raiseMatrix A = weightMatrix A := by
  ext i j
  rw [Matrix.sub_apply,raise_mul_transpose_entry,transpose_mul_raise_entry]
  by_cases hij : i=j
  · subst j
    simp only [ite_true,weightMatrix,Matrix.diagonal_apply_eq]
    rw [Nat.cast_sub (by omega : i.val ≤ A)]
    ring
  · simp [hij,weightMatrix]

theorem weight_lower_commutator (A : ℕ) :
    weightMatrix A * (raiseMatrix A)ᵀ =
      (raiseMatrix A)ᵀ * weightMatrix A - (2 : ℝ) • (raiseMatrix A)ᵀ := by
  ext i j
  simp only [weightMatrix,Matrix.diagonal_mul,Matrix.mul_diagonal,Matrix.sub_apply,
    Matrix.smul_apply,Matrix.transpose_apply,smul_eq_mul,raiseMatrix]
  by_cases h : j.val+1=i.val
  · rw [ite_eq_left h]
    have hc : (j.val : ℝ)+1=i.val := by exact_mod_cast h
    linear_combination 2*ladder A j.val*hc
  · rw [ite_eq_right h]; ring

end Laughlin.Spin

end OAI
