import Mathlib.Data.Matrix.Mul
import OAI.Analysis.Laughlin.Spin.Highest2

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

noncomputable def raiseMatrix (A : ℕ) : Matrix (Fin (A+1)) (Fin (A+1)) ℝ :=
  fun i j => if i.val+1=j.val then ladder A i.val else 0

theorem raiseMatrix_row (A : ℕ) (i : Fin (A+1)) (f : Fin (A+1) → ℝ) :
    (∑ j, raiseMatrix A i j*f j) =
      if hi : i.val < A then ladder A i.val*f ⟨i.val+1,by omega⟩ else 0 := by
  by_cases hi : i.val < A
  · rw [dite_eq_left hi]
    let next : Fin (A+1) := ⟨i.val+1,by omega⟩
    have he (j : Fin (A+1)) : i.val+1=j.val ↔ next=j := by
      constructor
      · intro h; exact Fin.ext h
      · intro h; exact congrArg Fin.val h
    simp only [raiseMatrix,he,ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    rfl
  · rw [dite_eq_right hi]
    apply Finset.sum_eq_zero
    intro j hj
    have hn : i.val+1 ≠ j.val := by omega
    simp [raiseMatrix,hn]

theorem raiseMatrix_column (A : ℕ) (j : Fin (A+1)) (f : Fin (A+1) → ℝ) :
    (∑ i, f i*raiseMatrix A i j) =
      if hj : 0 < j.val then f ⟨j.val-1,by omega⟩*ladder A (j.val-1) else 0 := by
  by_cases hj : 0 < j.val
  · rw [dite_eq_left hj]
    let prev : Fin (A+1) := ⟨j.val-1,by omega⟩
    rw [Finset.sum_eq_single prev]
    · simp [raiseMatrix,prev,show j.val-1+1=j.val by omega]
    · intro i hi hn
      have hne : i.val+1 ≠ j.val := by
        intro h; apply hn; apply Fin.ext; dsimp [prev]; omega
      simp [raiseMatrix,hne]
    · simp
  · rw [dite_eq_right hj]
    apply Finset.sum_eq_zero
    intro i hi
    have hn : i.val+1 ≠ j.val := by omega
    simp [raiseMatrix,hn]

noncomputable def totalRaise (A B : ℕ) :
    Matrix (Fin (A+1) × Fin (B+1)) (Fin (A+1) × Fin (B+1)) ℝ := fun i j =>
  raiseMatrix A i.1 j.1 * (if i.2=j.2 then 1 else 0) +
    (if i.1=j.1 then 1 else 0)*raiseMatrix B i.2 j.2

theorem totalRaise_apply (A B : ℕ) (f : Fin (A+1) × Fin (B+1) → ℝ)
    (i : Fin (A+1) × Fin (B+1)) :
    (∑ j, totalRaise A B i j*f j) =
      (∑ x, raiseMatrix A i.1 x*f (x,i.2)) +
      (∑ y, raiseMatrix B i.2 y*f (i.1,y)) := by
  rw [Fintype.sum_prod_type]
  simp only [totalRaise,add_mul,Finset.sum_add_distrib]
  congr 1
  · simp only [mul_ite,mul_one,mul_zero,ite_mul,zero_mul,Finset.sum_ite_eq,
      Finset.mem_univ,ite_true]
  · rw [Finset.sum_comm]
    simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]

theorem totalRaise_transpose_apply (A B : ℕ) (f : Fin (A+1) × Fin (B+1) → ℝ)
    (i : Fin (A+1) × Fin (B+1)) :
    (∑ j, totalRaise A B j i*f j) =
      (∑ x, f (x,i.2)*raiseMatrix A x i.1) +
      (∑ y, f (i.1,y)*raiseMatrix B y i.2) := by
  rw [Fintype.sum_prod_type]
  simp only [totalRaise,add_mul,Finset.sum_add_distrib]
  congr 1
  · simp only [mul_ite,mul_one,mul_zero,ite_mul,zero_mul,Finset.sum_ite_eq',
      Finset.mem_univ,ite_true]
    apply Finset.sum_congr rfl
    intro x hx; ring
  · rw [Finset.sum_comm]
    simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    apply Finset.sum_congr rfl
    intro y hy; ring

end Laughlin.Spin

end OAI
