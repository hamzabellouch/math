import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.BigOperators

namespace OAI

noncomputable section

namespace NCHitting

open Matrix Finset Polynomial

variable {R : Type*} [CommRing R]
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]

theorem det_rectangular_mul (A : Matrix I J R) (B : Matrix J I R) :
    (A * B).det = ∑ f : I → J, (A.submatrix id f).det * ∏ i, B (f i) i := by
  classical
  calc
    (A * B).det = ∑ f : I → J, ∑ σ : Equiv.Perm I,
        (Equiv.Perm.sign σ : R) * ∏ i, A (σ i) (f i) * B (f i) i := by
      simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum,
        Finset.mul_sum, Fintype.piFinset_univ]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro f _
      simp only [Matrix.det_apply', Matrix.submatrix_apply, id_eq,
        Finset.prod_mul_distrib, Finset.sum_mul, mul_assoc]

theorem dvd_det_rectangular_mul (A : Matrix I J R) (B : Matrix J I R)
    (p : R) (h : ∀ f : I → J, p ∣ (A.submatrix id f).det) :
    p ∣ (A * B).det := by
  rw [det_rectangular_mul]
  exact Finset.dvd_sum (fun f _ => dvd_mul_of_dvd_left (h f) _)

theorem exists_minor_ne_zero_of_mul_det_ne_zero (A : Matrix I J R)
    (B : Matrix J I R) (h : (A * B).det ≠ 0) :
    ∃ f : I → J, (A.submatrix id f).det ≠ 0 := by
  classical
  by_contra hn
  push Not at hn
  apply h
  simp [det_rectangular_mul, hn]

theorem dvd_det_of_column_dvd (A : Matrix I I R) (c : I) (p : R)
    (h : ∀ i, p ∣ A i c) : p ∣ A.det := by
  classical
  rw [Matrix.det_apply']
  apply Finset.dvd_sum
  intro σ _
  apply dvd_mul_of_dvd_right
  exact (h (σ c)).trans (Finset.dvd_prod_of_mem (fun i => A (σ i) i) (Finset.mem_univ c))

theorem natDegree_det_le_sum {F : Type*} [Field F]
    (A : Matrix I I F[X]) (d : I → ℕ)
    (h : ∀ i j, (A i j).natDegree ≤ d i) :
    A.det.natDegree ≤ ∑ i, d i := by
  classical
  rw [Matrix.det_apply']
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ _
  apply (Polynomial.natDegree_mul_le).trans
  have hsign : (↑(Equiv.Perm.sign σ) : F[X]).natDegree = 0 := by
    exact Polynomial.natDegree_intCast _
  rw [hsign, zero_add]
  calc
    (∏ i, A (σ i) i).natDegree ≤ ∑ i, d (σ i) :=
      (Polynomial.natDegree_prod_le Finset.univ (fun i => A (σ i) i)).trans (Finset.sum_le_sum (fun i _ => h (σ i) i))
    _ = ∑ i, d i := Equiv.sum_comp σ d

end NCHitting

end

end OAI
