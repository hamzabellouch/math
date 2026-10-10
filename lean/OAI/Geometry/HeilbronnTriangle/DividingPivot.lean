import Mathlib

namespace OAI


namespace Problem355.DividingPivot

variable {R : Type*} [CommRing R]

def lowerShear (t : R) : (Matrix (Fin 2) (Fin 2) R)ˣ where
  val := !![1, 0; -t, 1]
  inv := !![1, 0; t, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

def upperShear (s : R) : (Matrix (Fin 2) (Fin 2) R)ˣ where
  val := !![1, -s; 0, 1]
  inv := !![1, s; 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

theorem reduce_dividing_pivot (C : Matrix (Fin 2) (Fin 2) R) (s t : R)
    (hs : C 0 1 = C 0 0 * s) (ht : C 1 0 = t * C 0 0) :
    (lowerShear t : Matrix (Fin 2) (Fin 2) R) * C *
      (upperShear s : Matrix (Fin 2) (Fin 2) R) =
        Matrix.diagonal ![C 0 0, C 1 1 - t * C 0 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerShear, upperShear, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ, hs, ht]
  ring

theorem divides_remaining_pivot (C : Matrix (Fin 2) (Fin 2) R) (t : R)
    (hb : C 0 0 ∣ C 0 1) (hd : C 0 0 ∣ C 1 1) :
    C 0 0 ∣ C 1 1 - t * C 0 1 :=
  dvd_sub hd (dvd_mul_of_dvd_right hb t)

theorem undo_reduction {M : Type*} [Monoid M] (P Q : Mˣ) (C D : M)
    (h : (P : M) * C * (Q : M) = D) :
    C = (P⁻¹ : Mˣ) * D * (Q⁻¹ : Mˣ) := by
  rw [← h]
  simp [← mul_assoc]

theorem exists_dividing_pivot_factorization (C : Matrix (Fin 2) (Fin 2) R)
    (h : ∀ i j, C 0 0 ∣ C i j) :
    ∃ (d : R) (P Q : (Matrix (Fin 2) (Fin 2) R)ˣ),
      C 0 0 ∣ d ∧
      C = (P : Matrix (Fin 2) (Fin 2) R) * Matrix.diagonal ![C 0 0, d] *
        (Q : Matrix (Fin 2) (Fin 2) R) := by
  obtain ⟨s, hs⟩ := h 0 1
  obtain ⟨t, ht⟩ := h 1 0
  refine ⟨C 1 1 - t * C 0 1, (lowerShear t)⁻¹, (upperShear s)⁻¹,
    divides_remaining_pivot C t (h 0 1) (h 1 1), ?_⟩
  exact undo_reduction _ _ _ _
    (reduce_dividing_pivot C s t hs (by simpa [mul_comm] using ht))

end Problem355.DividingPivot

end OAI
