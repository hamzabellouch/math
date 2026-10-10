import Mathlib

namespace OAI

namespace Problem355.TwoByTwoPivot
variable {R : Type*} [CommRing R]
def swapUnit : (Matrix (Fin 2) (Fin 2) R)ˣ where
  val := !![0, 1; 1, 0]
  inv := !![0, 1; 1, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
def pivotUnit (i : Fin 2) : (Matrix (Fin 2) (Fin 2) R)ˣ :=
  if i = 0 then 1 else swapUnit
theorem pivotUnit_mul_apply (A : Matrix (Fin 2) (Fin 2) R) (i a b : Fin 2) :
    ((pivotUnit (R := R) i : Matrix (Fin 2) (Fin 2) R) * A) a b =
      A (Equiv.swap 0 i a) b := by
  fin_cases i <;> fin_cases a <;>
    simp [pivotUnit, swapUnit, Matrix.mul_apply, Fin.sum_univ_two]
theorem mul_pivotUnit_apply (A : Matrix (Fin 2) (Fin 2) R) (j a b : Fin 2) :
    (A * (pivotUnit (R := R) j : Matrix (Fin 2) (Fin 2) R)) a b =
      A a (Equiv.swap 0 j b) := by
  fin_cases j <;> fin_cases b <;>
    simp [pivotUnit, swapUnit, Matrix.mul_apply, Fin.sum_univ_two]
theorem move_pivot_apply (A : Matrix (Fin 2) (Fin 2) R) (i j a b : Fin 2) :
    ((pivotUnit (R := R) i : Matrix (Fin 2) (Fin 2) R) * A *
      (pivotUnit (R := R) j : Matrix (Fin 2) (Fin 2) R)) a b =
      A (Equiv.swap 0 i a) (Equiv.swap 0 j b) := by
  rw [mul_pivotUnit_apply, pivotUnit_mul_apply]
theorem move_dividing_entry (A : Matrix (Fin 2) (Fin 2) R) (i j : Fin 2)
    (h : ∀ a b, A i j ∣ A a b) :
    ∃ P Q : (Matrix (Fin 2) (Fin 2) R)ˣ,
      ((P : Matrix (Fin 2) (Fin 2) R) * A * Q) 0 0 = A i j ∧
      ∀ a b, ((P : Matrix (Fin 2) (Fin 2) R) * A * Q) 0 0 ∣
        ((P : Matrix (Fin 2) (Fin 2) R) * A * Q) a b := by
  refine ⟨pivotUnit i, pivotUnit j, ?_, ?_⟩
  · simp only [move_pivot_apply, Equiv.swap_apply_left]
  · intro a b
    simpa only [move_pivot_apply, Equiv.swap_apply_left] using
      h (Equiv.swap 0 i a) (Equiv.swap 0 j b)
end Problem355.TwoByTwoPivot

end OAI
