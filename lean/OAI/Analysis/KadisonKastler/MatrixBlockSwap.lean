import OAI.Analysis.FactorGeneration.MatrixUnits
import Mathlib.Algebra.Group.End
import Mathlib.Logic.Equiv.Prod

namespace OAI

/-! # Finite permutations and block swaps of matrix units

These unitaries are finite sums of the given matrix units. No trace,
infinite tensor product, or existence premise is involved.
-/

namespace KadisonKastler

open Generator
open scoped BigOperators

noncomputable section

variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
  [Ring A] [StarRing A] [_root_.Algebra ℂ A]

/-- The permutation matrix in an actual system of matrix units. -/
def matrixPermutationValue (E : MatrixUnitSystem ι A) (e : Equiv.Perm ι) : A :=
  ∑ i, E.entry (e i) i

theorem matrixPermutationValue_mul_entry (E : MatrixUnitSystem ι A)
    (e : Equiv.Perm ι) (i j : ι) :
    matrixPermutationValue E e * E.entry i j = E.entry (e i) j := by
  rw [matrixPermutationValue, Finset.sum_mul, Finset.sum_eq_single i]
  · simp only [E.mul_entry, ite_true]
  · intro k _ hki
    rw [E.mul_entry, ite_eq_right hki]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

theorem matrixPermutationValue_mul (E : MatrixUnitSystem ι A)
    (e f : Equiv.Perm ι) :
    matrixPermutationValue E e * matrixPermutationValue E f =
      matrixPermutationValue E (e * f) := by
  change matrixPermutationValue E e * (∑ i, E.entry (f i) i) = _
  rw [Finset.mul_sum]
  simp only [matrixPermutationValue_mul_entry]
  rfl

@[simp] theorem matrixPermutationValue_one (E : MatrixUnitSystem ι A) :
    matrixPermutationValue E 1 = 1 := E.total

theorem matrixPermutationValue_star (E : MatrixUnitSystem ι A)
    (e : Equiv.Perm ι) :
    star (matrixPermutationValue E e) = matrixPermutationValue E e.symm := by
  rw [matrixPermutationValue, star_sum]
  simp only [E.star_entry]
  simpa only [matrixPermutationValue, Equiv.symm_apply_apply] using
    (Equiv.sum_comp (e : ι ≃ ι) (fun j => E.entry (e.symm j) j))

/-- The finite permutation sum is an actual unitary. -/
def matrixPermutationUnitary (E : MatrixUnitSystem ι A) (e : Equiv.Perm ι) : unitary A :=
  ⟨matrixPermutationValue E e, by
    constructor <;> rw [matrixPermutationValue_star, matrixPermutationValue_mul]
    · simpa only [← Equiv.Perm.inv_def, inv_mul_cancel] using matrixPermutationValue_one E
    · simpa only [← Equiv.Perm.inv_def, mul_inv_cancel] using matrixPermutationValue_one E⟩

theorem matrixPermutationUnitary_conjugate_entry (E : MatrixUnitSystem ι A)
    (e : Equiv.Perm ι) (i j : ι) :
    (matrixPermutationUnitary E e : A) * E.entry i j *
      star (matrixPermutationUnitary E e : A) = E.entry (e i) (e j) := by
  change matrixPermutationValue E e * E.entry i j * star (matrixPermutationValue E e) = _
  rw [matrixPermutationValue_mul_entry, matrixPermutationValue_star, matrixPermutationValue,
    Finset.mul_sum, Finset.sum_eq_single (e j)]
  · simp only [Equiv.symm_apply_apply, E.mul_entry, ite_true]
  · intro k _ hkj
    rw [E.mul_entry, ite_eq_right]
    exact fun h => hkj (by simpa only [Equiv.apply_symm_apply] using congrArg e h.symm)
  · intro hj
    exact False.elim (hj (Finset.mem_univ (e j)))

/-- The unitary exchanging two equal finite tensor blocks. -/
def finiteMatrixBlockSwap (E : MatrixUnitSystem (ι × ι) A) : unitary A :=
  matrixPermutationUnitary E (Equiv.prodComm ι ι)

theorem finiteMatrixBlockSwap_value (E : MatrixUnitSystem (ι × ι) A) :
    (finiteMatrixBlockSwap E : A) = ∑ i, ∑ j, E.entry (i, j) (j, i) := by
  change matrixPermutationValue E (Equiv.prodComm ι ι) = _
  simp only [matrixPermutationValue, Fintype.sum_prod_type, Equiv.prodComm_apply]
  exact Finset.sum_comm

/-- Block swapping exchanges the two indices on each side. -/
theorem finiteMatrixBlockSwap_conjugate_entry (E : MatrixUnitSystem (ι × ι) A)
    (i j k l : ι) :
    (finiteMatrixBlockSwap E : A) * E.entry (i, j) (k, l) * star (finiteMatrixBlockSwap E : A) =
      E.entry (j, i) (l, k) :=
  matrixPermutationUnitary_conjugate_entry E (Equiv.prodComm ι ι) (i, j) (k, l)

/-- The swap belongs to the same finite matrix algebra. -/
theorem finiteMatrixBlockSwap_mem [StarModule ℂ A] (E : MatrixUnitSystem (ι × ι) A) :
    (finiteMatrixBlockSwap E : A) ∈ E.algebra := by
  rw [finiteMatrixBlockSwap_value]
  exact E.algebra.sum_mem fun i _ => E.algebra.sum_mem fun j _ => E.entry_mem _ _

end

end KadisonKastler

end OAI
