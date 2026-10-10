import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI
/-!
# A finite factorial-lift counterexample

The ten labels are the first cell's rows 0, 1, 2 and columns 3, 4, 5,
and the second cell's rows 6, 7 and columns 8, 9. Conditioning on the
first three rows gives a symmetric addition matrix with two distinct
positive eigenvalues. This finite counterexample does not formalize a
randomized approximation algorithm for contingency tables.
-/
noncomputable section

namespace DistinctLifts

abbrev Label := Fin 10
abbrev Remaining := Fin 7

def count (S : Finset Label) (lo hi : ℕ) : ℕ :=
  (S.filter fun i => lo ≤ i.val ∧ i.val < hi).card
/-- The factorial lift for capacities 3 and 2, with constant weight one.
It is defined on all sets here and subsequently restricted to 5-subsets. -/
def factorialLift (S : Finset Label) : ℝ :=
  ((count S 0 3).factorial : ℝ) * (count S 3 6).factorial / (3 : ℕ).factorial *
    (((count S 6 8).factorial : ℝ) * (count S 8 10).factorial / (2 : ℕ).factorial)

def fixed : Finset Label := {0, 1, 2}
def remaining (i : Remaining) : Label := ⟨i.val + 3, by exact Nat.add_lt_add_right i.isLt 3⟩
def conditioned (i j : Remaining) : Finset Label := fixed ∪ {remaining i, remaining j}

theorem conditioned_card (i j : Remaining) (h : i ≠ j) :
    (conditioned i j).card = 5 := by
  exact (by decide : ∀ i j : Remaining, i ≠ j → (conditioned i j).card = 5) i j h

/-- Actual row-conditioned addition matrix, with the required zero diagonal. -/
def additionMatrix : Matrix Remaining Remaining ℝ :=
  fun i j => if i = j then 0 else factorialLift (conditioned i j)
/-- First block: three first-cell columns. Second block: two rows and two
columns of the second cell; same-kind and mixed-kind entries differ. -/
def explicitMatrix : Matrix Remaining Remaining ℝ := fun i j =>
  if i = j then 0 else
  if (i.val < 3 ∧ j.val < 3) ∨
    (3 ≤ i.val ∧ i.val < 5 ∧ 3 ≤ j.val ∧ j.val < 5) ∨
    (5 ≤ i.val ∧ 5 ≤ j.val) then 1 else 1 / 2

theorem additionMatrix_eq : additionMatrix = explicitMatrix := by
  have hcard : ({0, 1, 2} : Finset Label).card = 3 := by decide
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [additionMatrix, explicitMatrix, factorialLift, count,
      conditioned, fixed, remaining, Finset.filter_insert, Finset.filter_singleton,
      Finset.card_insert_of_notMem, Nat.factorial_succ, hcard]

theorem additionMatrix_symmetric : Matrix.IsSymm additionMatrix := by
  rw [additionMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [explicitMatrix, Matrix.transpose_apply]

/-- Both signs use the same three nonzero first coordinates. -/
def eigenvector (s : ℝ) : Remaining → ℝ := fun i => if i.val < 3 then 2 else s

theorem eigenvector_nonzero (s : ℝ) : eigenvector s ≠ 0 := by
  intro h
  have := congrFun h (0 : Remaining)
  norm_num [eigenvector] at this

/-- The calculation retains all four second-block entries separately. -/
theorem eigenvector_equation (s : ℝ) (hs : s ^ 2 = 3) :
    additionMatrix.mulVecLin (eigenvector s) = (2 + s) • eigenvector s := by
  rw [additionMatrix_eq]
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      explicitMatrix, eigenvector] <;> nlinarith

theorem eigenvalue_of_square (s : ℝ) (hs : s ^ 2 = 3) :
    Module.End.HasEigenvalue additionMatrix.mulVecLin (2 + s) := by
  apply Module.End.hasEigenvalue_of_hasEigenvector
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
  exact ⟨eigenvector_equation s hs, eigenvector_nonzero s⟩
/-- A necessary condition for having at most one positive eigenvalue, even
when multiplicities are counted. Two distinct positive native eigenvalues
already contradict this condition, so no inertia convention is required. -/
def PositiveEigenvaluesUnique (A : Matrix Remaining Remaining ℝ) : Prop :=
  ∀ a b : ℝ, 0 < a → 0 < b →
    Module.End.HasEigenvalue A.mulVecLin a → Module.End.HasEigenvalue A.mulVecLin b → a = b

theorem two_distinct_positive_eigenvalues :
    0 < 2 + Real.sqrt 3 ∧ 0 < 2 - Real.sqrt 3 ∧
    2 + Real.sqrt 3 ≠ 2 - Real.sqrt 3 ∧
    Module.End.HasEigenvalue additionMatrix.mulVecLin (2 + Real.sqrt 3) ∧
    Module.End.HasEigenvalue additionMatrix.mulVecLin (2 - Real.sqrt 3) := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  have hp : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  refine ⟨by positivity, by nlinarith, by nlinarith, eigenvalue_of_square _ hs, ?_⟩
  have hm : (-Real.sqrt (3 : ℝ)) ^ 2 = 3 := by nlinarith
  simpa only [sub_eq_add_neg] using eigenvalue_of_square _ hm
/-- The actual conditioned factorial lift fails the necessary spectral
condition in the addition property. No claim about the other lift is made. -/
theorem factorial_lift_fails_addition_signature :
    ¬ PositiveEigenvaluesUnique additionMatrix := by
  obtain ⟨hp, hm, hne, hep, hem⟩ := two_distinct_positive_eigenvalues
  intro h
  exact hne (h _ _ hp hm hep hem)

/-- Vectors constant on the groups of three and four remaining labels. -/
def blockVector (a b : ℝ) : Remaining → ℝ := fun i => if i.val < 3 then a else b

theorem restricted_quadratic (a b : ℝ) :
    dotProduct (blockVector a b) (additionMatrix.mulVec (blockVector a b)) =
      6 * a ^ 2 + 12 * a * b + 8 * b ^ 2 := by
  rw [additionMatrix_eq]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, explicitMatrix, blockVector]
  ring
/-- Full finite counterexample: the conditioned sets have the required size,
the actual factorial-lift matrix is symmetric, and it has two distinct
positive eigenvalues in the native linear-map API. -/
theorem factorial_lift_counterexample :
    (∀ i j : Remaining, i ≠ j → (conditioned i j).card = 5) ∧
    Matrix.IsSymm additionMatrix ∧
    0 < 2 + Real.sqrt 3 ∧ 0 < 2 - Real.sqrt 3 ∧
    2 + Real.sqrt 3 ≠ 2 - Real.sqrt 3 ∧
    Module.End.HasEigenvalue additionMatrix.mulVecLin (2 + Real.sqrt 3) ∧
    Module.End.HasEigenvalue additionMatrix.mulVecLin (2 - Real.sqrt 3) := by
  exact ⟨conditioned_card, additionMatrix_symmetric, two_distinct_positive_eigenvalues⟩

end DistinctLifts

end

end OAI
