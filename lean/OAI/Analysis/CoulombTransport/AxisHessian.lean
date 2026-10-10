import Mathlib

namespace OAI

/-! Explicit nondegeneracy algebra for the two local Coulomb branches.
The Hessian eigenvalues are 2 in the axial direction and -1 transversely.
A common regularization parameter K = 20 works in every direction. -/

noncomputable section

namespace Problem356.LocalHessian

open Matrix

/-- Eigenvalue of the inverse-distance Hessian at a unit coordinate vector. -/
def eigenvalue (k i : Fin 3) : ℝ := if i = k then 2 else -1

/-- The inverse-distance Hessian at either chosen unit coordinate vector. -/
def pairHessian (k : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  diagonal (eigenvalue k)

/-- First derivative of the central stationary branch for K = 20. -/
def centralDerivative (k : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  diagonal fun i => if i = k then 9 / 106 else -15 / 271

/-- First derivative of the opposite stationary branch for K = 20. -/
def oppositeDerivative (k : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  diagonal fun i => if i = k then 1 / 53 else -1 / 271

/-- Upper diagonal block of the regularized Hessian. -/
def upperBlock (k : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  diagonal fun i => 20 + 2 * eigenvalue k i

/-- Lower diagonal block of the regularized Hessian. -/
def lowerBlock (k : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  diagonal fun i => 20 + (9 / 8) * eigenvalue k i

/-- Mixed block of the regularized Hessian. -/
def mixedBlock (k : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  diagonal fun i => -eigenvalue k i

/-- The full six-dimensional regularized Hessian. -/
def regularizedHessian (k : Fin 3) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
  fromBlocks (upperBlock k) (mixedBlock k) (mixedBlock k) (lowerBlock k)

lemma eigenvalue_cases (k i : Fin 3) :
    eigenvalue k i = 2 ∨ eigenvalue k i = -1 := by
  unfold eigenvalue
  split_ifs <;> simp

lemma scalar_quadratic_coercive {q x z : ℝ}
    (hq : q = 2 ∨ q = -1) :
    16 * (x ^ 2 + z ^ 2) ≤
      (20 + 2 * q) * x ^ 2 - 2 * q * x * z +
        (20 + (9 / 8) * q) * z ^ 2 := by
  rcases hq with rfl | rfl
  · nlinarith [sq_nonneg (x - z), sq_nonneg x, sq_nonneg z]
  · nlinarith [sq_nonneg (x + z), sq_nonneg x, sq_nonneg z]

lemma scalar_quadratic_positive {q x z : ℝ}
    (hq : q = 2 ∨ q = -1) (hxz : x ≠ 0 ∨ z ≠ 0) :
    0 < (20 + 2 * q) * x ^ 2 - 2 * q * x * z +
      (20 + (9 / 8) * q) * z ^ 2 := by
  have hsum : 0 < x ^ 2 + z ^ 2 := by
    rcases hxz with hx | hz
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hx) (sq_nonneg z)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg x) (sq_pos_of_ne_zero hz)
  rcases hq with rfl | rfl
  · nlinarith [sq_nonneg (x - z), sq_nonneg x, sq_nonneg z]
  · nlinarith [sq_nonneg (x + z), sq_nonneg x, sq_nonneg z]

lemma scalar_quadratic_nonnegative {q x z : ℝ}
    (hq : q = 2 ∨ q = -1) :
    0 ≤ (20 + 2 * q) * x ^ 2 - 2 * q * x * z +
      (20 + (9 / 8) * q) * z ^ 2 := by
  by_cases hx : x = 0
  · by_cases hz : z = 0
    · simp [hx, hz]
    · exact (scalar_quadratic_positive hq (Or.inr hz)).le
  · exact (scalar_quadratic_positive hq (Or.inl hx)).le

lemma centralDerivative_isUnit (k : Fin 3) : IsUnit (centralDerivative k) := by
  rw [centralDerivative, Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal]
  apply isUnit_iff_ne_zero.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  split_ifs <;> norm_num

lemma oppositeDerivative_isUnit (k : Fin 3) : IsUnit (oppositeDerivative k) := by
  rw [oppositeDerivative, Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal]
  apply isUnit_iff_ne_zero.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  split_ifs <;> norm_num

lemma central_stationary_equation (k : Fin 3) :
    upperBlock k * centralDerivative k + mixedBlock k * oppositeDerivative k =
      pairHessian k := by
  simp only [upperBlock, centralDerivative, mixedBlock, oppositeDerivative,
    pairHessian, diagonal_mul_diagonal, diagonal_add]
  congr 1
  funext i
  unfold eigenvalue
  split_ifs <;> norm_num

lemma opposite_stationary_equation (k : Fin 3) :
    mixedBlock k * centralDerivative k + lowerBlock k * oppositeDerivative k =
      diagonal (fun i => (eigenvalue k i) / 8) := by
  simp only [mixedBlock, centralDerivative, lowerBlock, oppositeDerivative,
    diagonal_mul_diagonal, diagonal_add]
  congr 1
  funext i
  unfold eigenvalue
  split_ifs <;> norm_num

lemma regularizedHessian_quadratic (k : Fin 3) (v : Fin 3 ⊕ Fin 3 → ℝ) :
    star v ⬝ᵥ ((regularizedHessian k) *ᵥ v) =
      ∑ i : Fin 3, ((20 + 2 * eigenvalue k i) * v (Sum.inl i) ^ 2 -
        2 * eigenvalue k i * v (Sum.inl i) * v (Sum.inr i) +
        (20 + (9 / 8) * eigenvalue k i) * v (Sum.inr i) ^ 2) := by
  simp only [regularizedHessian, fromBlocks_mulVec, dotProduct,
    Fintype.sum_sum_type, Pi.star_apply, star_trivial, Sum.elim_inl,
    Sum.elim_inr, Pi.add_apply, upperBlock, lowerBlock, mixedBlock,
    mulVec_diagonal, Function.comp_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma regularizedHessian_isHermitian (k : Fin 3) :
    (regularizedHessian k).IsHermitian := by
  apply Matrix.IsHermitian.fromBlocks
  · exact Matrix.isHermitian_diagonal _
  · exact Matrix.isHermitian_diagonal _
  · exact Matrix.isHermitian_diagonal _

lemma regularizedHessian_posDef (k : Fin 3) :
    (regularizedHessian k).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (regularizedHessian_isHermitian k)
  intro v hv
  rw [regularizedHessian_quadratic]
  apply Finset.sum_pos'
  · intro i hi
    exact scalar_quadratic_nonnegative (eigenvalue_cases k i)
  · have hex : ∃ j, v j ≠ 0 := by
      contrapose! hv
      ext j
      exact hv j
    obtain ⟨j, hj⟩ := hex
    cases j with
    | inl i =>
      exact ⟨i, Finset.mem_univ _,
        scalar_quadratic_positive (eigenvalue_cases k i) (Or.inl hj)⟩
    | inr i =>
      exact ⟨i, Finset.mem_univ _,
        scalar_quadratic_positive (eigenvalue_cases k i) (Or.inr hj)⟩

lemma regularizedHessian_isUnit (k : Fin 3) : IsUnit (regularizedHessian k) :=
  (regularizedHessian_posDef k).isUnit

lemma stationary_equation (k : Fin 3) :
    regularizedHessian k * fromRows (centralDerivative k) (oppositeDerivative k) =
      fromRows (pairHessian k) (diagonal fun i => (eigenvalue k i) / 8) := by
  rw [regularizedHessian, fromBlocks_mul_fromRows,
    central_stationary_equation, opposite_stationary_equation]

end Problem356.LocalHessian

end

end OAI
