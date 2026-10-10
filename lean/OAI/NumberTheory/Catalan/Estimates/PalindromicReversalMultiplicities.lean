import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import OAI.NumberTheory.Catalan.Determinants.RealColumnDeterminant
import OAI.NumberTheory.Catalan.Polynomial.PalindromicCoefficientMatrices

namespace OAI


noncomputable section

namespace InternalCatalan

open Polynomial
open scoped BigOperators

def IsPalindromicAt (p : ℕ) (P : (ZMod p)[X]) : Prop :=
  (∀ k, 2 * p - 2 < k → P.coeff k = 0) ∧
  (∀ k, k ≤ 2 * p - 2 → P.coeff (2 * p - 2 - k) = P.coeff k)

theorem IsPalindromicAt.ext {p : ℕ} (hp : 0 < p) {P Q : (ZMod p)[X]}
    (hP : IsPalindromicAt p P) (hQ : IsPalindromicAt p Q)
    (hlow : ∀ k < p, P.coeff k = Q.coeff k) : P = Q := by
  ext k
  by_cases hk : k < p
  · exact hlow k hk
  · by_cases hhigh : 2 * p - 2 < k
    · rw [hP.1 k hhigh, hQ.1 k hhigh]
    · have hle : k ≤ 2 * p - 2 := by omega
      have href : 2 * p - 2 - k < p := by omega
      exact (hP.2 k hle).symm.trans ((hlow _ href).trans (hQ.2 k hle))

theorem IsPalindromicAt.C_mul {p : ℕ} {P : (ZMod p)[X]}
    (hP : IsPalindromicAt p P) (c : ZMod p) :
    IsPalindromicAt p (C c * P) := by
  constructor
  · intro k hk
    simp only [coeff_C_mul, hP.1 k hk, mul_zero]
  · intro k hk
    simp only [coeff_C_mul, hP.2 k hk]

theorem IsPalindromicAt.sum {p : ℕ} {ι : Type*} (s : Finset ι)
    (P : ι → (ZMod p)[X]) (hP : ∀ i ∈ s, IsPalindromicAt p (P i)) :
    IsPalindromicAt p (∑ i ∈ s, P i) := by
  constructor
  · intro k hk
    rw [finsetSum_coeff]
    apply Finset.sum_eq_zero
    intro i hi
    exact (hP i hi).1 k hk
  · intro k hk
    simp only [finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro i hi
    exact (hP i hi).2 k hk

theorem IsPalindromicAt.natDegree_le {p : ℕ} {P : (ZMod p)[X]}
    (hP : IsPalindromicAt p P) : P.natDegree ≤ 2 * p - 2 :=
  Polynomial.natDegree_le_iff_coeff_eq_zero.mpr hP.1

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Polynomial
open scoped BigOperators

private theorem one_add_X_sq_natDegree_le (p : ℕ) :
    (1 + X ^ 2 : (ZMod p)[X]).natDegree ≤ 2 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  simp [coeff_one, show k ≠ 0 by omega, show k ≠ 2 by omega]

private theorem one_add_X_sq_pow_natDegree_le (p n : ℕ) :
    ((1 + X ^ 2 : (ZMod p)[X]) ^ n).natDegree ≤ 2 * n := by
  simpa only [Nat.mul_comm] using
    natDegree_pow_le_of_le n (one_add_X_sq_natDegree_le p)

private theorem reflect_one_add_X_sq (p : ℕ) :
    reflect 2 (1 + X ^ 2 : (ZMod p)[X]) = 1 + X ^ 2 := by
  rw [reflect_add, reflect_one, reflect_monomial, revAt_le (by omega)]
  simp [add_comm]

private theorem reflect_one_add_X_sq_pow (p n : ℕ) :
    reflect (2 * n) ((1 + X ^ 2 : (ZMod p)[X]) ^ n) =
      (1 + X ^ 2) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ (1 + X ^ 2 : (ZMod p)[X]) n]
    rw [show 2 * (n + 1) = 2 * n + 2 by omega,
      reflect_mul _ _ (one_add_X_sq_pow_natDegree_le p n)
        (one_add_X_sq_natDegree_le p), ih, reflect_one_add_X_sq]

theorem isPalindromicAt_of_reflect {p : ℕ} {P : (ZMod p)[X]}
    (hdeg : P.natDegree ≤ 2 * p - 2)
    (hreflect : reflect (2 * p - 2) P = P) : IsPalindromicAt p P := by
  constructor
  · intro k hk
    exact coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt hk)
  · intro k hk
    have h := congrArg (fun Q : (ZMod p)[X] => Q.coeff k) hreflect
    simpa only [coeff_reflect, revAt_le hk] using h

theorem palindromicU_natDegree_le {p l : ℕ} (hp : 0 < p) (hl : l < p) :
    (palindromicU p l).natDegree ≤ 2 * p - 2 := by
  have hD : 2 * p - 2 = 2 * l + 2 * (p - 1 - l) := by omega
  have hx : (X ^ l : (ZMod p)[X]).natDegree ≤ 2 * l :=
    (natDegree_X_pow_le l).trans (by omega)
  rw [palindromicU_factor, hD]
  apply (natDegree_C_mul_le _ _).trans
  exact natDegree_mul_le.trans
    (Nat.add_le_add hx (one_add_X_sq_pow_natDegree_le p (p - 1 - l)))

theorem palindromicU_reflect {p l : ℕ} (hp : 0 < p) (hl : l < p) :
    reflect (2 * p - 2) (palindromicU p l) = palindromicU p l := by
  have hD : 2 * p - 2 = 2 * l + 2 * (p - 1 - l) := by omega
  have hx : (X ^ l : (ZMod p)[X]).natDegree ≤ 2 * l :=
    (natDegree_X_pow_le l).trans (by omega)
  simp only [palindromicU_factor]
  rw [hD, reflect_C_mul,
    reflect_mul _ _ hx (one_add_X_sq_pow_natDegree_le p (p - 1 - l)),
    reflect_monomial, revAt_le (by omega), show 2 * l - l = l by omega,
    reflect_one_add_X_sq_pow]

theorem palindromicU_isPalindromic {p l : ℕ} (hp : 0 < p) (hl : l < p) :
    IsPalindromicAt p (palindromicU p l) :=
  isPalindromicAt_of_reflect (palindromicU_natDegree_le hp hl)
    (palindromicU_reflect hp hl)

theorem palindromicQ_eq_sum (p i : ℕ) :
    palindromicQ p i = ∑ j ∈ Finset.range (p - i),
      (X : (ZMod p)[X]) ^ (i + 2 * j) := by
  rw [palindromicQ, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact (pow_add _ _ _).symm

theorem palindromicQ_natDegree_le {p i : ℕ} (hp : 0 < p) (hi : i < p) :
    (palindromicQ p i).natDegree ≤ 2 * p - 2 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [palindromicQ_eq_sum, finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro j hj
  have hj' := Finset.mem_range.mp hj
  rw [coeff_X_pow, ite_eq_right (by omega)]

theorem palindromicQ_reflect {p i : ℕ} (hp : 0 < p) (hi : i < p) :
    reflect (2 * p - 2) (palindromicQ p i) = palindromicQ p i := by
  simp only [palindromicQ_eq_sum]
  calc
    reflect (2 * p - 2) (∑ j ∈ Finset.range (p - i),
        (X : (ZMod p)[X]) ^ (i + 2 * j)) =
        ∑ j ∈ Finset.range (p - i),
          reflect (2 * p - 2) ((X : (ZMod p)[X]) ^ (i + 2 * j)) := by
      ext k
      simp only [coeff_reflect, finsetSum_coeff]
    _ = ∑ j ∈ Finset.range (p - i),
        (X : (ZMod p)[X]) ^ (i + 2 * (p - i - 1 - j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [reflect_monomial, revAt_le (by omega)]
      congr 1
      omega
    _ = ∑ j ∈ Finset.range (p - i),
        (X : (ZMod p)[X]) ^ (i + 2 * j) :=
      Finset.sum_range_reflect (fun j => (X : (ZMod p)[X]) ^ (i + 2 * j)) (p - i)

theorem palindromicQ_isPalindromic {p i : ℕ} (hp : 0 < p) (hi : i < p) :
    IsPalindromicAt p (palindromicQ p i) :=
  isPalindromicAt_of_reflect (palindromicQ_natDegree_le hp hi)
    (palindromicQ_reflect hp hi)

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Polynomial
open scoped BigOperators

def palindromicUCombination (p : ℕ) (c : Fin p → ZMod p) : (ZMod p)[X] :=
  ∑ l : Fin p, C (c l) * palindromicU p l.val

def palindromicUCoordinates (p : ℕ) (P : (ZMod p)[X]) : Fin p → ZMod p :=
  (palindromicUCoeffMatrix p)⁻¹.mulVec (fun k => P.coeff k.val)

theorem palindromicUCombination_coeff (p : ℕ) (c : Fin p → ZMod p) (k : Fin p) :
    (palindromicUCombination p c).coeff k.val =
      (palindromicUCoeffMatrix p).mulVec c k := by
  simp only [palindromicUCombination, finsetSum_coeff, coeff_C_mul,
    Matrix.mulVec_apply_eq_sum, palindromicUCoeffMatrix]
  apply Finset.sum_congr rfl
  intro l hl
  exact mul_comm _ _

theorem palindromicUCombination_isPalindromic {p : ℕ} (hp : 0 < p)
    (c : Fin p → ZMod p) : IsPalindromicAt p (palindromicUCombination p c) := by
  apply IsPalindromicAt.sum
  intro l hl
  exact (palindromicU_isPalindromic hp l.isLt).C_mul (c l)

theorem palindromicUCoordinates_spec {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (P : (ZMod p)[X]) :
    (palindromicUCoeffMatrix p).mulVec (palindromicUCoordinates p P) =
      fun k => P.coeff k.val := by
  have hunit : IsUnit (palindromicUCoeffMatrix p).det :=
    isUnit_iff_ne_zero.mpr (det_palindromicUCoeffMatrix_ne_zero hp2)
  unfold palindromicUCoordinates
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]

theorem palindromicU_expansion {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (P : (ZMod p)[X]) (hP : IsPalindromicAt p P) :
    P = palindromicUCombination p (palindromicUCoordinates p P) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  apply IsPalindromicAt.ext hp hP (palindromicUCombination_isPalindromic hp _)
  intro k hk
  rw [palindromicUCombination_coeff p _ (⟨k, hk⟩ : Fin p)]
  exact (congrFun (palindromicUCoordinates_spec hp2 P) (⟨k, hk⟩ : Fin p)).symm

def palindromicTransitionMatrix (p : ℕ) : Matrix (Fin p) (Fin p) (ZMod p) :=
  (palindromicUCoeffMatrix p)⁻¹ * palindromicQCoeffMatrix p

theorem palindromicUCoordinates_Q (p : ℕ) (i : Fin p) :
    palindromicUCoordinates p (palindromicQ p i.val) =
      fun l => palindromicTransitionMatrix p l i := by
  funext l
  rfl

theorem palindromicUCoeffMatrix_mul_transition {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) :
    palindromicUCoeffMatrix p * palindromicTransitionMatrix p =
      palindromicQCoeffMatrix p := by
  exact Matrix.mul_nonsing_inv_cancel_left _ _
    (isUnit_iff_ne_zero.mpr (det_palindromicUCoeffMatrix_ne_zero hp2))

theorem palindromicQ_eq_sum_U {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (i : Fin p) :
    palindromicQ p i.val =
      ∑ l : Fin p, C (palindromicTransitionMatrix p l i) * palindromicU p l.val := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have h := palindromicU_expansion hp2 (palindromicQ p i.val)
    (palindromicQ_isPalindromic hp i.isLt)
  rw [palindromicUCoordinates_Q] at h
  exact h

theorem det_palindromicTransitionMatrix {p : ℕ} [Fact p.Prime] :
    (palindromicTransitionMatrix p).det =
      (∏ l : Fin p, (2 : ZMod p) ^ l.val)⁻¹ := by
  rw [palindromicTransitionMatrix, Matrix.det_mul, Matrix.det_nonsing_inv,
    Ring.inverse_eq_inv, det_palindromicUCoeffMatrix, det_palindromicQCoeffMatrix, mul_one]

theorem det_palindromicTransitionMatrix_ne_zero {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) : (palindromicTransitionMatrix p).det ≠ 0 := by
  rw [det_palindromicTransitionMatrix]
  apply inv_ne_zero
  rw [← det_palindromicUCoeffMatrix]
  exact det_palindromicUCoeffMatrix_ne_zero hp2

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Polynomial
open scoped BigOperators

def palindromicReverseIndex {p : ℕ} (i : Fin p) (hi : 0 < i.val) : Fin p :=
  ⟨p - i.val, by have h := i.isLt; omega⟩

@[simp] theorem palindromicReverseIndex_val {p : ℕ} (i : Fin p)
    (hi : 0 < i.val) : (palindromicReverseIndex i hi).val = p - i.val := rfl

theorem palindromicReverseIndex_pos {p : ℕ} (i : Fin p) (hi : 0 < i.val) :
    0 < (palindromicReverseIndex i hi).val := by
  have h := i.isLt
  simp only [palindromicReverseIndex_val]
  omega

@[simp] theorem palindromicReverseIndex_invol {p : ℕ} (i : Fin p)
    (hi : 0 < i.val) :
    palindromicReverseIndex (palindromicReverseIndex i hi)
      (palindromicReverseIndex_pos i hi) = i := by
  apply Fin.ext
  simp only [palindromicReverseIndex_val]
  have h := i.isLt
  omega

def palindromicQPrime (p : ℕ) (i : Fin p) : (ZMod p)[X] :=
  if i.val = 0 then 0 else palindromicQ p (p - i.val)

theorem palindromicQPrime_zero {p : ℕ} (i : Fin p) (hi : i.val = 0) :
    palindromicQPrime p i = 0 := by simp [palindromicQPrime, hi]

theorem palindromicQPrime_pos {p : ℕ} (i : Fin p) (hi : 0 < i.val) :
    palindromicQPrime p i =
      palindromicQ p (palindromicReverseIndex i hi).val := by
  simp [palindromicQPrime, show i.val ≠ 0 by omega]

def palindromicReversalMatrix (p : ℕ) : Matrix (Fin p) (Fin p) (ZMod p) :=
  fun k i => if i.val = 0 then 0 else if k.val = p - i.val then 1 else 0

theorem palindromicReversalMatrix_column_zero {p : ℕ} (i : Fin p)
    (hi : i.val = 0) (k : Fin p) : palindromicReversalMatrix p k i = 0 := by
  simp [palindromicReversalMatrix, hi]

theorem palindromicReversalMatrix_column_pos {p : ℕ} (i : Fin p)
    (hi : 0 < i.val) (k : Fin p) :
    palindromicReversalMatrix p k i =
      if k = palindromicReverseIndex i hi then 1 else 0 := by
  have heq : k.val = p - i.val ↔ k = palindromicReverseIndex i hi := by
    constructor
    · intro h
      exact Fin.ext h
    · intro h
      exact congrArg Fin.val h
  simp only [palindromicReversalMatrix, ite_eq_right (show i.val ≠ 0 by omega), heq]

theorem mul_palindromicReversalMatrix_column_zero {p : ℕ} {ι : Type*}
    (A : Matrix ι (Fin p) (ZMod p)) (l : ι) (i : Fin p) (hi : i.val = 0) :
    (A * palindromicReversalMatrix p) l i = 0 := by
  simp [Matrix.mul_apply, palindromicReversalMatrix_column_zero i hi]

theorem mul_palindromicReversalMatrix_column_pos {p : ℕ} {ι : Type*}
    (A : Matrix ι (Fin p) (ZMod p)) (l : ι) (i : Fin p) (hi : 0 < i.val) :
    (A * palindromicReversalMatrix p) l i = A l (palindromicReverseIndex i hi) := by
  simp [Matrix.mul_apply, palindromicReversalMatrix_column_pos i hi, mul_ite]

def palindromicReversedTransitionMatrix (p : ℕ) : Matrix (Fin p) (Fin p) (ZMod p) :=
  palindromicTransitionMatrix p * palindromicReversalMatrix p

theorem palindromicReversedTransitionMatrix_column_zero {p : ℕ} (l i : Fin p)
    (hi : i.val = 0) : palindromicReversedTransitionMatrix p l i = 0 :=
  mul_palindromicReversalMatrix_column_zero _ l i hi

theorem palindromicReversedTransitionMatrix_column_pos {p : ℕ} (l i : Fin p)
    (hi : 0 < i.val) :
    palindromicReversedTransitionMatrix p l i =
      palindromicTransitionMatrix p l (palindromicReverseIndex i hi) :=
  mul_palindromicReversalMatrix_column_pos _ l i hi

theorem palindromicQPrime_eq_sum_U {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (i : Fin p) :
    palindromicQPrime p i = ∑ l : Fin p,
      C (palindromicReversedTransitionMatrix p l i) * palindromicU p l.val := by
  by_cases hi : i.val = 0
  · rw [palindromicQPrime_zero i hi]
    symm
    apply Finset.sum_eq_zero
    intro l hl
    rw [palindromicReversedTransitionMatrix_column_zero l i hi]
    simp
  · have hip : 0 < i.val := by omega
    rw [palindromicQPrime_pos i hip, palindromicQ_eq_sum_U hp2]
    apply Finset.sum_congr rfl
    intro l hl
    rw [palindromicReversedTransitionMatrix_column_pos l i hip]

theorem palindromicReversalMatrix_mulVec_basis (p : ℕ) (i : Fin p) :
    (palindromicReversalMatrix p).mulVec (fun j => if j = i then 1 else 0) =
      fun k => palindromicReversalMatrix p k i := by
  funext k
  simp [Matrix.mulVec_apply_eq_sum, mul_ite]

theorem palindromicReversalMatrix_mulVec_basis_zero {p : ℕ} (i : Fin p)
    (hi : i.val = 0) :
    (palindromicReversalMatrix p).mulVec (fun j => if j = i then 1 else 0) = 0 := by
  rw [palindromicReversalMatrix_mulVec_basis]
  funext k
  exact palindromicReversalMatrix_column_zero i hi k

theorem palindromicReversalMatrix_mulVec_basis_pos {p : ℕ} (i : Fin p)
    (hi : 0 < i.val) :
    (palindromicReversalMatrix p).mulVec (fun j => if j = i then 1 else 0) =
      fun k => if k = palindromicReverseIndex i hi then 1 else 0 := by
  rw [palindromicReversalMatrix_mulVec_basis]
  funext k
  exact palindromicReversalMatrix_column_pos i hi k

theorem palindromicReversalMatrix_mul_self {p : ℕ} (k i : Fin p) :
    (palindromicReversalMatrix p * palindromicReversalMatrix p) k i =
      if i.val = 0 then 0 else if k = i then 1 else 0 := by
  by_cases hi : i.val = 0
  · simp [mul_palindromicReversalMatrix_column_zero _ k i hi, hi]
  · have hip : 0 < i.val := by omega
    rw [mul_palindromicReversalMatrix_column_pos _ k i hip,
      palindromicReversalMatrix_column_pos _ (palindromicReverseIndex_pos i hip),
      palindromicReverseIndex_invol]
    simp [hi]

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open scoped BigOperators

theorem palindromicTransitionMatrix_lower {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) : (palindromicTransitionMatrix p).IsLowerTriangular := by
  have hunit : IsUnit (palindromicUCoeffMatrix p).det :=
    isUnit_iff_ne_zero.mpr (det_palindromicUCoeffMatrix_ne_zero hp2)
  cases ((palindromicUCoeffMatrix p).isUnit_iff_isUnit_det.mpr hunit).nonempty_invertible
  have hinv : ((palindromicUCoeffMatrix p)⁻¹).IsLowerTriangular :=
    Matrix.blockTriangular_inv_of_blockTriangular (palindromicUCoeffMatrix_lower p)
  exact hinv.mul (palindromicQCoeffMatrix_lower p)

theorem palindromicTransitionMatrix_below_index {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {l i : Fin p} (hli : l < i) :
    palindromicTransitionMatrix p l i = 0 :=
  palindromicTransitionMatrix_lower hp2 hli

theorem palindromicTransitionMatrix_diagonal_mul {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (i : Fin p) :
    (2 : ZMod p) ^ i.val * palindromicTransitionMatrix p i i = 1 := by
  have h := congrArg (fun M : Matrix (Fin p) (Fin p) (ZMod p) => M i i)
    (palindromicUCoeffMatrix_mul_transition hp2)
  rw [Matrix.mul_apply] at h
  have hsum :
      (∑ k : Fin p, palindromicUCoeffMatrix p i k * palindromicTransitionMatrix p k i) =
        palindromicUCoeffMatrix p i i * palindromicTransitionMatrix p i i := by
    apply Finset.sum_eq_single i
    · intro k hk hki
      rcases lt_or_gt_of_ne hki with hlt | hgt
      · rw [palindromicTransitionMatrix_below_index hp2 hlt, mul_zero]
      · rw [palindromicUCoeffMatrix_lower p hgt, zero_mul]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ i))
  rw [hsum] at h
  simpa only [palindromicUCoeffMatrix, palindromicQCoeffMatrix,
    palindromicU_coeff_self, palindromicQ_coeff_self i.isLt] using h

theorem palindromicTransitionMatrix_diagonal {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (i : Fin p) :
    palindromicTransitionMatrix p i i = ((2 : ZMod p) ^ i.val)⁻¹ := by
  have hpow : (2 : ZMod p) ^ i.val ≠ 0 :=
    pow_ne_zero _ (palindromic_two_ne_zero hp2)
  apply mul_left_cancel₀ hpow
  rw [mul_inv_cancel₀ hpow]
  exact palindromicTransitionMatrix_diagonal_mul hp2 i

theorem palindromicTransitionMatrix_diagonal_ne_zero {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (i : Fin p) : palindromicTransitionMatrix p i i ≠ 0 := by
  rw [palindromicTransitionMatrix_diagonal hp2 i]
  exact inv_ne_zero (pow_ne_zero _ (palindromic_two_ne_zero hp2))

theorem det_palindromicTransitionMatrix_exact {p : ℕ} [Fact p.Prime] :
    (palindromicTransitionMatrix p).det =
      ((2 : ZMod p) ^ (p * (p - 1) / 2))⁻¹ := by
  have hsum : (∑ i : Fin p, i.val) = p * (p - 1) / 2 := by
    calc
      (∑ i : Fin p, i.val) = ∑ i ∈ Finset.range p, i :=
        Fin.sum_univ_eq_sum_range (fun i : ℕ => i) p
      _ = p * (p - 1) / 2 := Finset.sum_range_id p
  rw [det_palindromicTransitionMatrix, Finset.prod_pow_eq_pow_sum, hsum]

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Polynomial
open scoped BigOperators

theorem palindromicQPrime_formula {p : ℕ} (i : Fin p) :
    palindromicQPrime p i = (X : (ZMod p)[X]) ^ (p - i.val) *
      ∑ j ∈ Finset.range i.val, X ^ (2 * j) := by
  by_cases hi : i.val = 0
  · simp [palindromicQPrime, hi]
  · have hsub : p - (p - i.val) = i.val := by have h := i.isLt; omega
    simp only [palindromicQPrime, ite_eq_right hi, palindromicQ, hsub]

theorem palindromicQ_add_X_pow_QPrime {p : ℕ} (i : Fin p) :
    palindromicQ p i.val + (X : (ZMod p)[X]) ^ p * palindromicQPrime p i =
      X ^ i.val * ∑ j ∈ Finset.range p, X ^ (2 * j) := by
  have hsplit := Finset.sum_range_add
    (fun j : ℕ => (X : (ZMod p)[X]) ^ (2 * j)) (p - i.val) i.val
  rw [Nat.sub_add_cancel (Nat.le_of_lt i.isLt)] at hsplit
  rw [palindromicQ, palindromicQPrime_formula, hsplit, mul_add]
  congr 1
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [← pow_add]
  congr 1
  have h := i.isLt
  omega

theorem palindromicPairing_eq_sum_U {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (i : Fin p) :
    (X : (ZMod p)[X]) ^ i.val * (∑ j ∈ Finset.range p, X ^ (2 * j)) =
      ∑ l : Fin p, (C (palindromicTransitionMatrix p l i) +
        C (palindromicReversedTransitionMatrix p l i) * X ^ p) *
          palindromicU p l.val := by
  rw [← palindromicQ_add_X_pow_QPrime, palindromicQ_eq_sum_U hp2,
    palindromicQPrime_eq_sum_U hp2, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  ring

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Polynomial
open scoped BigOperators

def palindromicResidueSum {R : Type*} [CommSemiring R] (p : ℕ)
    (A : Fin p → R[X]) : R[X] :=
  ∑ l : Fin p, X ^ l.val * (A l).comp (X ^ p)

theorem palindromicResidue_sub_not_dvd {p : ℕ} (l ell : Fin p) (u : ℕ)
    (hne : l ≠ ell) (hle : l.val ≤ u * p + ell.val) :
    ¬ p ∣ u * p + ell.val - l.val := by
  intro hd
  have hz : (u * p + ell.val - l.val) % p = 0 := Nat.mod_eq_zero_of_dvd hd
  have hmod := congrArg (fun n : ℕ => n % p) (Nat.sub_add_cancel hle)
  have hval : l.val = ell.val := by
    simpa only [Nat.add_mod, Nat.mul_mod, hz, Nat.mod_self, Nat.mul_zero,
      Nat.zero_mod, zero_add, Nat.mod_eq_of_lt l.isLt,
      Nat.mod_eq_of_lt ell.isLt] using hmod
  exact hne (Fin.ext hval)

theorem palindromicResidueSum_coeff {R : Type*} [CommSemiring R] {p : ℕ}
    (hp : 0 < p) (A : Fin p → R[X]) (u : ℕ) (ell : Fin p) :
    (palindromicResidueSum p A).coeff (u * p + ell.val) = (A ell).coeff u := by
  classical
  rw [palindromicResidueSum, finsetSum_coeff, Finset.sum_eq_single ell]
  · rw [coeff_X_pow_mul, ← expand_eq_comp_X_pow, coeff_expand_mul hp]
  · intro l hl hne
    rw [coeff_X_pow_mul']
    split_ifs with hle
    · rw [← expand_eq_comp_X_pow, coeff_expand hp,
        ite_eq_right (palindromicResidue_sub_not_dvd l ell u hne hle)]
    · rfl
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ ell))

def palindromicPBase (p j : ℕ) : (ZMod p)[X] :=
  (rowP 1 j).map (Int.castRingHom (ZMod p))

def palindromicDBase (p j : ℕ) : (ZMod p)[X] :=
  (rowD 1 j).map (Int.castRingHom (ZMod p))

def palindromicPBaseCombination (p r0 : ℕ) (i l : Fin p) : (ZMod p)[X] :=
  C (palindromicTransitionMatrix p l i) * palindromicPBase p r0 +
    C (palindromicReversedTransitionMatrix p l i) * palindromicPBase p (r0 + 1)

def palindromicDBaseCombination (p r0 : ℕ) (i l : Fin p) : (ZMod p)[X] :=
  C (palindromicTransitionMatrix p l i) * palindromicDBase p r0 +
    C (palindromicReversedTransitionMatrix p l i) * palindromicDBase p (r0 + 1)

def palindromicPResidueSum (p r0 : ℕ) (i : Fin p) : (ZMod p)[X] :=
  ∑ l : Fin p, X ^ l.val * X ^ p *
    (C (palindromicTransitionMatrix p l i) * (palindromicPBase p r0).comp (X ^ p) +
      C (palindromicReversedTransitionMatrix p l i) *
        (palindromicPBase p (r0 + 1)).comp (X ^ p))

def palindromicDResidueSum (p r0 : ℕ) (i : Fin p) : (ZMod p)[X] :=
  ∑ l : Fin p, X ^ l.val *
    (C (palindromicTransitionMatrix p l i) * (palindromicDBase p r0).comp (X ^ p) +
      C (palindromicReversedTransitionMatrix p l i) *
        (palindromicDBase p (r0 + 1)).comp (X ^ p))

theorem palindromicPResidueSum_eq_X_pow_mul (p r0 : ℕ) (i : Fin p) :
    palindromicPResidueSum p r0 i = X ^ p *
      palindromicResidueSum p (palindromicPBaseCombination p r0 i) := by
  classical
  simp only [palindromicPResidueSum, palindromicResidueSum,
    palindromicPBaseCombination, add_comp, mul_comp, C_comp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  ring

theorem palindromicDResidueSum_eq (p r0 : ℕ) (i : Fin p) :
    palindromicDResidueSum p r0 i =
      palindromicResidueSum p (palindromicDBaseCombination p r0 i) := by
  simp only [palindromicDResidueSum, palindromicResidueSum,
    palindromicDBaseCombination, add_comp, mul_comp, C_comp]

theorem palindromicPResidueSum_coeff (p r0 u : ℕ) (i ell : Fin p) :
    (palindromicPResidueSum p r0 i).coeff ((u + 1) * p + ell.val) =
      palindromicTransitionMatrix p ell i * (palindromicPBase p r0).coeff u +
        palindromicReversedTransitionMatrix p ell i *
          (palindromicPBase p (r0 + 1)).coeff u := by
  have hp : 0 < p := lt_of_le_of_lt (Nat.zero_le ell.val) ell.isLt
  have hindex : (u + 1) * p + ell.val = (u * p + ell.val) + p := by ring
  rw [palindromicPResidueSum_eq_X_pow_mul, hindex, coeff_X_pow_mul,
    palindromicResidueSum_coeff hp]
  simp only [palindromicPBaseCombination, coeff_add, coeff_C_mul]

theorem palindromicDResidueSum_coeff (p r0 u : ℕ) (i ell : Fin p) :
    (palindromicDResidueSum p r0 i).coeff (u * p + ell.val) =
      palindromicTransitionMatrix p ell i * (palindromicDBase p r0).coeff u +
        palindromicReversedTransitionMatrix p ell i *
          (palindromicDBase p (r0 + 1)).coeff u := by
  have hp : 0 < p := lt_of_le_of_lt (Nat.zero_le ell.val) ell.isLt
  rw [palindromicDResidueSum_eq, palindromicResidueSum_coeff hp]
  simp only [palindromicDBaseCombination, coeff_add, coeff_C_mul]

theorem palindromicPResidueSum_coeff_below (p r0 : ℕ) (i ell : Fin p) :
    (palindromicPResidueSum p r0 i).coeff ell.val = 0 := by
  rw [palindromicPResidueSum_eq_X_pow_mul, coeff_X_pow_mul',
    ite_eq_right (Nat.not_le_of_lt ell.isLt)]

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

def palindromicStandardVector {p : ℕ} (i : Fin p) : Fin p → ZMod p :=
  fun k => if k = i then 1 else 0

def palindromicReversalPlusVector {p : ℕ} (i : Fin p) (hi : 0 < i.val) :
    Fin p → ZMod p :=
  palindromicStandardVector i +
    palindromicStandardVector (palindromicReverseIndex i hi)

def palindromicReversalMinusVector {p : ℕ} (i : Fin p) (hi : 0 < i.val) :
    Fin p → ZMod p :=
  palindromicStandardVector i -
    palindromicStandardVector (palindromicReverseIndex i hi)

@[simp] theorem palindromicStandardVector_self {p : ℕ} (i : Fin p) :
    palindromicStandardVector i i = 1 := by simp [palindromicStandardVector]

theorem palindromicStandardVector_ne_zero {p : ℕ} [Fact p.Prime] (i : Fin p) :
    palindromicStandardVector i ≠ 0 := by
  intro h
  have hval := congrFun h i
  simp at hval

theorem palindromicReversalMatrix_mulVec_zero {p : ℕ} (i : Fin p)
    (hi : i.val = 0) :
    (palindromicReversalMatrix p).mulVec (palindromicStandardVector i) = 0 :=
  palindromicReversalMatrix_mulVec_basis_zero i hi

theorem palindromicReversalMatrix_mulVec_e0 {p : ℕ} (hp : 0 < p) :
    (palindromicReversalMatrix p).mulVec
      (palindromicStandardVector (⟨0, hp⟩ : Fin p)) =
        (0 : ZMod p) • palindromicStandardVector (⟨0, hp⟩ : Fin p) := by
  rw [palindromicReversalMatrix_mulVec_zero _ rfl, zero_smul]

theorem palindromicReversalMatrix_mulVec_standard_pos {p : ℕ} (i : Fin p)
    (hi : 0 < i.val) :
    (palindromicReversalMatrix p).mulVec (palindromicStandardVector i) =
      palindromicStandardVector (palindromicReverseIndex i hi) :=
  palindromicReversalMatrix_mulVec_basis_pos i hi

theorem palindromicReversalMatrix_mulVec_plus {p : ℕ} (i : Fin p)
    (hi : 0 < i.val) :
    (palindromicReversalMatrix p).mulVec (palindromicReversalPlusVector i hi) =
      palindromicReversalPlusVector i hi := by
  rw [palindromicReversalPlusVector, Matrix.mulVec_add,
    palindromicReversalMatrix_mulVec_standard_pos i hi,
    palindromicReversalMatrix_mulVec_standard_pos _ (palindromicReverseIndex_pos i hi),
    palindromicReverseIndex_invol]
  exact add_comm _ _

theorem palindromicReversalMatrix_mulVec_minus {p : ℕ} (i : Fin p)
    (hi : 0 < i.val) :
    (palindromicReversalMatrix p).mulVec (palindromicReversalMinusVector i hi) =
      -palindromicReversalMinusVector i hi := by
  rw [palindromicReversalMinusVector, Matrix.mulVec_sub,
    palindromicReversalMatrix_mulVec_standard_pos i hi,
    palindromicReversalMatrix_mulVec_standard_pos _ (palindromicReverseIndex_pos i hi),
    palindromicReverseIndex_invol]
  exact (neg_sub _ _).symm

theorem palindromicReversalMatrix_eigenvalue_one {p : ℕ} (i : Fin p)
    (hi : 0 < i.val) :
    (palindromicReversalMatrix p).mulVec (palindromicReversalPlusVector i hi) =
      (1 : ZMod p) • palindromicReversalPlusVector i hi := by
  rw [one_smul, palindromicReversalMatrix_mulVec_plus]

theorem palindromicReversalMatrix_eigenvalue_neg_one {p : ℕ} (i : Fin p)
    (hi : 0 < i.val) :
    (palindromicReversalMatrix p).mulVec (palindromicReversalMinusVector i hi) =
      (-1 : ZMod p) • palindromicReversalMinusVector i hi := by
  rw [neg_one_smul, palindromicReversalMatrix_mulVec_minus]

theorem palindromicReverseIndex_ne {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (i : Fin p) (hi : 0 < i.val) : i ≠ palindromicReverseIndex i hi := by
  intro heq
  have hval := congrArg Fin.val heq
  simp only [palindromicReverseIndex_val] at hval
  have hirange := i.isLt
  obtain ⟨k, hk⟩ := (Fact.out : p.Prime).odd_of_ne_two hp2
  omega

theorem palindromicReversalPlusVector_self {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (i : Fin p) (hi : 0 < i.val) :
    palindromicReversalPlusVector i hi i = 1 := by
  simp [palindromicReversalPlusVector, palindromicStandardVector,
    palindromicReverseIndex_ne hp2 i hi]

theorem palindromicReversalMinusVector_self {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (i : Fin p) (hi : 0 < i.val) :
    palindromicReversalMinusVector i hi i = 1 := by
  simp [palindromicReversalMinusVector, palindromicStandardVector,
    palindromicReverseIndex_ne hp2 i hi]

theorem palindromicReversalPlusVector_ne_zero {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (i : Fin p) (hi : 0 < i.val) :
    palindromicReversalPlusVector i hi ≠ 0 := by
  intro h
  have hval := congrFun h i
  exact one_ne_zero (by
    simpa only [palindromicReversalPlusVector_self hp2 i hi, Pi.zero_apply] using hval)

theorem palindromicReversalMinusVector_ne_zero {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (i : Fin p) (hi : 0 < i.val) :
    palindromicReversalMinusVector i hi ≠ 0 := by
  intro h
  have hval := congrFun h i
  exact one_ne_zero (by
    simpa only [palindromicReversalMinusVector_self hp2 i hi, Pi.zero_apply] using hval)

theorem palindromicReversalMatrix_transpose (p : ℕ) :
    Matrix.transpose (palindromicReversalMatrix p) = palindromicReversalMatrix p := by
  ext k i
  change palindromicReversalMatrix p i k = palindromicReversalMatrix p k i
  have hkbound := k.isLt
  have hibound := i.isLt
  by_cases hk : k.val = 0
  · by_cases hi : i.val = 0
    · simp [palindromicReversalMatrix, hk, hi]
    · simp [palindromicReversalMatrix, hk, hi, show 0 ≠ p - i.val by omega]
  · by_cases hi : i.val = 0
    · simp [palindromicReversalMatrix, hk, hi, show 0 ≠ p - k.val by omega]
    · have heq : i.val = p - k.val ↔ k.val = p - i.val := by omega
      simp only [palindromicReversalMatrix, ite_eq_right hk, ite_eq_right hi, heq]

theorem palindromicReversalMatrix_transpose_mulVec_plus {p : ℕ}
    (i : Fin p) (hi : 0 < i.val) :
    (Matrix.transpose (palindromicReversalMatrix p)).mulVec
      (palindromicReversalPlusVector i hi) =
      palindromicReversalPlusVector i hi := by
  rw [palindromicReversalMatrix_transpose, palindromicReversalMatrix_mulVec_plus]

theorem palindromicReversalMatrix_transpose_mulVec_minus {p : ℕ}
    (i : Fin p) (hi : 0 < i.val) :
    (Matrix.transpose (palindromicReversalMatrix p)).mulVec
      (palindromicReversalMinusVector i hi) =
      -palindromicReversalMinusVector i hi := by
  rw [palindromicReversalMatrix_transpose, palindromicReversalMatrix_mulVec_minus]

theorem palindromic_prime_card_split {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    p = 1 + 2 * ((p - 1) / 2) := by
  have hp := (Fact.out : p.Prime).pos
  obtain ⟨m, hm⟩ := (Fact.out : p.Prime).even_sub_one hp2
  omega







open Matrix Module

def palindromicPairMate (p : ℕ) (i : Fin p) : Fin p :=
  if hi : i.val = 0 then i
  else palindromicReverseIndex i (Nat.pos_of_ne_zero hi)

theorem palindromicPairMate_zero {p : ℕ} (i : Fin p) (hi : i.val = 0) :
    palindromicPairMate p i = i := by
  simp [palindromicPairMate, hi]

theorem palindromicPairMate_of_pos {p : ℕ} (i : Fin p) (hi : 0 < i.val) :
    palindromicPairMate p i = palindromicReverseIndex i hi := by
  simp [palindromicPairMate, Nat.ne_of_gt hi]

theorem palindromicPairMate_val {p : ℕ} (i : Fin p) (hi : 0 < i.val) :
    (palindromicPairMate p i).val = p - i.val := by
  rw [palindromicPairMate_of_pos i hi, palindromicReverseIndex_val]

theorem palindromicPairMate_pos {p : ℕ} (i : Fin p) (hi : 0 < i.val) :
    0 < (palindromicPairMate p i).val := by
  rw [palindromicPairMate_val i hi]
  have := i.isLt
  omega

@[simp] theorem palindromicPairMate_invol {p : ℕ} (i : Fin p) :
    palindromicPairMate p (palindromicPairMate p i) = i := by
  by_cases hi : i.val = 0
  · simp [palindromicPairMate_zero i hi]
  · have hip : 0 < i.val := Nat.pos_of_ne_zero hi
    apply Fin.ext
    rw [palindromicPairMate_val _ (palindromicPairMate_pos i hip),
      palindromicPairMate_val i hip]
    have := i.isLt
    omega

theorem palindromicPairMate_upper {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (i : Fin p) (hi : 0 < i.val) (hle : i.val ≤ (p - 1) / 2) :
    (p - 1) / 2 < (palindromicPairMate p i).val := by
  have hsplit := palindromic_prime_card_split hp2
  have hibound := i.isLt
  rw [palindromicPairMate_val i hi]
  omega

theorem palindromicPairMate_lower {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (i : Fin p) (hi : (p - 1) / 2 < i.val) :
    (palindromicPairMate p i).val ≤ (p - 1) / 2 := by
  have hsplit := palindromic_prime_card_split hp2
  have hibound := i.isLt
  have hip : 0 < i.val := by omega
  rw [palindromicPairMate_val i hip]
  omega

def palindromicEigenLambda (p : ℕ) (i : Fin p) : ZMod p :=
  if i.val = 0 then 0 else if i.val ≤ (p - 1) / 2 then 1 else -1

theorem palindromicEigenLambda_zero {p : ℕ} (i : Fin p) (hi : i.val = 0) :
    palindromicEigenLambda p i = 0 := by
  simp [palindromicEigenLambda, hi]

theorem palindromicEigenLambda_lower {p : ℕ} (i : Fin p) (hi : 0 < i.val)
    (hle : i.val ≤ (p - 1) / 2) : palindromicEigenLambda p i = 1 := by
  simp [palindromicEigenLambda, Nat.ne_of_gt hi, hle]

theorem palindromicEigenLambda_upper {p : ℕ} (i : Fin p)
    (hi : (p - 1) / 2 < i.val) : palindromicEigenLambda p i = -1 := by
  have hip : 0 < i.val := by omega
  simp [palindromicEigenLambda, Nat.ne_of_gt hip, not_le_of_gt hi]

def palindromicEigenCoordinatesLinear (p : ℕ) [Fact p.Prime] :
    (Fin p → ZMod p) →ₗ[ZMod p] (Fin p → ZMod p) where
  toFun v i :=
    if i.val = 0 then v i
    else if i.val ≤ (p - 1) / 2 then
      (v i + v (palindromicPairMate p i)) / 2
    else (v (palindromicPairMate p i) - v i) / 2
  map_add' v w := by
    funext i
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' a v := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

def palindromicEigenSynthesisLinear (p : ℕ) [Fact p.Prime] :
    (Fin p → ZMod p) →ₗ[ZMod p] (Fin p → ZMod p) where
  toFun v i :=
    if i.val = 0 then v i
    else if i.val ≤ (p - 1) / 2 then
      v i + v (palindromicPairMate p i)
    else v (palindromicPairMate p i) - v i
  map_add' v w := by
    funext i
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' a v := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

theorem palindromicEigenCoordinatesLinear_apply (p : ℕ) [Fact p.Prime]
    (v : Fin p → ZMod p) (i : Fin p) :
    palindromicEigenCoordinatesLinear p v i =
      if i.val = 0 then v i
      else if i.val ≤ (p - 1) / 2 then
        (v i + v (palindromicPairMate p i)) / 2
      else (v (palindromicPairMate p i) - v i) / 2 := rfl

theorem palindromicEigenSynthesisLinear_apply (p : ℕ) [Fact p.Prime]
    (v : Fin p → ZMod p) (i : Fin p) :
    palindromicEigenSynthesisLinear p v i =
      if i.val = 0 then v i
      else if i.val ≤ (p - 1) / 2 then
        v i + v (palindromicPairMate p i)
      else v (palindromicPairMate p i) - v i := rfl

theorem palindromicEigenSynthesis_coordinates {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (v : Fin p → ZMod p) :
    palindromicEigenSynthesisLinear p (palindromicEigenCoordinatesLinear p v) = v := by
  funext i
  by_cases hi : i.val = 0
  · simp [palindromicEigenSynthesisLinear_apply,
      palindromicEigenCoordinatesLinear_apply, hi]
  · have hip : 0 < i.val := Nat.pos_of_ne_zero hi
    have hm0 : (palindromicPairMate p i).val ≠ 0 :=
      Nat.ne_of_gt (palindromicPairMate_pos i hip)
    by_cases hlo : i.val ≤ (p - 1) / 2
    · have hmhi : ¬ (palindromicPairMate p i).val ≤ (p - 1) / 2 :=
        not_le_of_gt (palindromicPairMate_upper hp2 i hip hlo)
      simp only [palindromicEigenSynthesisLinear_apply,
        palindromicEigenCoordinatesLinear_apply, hi, hlo, hm0, hmhi,
        ite_false, ite_true, palindromicPairMate_invol]
      field_simp [palindromic_two_ne_zero hp2]
      ring
    · have hmlo := palindromicPairMate_lower hp2 i (lt_of_not_ge hlo)
      simp only [palindromicEigenSynthesisLinear_apply,
        palindromicEigenCoordinatesLinear_apply, hi, hlo, hm0, hmlo,
        ite_false, ite_true, palindromicPairMate_invol]
      field_simp [palindromic_two_ne_zero hp2]
      ring

theorem palindromicEigenCoordinates_synthesis {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (v : Fin p → ZMod p) :
    palindromicEigenCoordinatesLinear p (palindromicEigenSynthesisLinear p v) = v := by
  funext i
  by_cases hi : i.val = 0
  · simp [palindromicEigenSynthesisLinear_apply,
      palindromicEigenCoordinatesLinear_apply, hi]
  · have hip : 0 < i.val := Nat.pos_of_ne_zero hi
    have hm0 : (palindromicPairMate p i).val ≠ 0 :=
      Nat.ne_of_gt (palindromicPairMate_pos i hip)
    by_cases hlo : i.val ≤ (p - 1) / 2
    · have hmhi : ¬ (palindromicPairMate p i).val ≤ (p - 1) / 2 :=
        not_le_of_gt (palindromicPairMate_upper hp2 i hip hlo)
      simp only [palindromicEigenSynthesisLinear_apply,
        palindromicEigenCoordinatesLinear_apply, hi, hlo, hm0, hmhi,
        ite_false, ite_true, palindromicPairMate_invol]
      field_simp [palindromic_two_ne_zero hp2]
      ring
    · have hmlo := palindromicPairMate_lower hp2 i (lt_of_not_ge hlo)
      simp only [palindromicEigenSynthesisLinear_apply,
        palindromicEigenCoordinatesLinear_apply, hi, hlo, hm0, hmlo,
        ite_false, ite_true, palindromicPairMate_invol]
      field_simp [palindromic_two_ne_zero hp2]
      ring

def palindromicEigenCoordinates {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (Fin p → ZMod p) ≃ₗ[ZMod p] (Fin p → ZMod p) where
  __ := palindromicEigenCoordinatesLinear p
  toFun := palindromicEigenCoordinatesLinear p
  invFun := palindromicEigenSynthesisLinear p
  left_inv := palindromicEigenSynthesis_coordinates hp2
  right_inv := palindromicEigenCoordinates_synthesis hp2

def palindromicReversalEigenbasis {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    Basis (Fin p) (ZMod p) (Fin p → ZMod p) :=
  Basis.ofEquivFun (palindromicEigenCoordinates hp2)

theorem palindromicReversalEigenbasis_equivFun {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) :
    (palindromicReversalEigenbasis hp2).equivFun = palindromicEigenCoordinates hp2 :=
  Basis.equivFun_ofEquivFun _

theorem palindromicReversalEigenbasis_apply {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (i : Fin p) :
    palindromicReversalEigenbasis hp2 i =
      palindromicEigenSynthesisLinear p (Pi.single i 1) := by
  have h := ((palindromicReversalEigenbasis hp2).equivFun_symm_apply
    (Pi.single i (1 : ZMod p))).symm
  simpa [palindromicReversalEigenbasis_equivFun, palindromicEigenCoordinates,
    Pi.single_apply, ite_smul] using h

def palindromicEigenChange (p : ℕ) [Fact p.Prime] :
    Matrix (Fin p) (Fin p) (ZMod p) :=
  LinearMap.toMatrix' (palindromicEigenSynthesisLinear p)

def palindromicEigenChangeInv (p : ℕ) [Fact p.Prime] :
    Matrix (Fin p) (Fin p) (ZMod p) :=
  LinearMap.toMatrix' (palindromicEigenCoordinatesLinear p)

theorem palindromicEigenChange_mulVec (p : ℕ) [Fact p.Prime]
    (v : Fin p → ZMod p) :
    (palindromicEigenChange p).mulVec v = palindromicEigenSynthesisLinear p v := by
  exact LinearMap.toMatrix'_mulVec _ _

theorem palindromicEigenChangeInv_mulVec (p : ℕ) [Fact p.Prime]
    (v : Fin p → ZMod p) :
    (palindromicEigenChangeInv p).mulVec v = palindromicEigenCoordinatesLinear p v := by
  exact LinearMap.toMatrix'_mulVec _ _

theorem palindromicEigenChange_mul_inv {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    palindromicEigenChange p * palindromicEigenChangeInv p = 1 := by
  apply Matrix.toLin'.injective
  simp only [palindromicEigenChange, palindromicEigenChangeInv,
    Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_one]
  apply LinearMap.ext
  intro v
  exact palindromicEigenSynthesis_coordinates hp2 v

theorem palindromicEigenChangeInv_mul {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    palindromicEigenChangeInv p * palindromicEigenChange p = 1 := by
  apply Matrix.toLin'.injective
  simp only [palindromicEigenChange, palindromicEigenChangeInv,
    Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_one]
  apply LinearMap.ext
  intro v
  exact palindromicEigenCoordinates_synthesis hp2 v

theorem palindromicReversal_transpose_mulVec_apply (p : ℕ)
    (v : Fin p → ZMod p) (i : Fin p) :
    ((palindromicReversalMatrix p)ᵀ).mulVec v i =
      if i.val = 0 then 0 else v (palindromicPairMate p i) := by
  by_cases hi : i.val = 0
  · simp [Matrix.mulVec_apply_eq_sum, Matrix.transpose_apply,
      palindromicReversalMatrix_column_zero i hi, hi]
  · have hip : 0 < i.val := Nat.pos_of_ne_zero hi
    simp [Matrix.mulVec_apply_eq_sum, Matrix.transpose_apply,
      palindromicReversalMatrix_column_pos i hip, palindromicPairMate_of_pos i hip,
      hi, ite_mul]

theorem palindromicEigenCoordinates_reversal_synthesis {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (v : Fin p → ZMod p) :
    palindromicEigenCoordinatesLinear p
        (((palindromicReversalMatrix p)ᵀ).mulVec (palindromicEigenSynthesisLinear p v)) =
      fun i => palindromicEigenLambda p i * v i := by
  funext i
  by_cases hi : i.val = 0
  · simp [palindromicEigenCoordinatesLinear_apply,
      palindromicReversal_transpose_mulVec_apply, palindromicEigenLambda, hi]
  · have hip : 0 < i.val := Nat.pos_of_ne_zero hi
    have hm0 : (palindromicPairMate p i).val ≠ 0 :=
      Nat.ne_of_gt (palindromicPairMate_pos i hip)
    by_cases hlo : i.val ≤ (p - 1) / 2
    · have hmhi : ¬ (palindromicPairMate p i).val ≤ (p - 1) / 2 :=
        not_le_of_gt (palindromicPairMate_upper hp2 i hip hlo)
      simp only [palindromicEigenCoordinatesLinear_apply,
        palindromicReversal_transpose_mulVec_apply, palindromicEigenSynthesisLinear_apply,
        palindromicEigenLambda, hi, hlo, hm0, hmhi, ite_false, ite_true,
        palindromicPairMate_invol]
      field_simp [palindromic_two_ne_zero hp2]
      ring
    · have hmlo := palindromicPairMate_lower hp2 i (lt_of_not_ge hlo)
      simp only [palindromicEigenCoordinatesLinear_apply,
        palindromicReversal_transpose_mulVec_apply, palindromicEigenSynthesisLinear_apply,
        palindromicEigenLambda, hi, hlo, hm0, hmlo, ite_false, ite_true,
        palindromicPairMate_invol]
      field_simp [palindromic_two_ne_zero hp2]
      ring

theorem palindromicReversalEigenbasis_eigenvector {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (i : Fin p) :
    ((palindromicReversalMatrix p)ᵀ).mulVec (palindromicReversalEigenbasis hp2 i) =
      palindromicEigenLambda p i • palindromicReversalEigenbasis hp2 i := by
  apply (palindromicEigenCoordinates hp2).injective
  change palindromicEigenCoordinatesLinear p
      (((palindromicReversalMatrix p)ᵀ).mulVec (palindromicReversalEigenbasis hp2 i)) =
    palindromicEigenCoordinatesLinear p
      (palindromicEigenLambda p i • palindromicReversalEigenbasis hp2 i)
  simp only [palindromicReversalEigenbasis_apply]
  rw [palindromicEigenCoordinates_reversal_synthesis hp2,
    map_smul, palindromicEigenCoordinates_synthesis hp2]
  funext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [hji]

theorem palindromicEigenChange_diagonalizes {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    palindromicEigenChangeInv p * (palindromicReversalMatrix p)ᵀ *
        palindromicEigenChange p = Matrix.diagonal (palindromicEigenLambda p) := by
  apply Matrix.toLin'.injective
  simp only [palindromicEigenChange, palindromicEigenChangeInv,
    Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
  apply LinearMap.ext
  intro v
  change palindromicEigenCoordinatesLinear p
      (((palindromicReversalMatrix p)ᵀ).mulVec (palindromicEigenSynthesisLinear p v)) =
    (Matrix.diagonal (palindromicEigenLambda p)).mulVec v
  rw [palindromicEigenCoordinates_reversal_synthesis hp2]
  funext i
  simp [Matrix.mulVec_apply_eq_sum, Matrix.diagonal, ite_mul]

end InternalCatalan




open scoped BigOperators

namespace InternalCatalan

theorem palindromicEigenvalue_product {R : Type*} [CommMonoid R]
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (f : ZMod p → R) :
    (∏ i : Fin p, f (palindromicEigenLambda p i)) =
      f 0 * (f 1) ^ ((p - 1) / 2) * (f (-1)) ^ ((p - 1) / 2) := by
  let m : ℕ := (p - 1) / 2
  let F : ℕ → R := fun i => if i = 0 then f 0 else if i ≤ m then f 1 else f (-1)
  have hF (i : Fin p) : f (palindromicEigenLambda p i) = F i.val := by
    dsimp [palindromicEigenLambda, F, m]
    split_ifs <;> rfl
  have hp : p = m + m + 1 := by
    have h := palindromic_prime_card_split hp2
    dsimp [m]
    omega
  have hfirst : (∏ i ∈ Finset.range m, F (i + 1)) = (f 1) ^ m := by
    calc
      _ = ∏ _i ∈ Finset.range m, f 1 := by
        apply Finset.prod_congr rfl
        intro i hi
        have hi' := Finset.mem_range.mp hi
        simp [F, show i + 1 ≤ m by omega]
      _ = _ := by simp
  have hlast : (∏ i ∈ Finset.range m, F (m + i + 1)) = (f (-1)) ^ m := by
    calc
      _ = ∏ _i ∈ Finset.range m, f (-1) := by
        apply Finset.prod_congr rfl
        intro i _
        simp [F, show ¬m + i + 1 ≤ m by omega]
      _ = _ := by simp
  calc
    (∏ i : Fin p, f (palindromicEigenLambda p i)) = ∏ i : Fin p, F i.val := by
      apply Finset.prod_congr rfl
      intro i _
      exact hF i
    _ = ∏ i ∈ Finset.range p, F i := Fin.prod_univ_eq_prod_range F p
    _ = ∏ i ∈ Finset.range (m + m + 1), F i :=
      congrArg (fun k => ∏ i ∈ Finset.range k, F i) hp
    _ = ((∏ i ∈ Finset.range m, F (i + 1)) *
        (∏ i ∈ Finset.range m, F (m + i + 1))) * F 0 := by
      rw [Finset.prod_range_succ', Finset.prod_range_add]
    _ = f 0 * (f 1) ^ m * (f (-1)) ^ m := by
      rw [hfirst, hlast, show F 0 = f 0 by simp [F]]
      ac_rfl

end InternalCatalan

end



noncomputable section
open scoped BigOperators Matrix

namespace InternalCatalan

section CoordinateKernel

variable {K ι : Type*} [Field K] [DecidableEq K] [Fintype ι]

omit [DecidableEq K] [Fintype ι] in
private theorem coordinate_zero_off_eigenvalue
    (e : (ι → K) ≃ₗ[K] (ι → K)) (f : (ι → K) →ₗ[K] (ι → K))
    (lambda : ι → K)
    (hdiag : ∀ v i, e (f v) i = lambda i * e v i)
    (mu : K) (x : LinearMap.ker (f - mu • LinearMap.id))
    (i : ι) (hi : lambda i ≠ mu) : e (x : ι → K) i = 0 := by
  have hx : f (x : ι → K) = mu • (x : ι → K) := by
    have hx := x.property
    change f (x : ι → K) - mu • (x : ι → K) = 0 at hx
    exact sub_eq_zero.mp hx
  have hcoord : lambda i * e (x : ι → K) i = mu * e (x : ι → K) i := by
    rw [← hdiag, hx]
    simp
  have hmul : (lambda i - mu) * e (x : ι → K) i = 0 := by
    rw [sub_mul, hcoord, sub_self]
  exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hi)

private def eigenKernelCoordinateEquiv
    (e : (ι → K) ≃ₗ[K] (ι → K)) (f : (ι → K) →ₗ[K] (ι → K))
    (lambda : ι → K)
    (hdiag : ∀ v i, e (f v) i = lambda i * e v i) (mu : K) :
    LinearMap.ker (f - mu • LinearMap.id) ≃ₗ[K]
      ({i : ι // lambda i = mu} → K) := by
  classical
  let restrict : LinearMap.ker (f - mu • LinearMap.id) →ₗ[K]
      ({i : ι // lambda i = mu} → K) := {
    toFun := fun x i => e (x : ι → K) i.val
    map_add' := by
      intro x y
      funext i
      exact congrFun (map_add e (x : ι → K) (y : ι → K)) i.val
    map_smul' := by
      intro c x
      funext i
      exact congrFun (map_smul e c (x : ι → K)) i.val }
  let extend : ({i : ι // lambda i = mu} → K) →
      LinearMap.ker (f - mu • LinearMap.id) := fun y => by
    let w : ι → K := fun i => if hi : lambda i = mu then y ⟨i, hi⟩ else 0
    refine ⟨e.symm w, ?_⟩
    change f (e.symm w) - mu • e.symm w = 0
    apply e.injective
    rw [map_sub, map_smul, map_zero]
    funext i
    change e (f (e.symm w)) i - mu * e (e.symm w) i = 0
    rw [hdiag, e.apply_symm_apply]
    dsimp [w]
    split_ifs with hi
    · rw [hi, sub_self]
    · simp
  exact {
    restrict with
    toFun := restrict
    invFun := extend
    left_inv := by
      intro x
      apply Subtype.ext
      apply e.injective
      change e (e.symm (fun i =>
        if hi : lambda i = mu then e (x : ι → K) i else 0)) = e (x : ι → K)
      rw [e.apply_symm_apply]
      funext i
      by_cases hi : lambda i = mu
      · simp [hi]
      · simpa [hi] using
          (coordinate_zero_off_eigenvalue e f lambda hdiag mu x i hi).symm
    right_inv := by
      intro y
      funext i
      change e (e.symm (fun j =>
        if hj : lambda j = mu then y ⟨j, hj⟩ else 0)) i.val = y i
      rw [e.apply_symm_apply]
      simp [i.property] }

private theorem finrank_eigenKernel_of_coordinates
    (e : (ι → K) ≃ₗ[K] (ι → K)) (f : (ι → K) →ₗ[K] (ι → K))
    (lambda : ι → K)
    (hdiag : ∀ v i, e (f v) i = lambda i * e v i) (mu : K) :
    Module.finrank K (LinearMap.ker (f - mu • LinearMap.id)) =
      Fintype.card {i : ι // lambda i = mu} := by
  classical
  calc
    _ = Module.finrank K ({i : ι // lambda i = mu} → K) :=
      (eigenKernelCoordinateEquiv e f lambda hdiag mu).finrank_eq
    _ = _ := Module.finrank_fintype_fun_eq_card K

end CoordinateKernel

def palindromicReversalEigenKernel (p : ℕ) (mu : ZMod p) :
    Submodule (ZMod p) (Fin p → ZMod p) :=
  LinearMap.ker ((palindromicReversalMatrix p).mulVecLin - mu • LinearMap.id)

theorem palindromicEigenCoordinates_reversal {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (v : Fin p → ZMod p) (i : Fin p) :
    palindromicEigenCoordinates hp2 ((palindromicReversalMatrix p).mulVecLin v) i =
      palindromicEigenLambda p i * palindromicEigenCoordinates hp2 v i := by
  have h := congrFun (palindromicEigenCoordinates_reversal_synthesis hp2
    (palindromicEigenCoordinatesLinear p v)) i
  rw [palindromicEigenSynthesis_coordinates hp2,
    palindromicReversalMatrix_transpose] at h
  exact h

theorem finrank_palindromicReversalEigenKernel {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (mu : ZMod p) :
    Module.finrank (ZMod p) (palindromicReversalEigenKernel p mu) =
      Fintype.card {i : Fin p // palindromicEigenLambda p i = mu} := by
  classical
  exact finrank_eigenKernel_of_coordinates (palindromicEigenCoordinates hp2)
    (palindromicReversalMatrix p).mulVecLin (palindromicEigenLambda p)
    (palindromicEigenCoordinates_reversal hp2) mu

private theorem palindromic_neg_one_ne_one {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) : (-1 : ZMod p) ≠ 1 := by
  intro h
  apply palindromic_two_ne_zero hp2
  calc
    (2 : ZMod p) = 1 - (-1) := by ring
    _ = 1 - 1 := by rw [h]
    _ = 0 := sub_self _

theorem palindromicEigenLambda_eq_zero_iff {p : ℕ} [Fact p.Prime] (i : Fin p) :
    palindromicEigenLambda p i = 0 ↔ i.val = 0 := by
  by_cases hi : i.val = 0
  · simp [palindromicEigenLambda, hi]
  · by_cases hlo : i.val ≤ (p - 1) / 2 <;>
      simp [palindromicEigenLambda, hi, hlo]

theorem palindromicEigenLambda_eq_one_iff {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (i : Fin p) :
    palindromicEigenLambda p i = 1 ↔ 0 < i.val ∧ i.val ≤ (p - 1) / 2 := by
  by_cases hi : i.val = 0
  · simp [palindromicEigenLambda, hi]
  · have hip : 0 < i.val := Nat.pos_of_ne_zero hi
    by_cases hlo : i.val ≤ (p - 1) / 2 <;>
      simp [palindromicEigenLambda, hi, hip, hlo, palindromic_neg_one_ne_one hp2]

theorem palindromicEigenLambda_eq_neg_one_iff {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (i : Fin p) :
    palindromicEigenLambda p i = -1 ↔ (p - 1) / 2 < i.val := by
  have hone : (1 : ZMod p) ≠ -1 := Ne.symm (palindromic_neg_one_ne_one hp2)
  by_cases hi : i.val = 0
  · simp [palindromicEigenLambda, hi]
  · by_cases hlo : i.val ≤ (p - 1) / 2
    · simp [palindromicEigenLambda, hi, hlo, hone, not_lt.mpr hlo]
    · simp [palindromicEigenLambda, hi, hlo, lt_of_not_ge hlo]

private def palindromicZeroEigenIndexEquiv {p : ℕ} [Fact p.Prime] :
    {i : Fin p // palindromicEigenLambda p i = 0} ≃ Fin 1 where
  toFun := fun _ => 0
  invFun := fun _ => ⟨⟨0, (Fact.out : p.Prime).pos⟩, by
    simp [palindromicEigenLambda]⟩
  left_inv := by
    intro i
    apply Subtype.ext
    apply Fin.ext
    exact ((palindromicEigenLambda_eq_zero_iff i.val).mp i.property).symm
  right_inv := by
    intro i
    apply Fin.ext
    have := i.isLt
    dsimp
    omega

private def palindromicPlusEigenIndexEquiv {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    {i : Fin p // palindromicEigenLambda p i = 1} ≃ Fin ((p - 1) / 2) where
  toFun := fun i => ⟨i.val.val - 1, by
    obtain ⟨hpos, hle⟩ := (palindromicEigenLambda_eq_one_iff hp2 i.val).mp i.property
    omega⟩
  invFun := fun j => ⟨⟨j.val + 1, by
    have := j.isLt
    have := palindromic_prime_card_split hp2
    omega⟩, by
      apply (palindromicEigenLambda_eq_one_iff hp2 _).mpr
      have := j.isLt
      constructor <;> dsimp <;> omega⟩
  left_inv := by
    intro i
    apply Subtype.ext
    apply Fin.ext
    have := ((palindromicEigenLambda_eq_one_iff hp2 i.val).mp i.property).1
    dsimp
    omega
  right_inv := by
    intro i
    apply Fin.ext
    dsimp

private def palindromicMinusEigenIndexEquiv {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    {i : Fin p // palindromicEigenLambda p i = -1} ≃ Fin ((p - 1) / 2) where
  toFun := fun i => ⟨i.val.val - ((p - 1) / 2 + 1), by
    have := (palindromicEigenLambda_eq_neg_one_iff hp2 i.val).mp i.property
    have := i.val.isLt
    have := palindromic_prime_card_split hp2
    omega⟩
  invFun := fun j => ⟨⟨j.val + ((p - 1) / 2 + 1), by
    have := j.isLt
    have := palindromic_prime_card_split hp2
    omega⟩, by
      apply (palindromicEigenLambda_eq_neg_one_iff hp2 _).mpr
      dsimp
      omega⟩
  left_inv := by
    intro i
    apply Subtype.ext
    apply Fin.ext
    have := (palindromicEigenLambda_eq_neg_one_iff hp2 i.val).mp i.property
    dsimp
    omega
  right_inv := by
    intro i
    apply Fin.ext
    dsimp
    omega

theorem finrank_palindromicReversalEigenKernel_zero {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) :
    Module.finrank (ZMod p) (palindromicReversalEigenKernel p 0) = 1 := by
  classical
  rw [finrank_palindromicReversalEigenKernel hp2]
  simpa using Fintype.card_congr (palindromicZeroEigenIndexEquiv (p := p))

theorem finrank_palindromicReversalEigenKernel_one {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) :
    Module.finrank (ZMod p) (palindromicReversalEigenKernel p 1) = (p - 1) / 2 := by
  classical
  rw [finrank_palindromicReversalEigenKernel hp2]
  simpa using Fintype.card_congr (palindromicPlusEigenIndexEquiv hp2)

theorem finrank_palindromicReversalEigenKernel_neg_one {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) :
    Module.finrank (ZMod p) (palindromicReversalEigenKernel p (-1)) = (p - 1) / 2 := by
  classical
  rw [finrank_palindromicReversalEigenKernel hp2]
  simpa using Fintype.card_congr (palindromicMinusEigenIndexEquiv hp2)

theorem palindromicReversal_charpoly_eq_product {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) :
    (palindromicReversalMatrix p).charpoly =
      ∏ i : Fin p, (Polynomial.X - Polynomial.C (palindromicEigenLambda p i)) := by
  calc
    _ = ((palindromicReversalMatrix p)ᵀ).charpoly :=
      (Matrix.charpoly_transpose _).symm
    _ = (palindromicEigenChange p *
        (palindromicEigenChangeInv p * (palindromicReversalMatrix p)ᵀ)).charpoly := by
      rw [← mul_assoc, palindromicEigenChange_mul_inv hp2, one_mul]
    _ = (palindromicEigenChangeInv p * (palindromicReversalMatrix p)ᵀ *
        palindromicEigenChange p).charpoly :=
      Matrix.charpoly_mul_comm _ _
    _ = (Matrix.diagonal (palindromicEigenLambda p)).charpoly :=
      congrArg Matrix.charpoly (palindromicEigenChange_diagonalizes hp2)
    _ = _ := Matrix.charpoly_diagonal _

theorem palindromicReversal_charpoly {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) :
    (palindromicReversalMatrix p).charpoly =
      Polynomial.X * (Polynomial.X - 1) ^ ((p - 1) / 2) *
        (Polynomial.X + 1) ^ ((p - 1) / 2) := by
  rw [palindromicReversal_charpoly_eq_product hp2,
    palindromicEigenvalue_product hp2
      (fun z : ZMod p => (Polynomial.X : Polynomial (ZMod p)) - Polynomial.C z)]
  simp

end InternalCatalan

end

end OAI
