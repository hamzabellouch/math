import OAI.LinearAlgebra.MatrixMultiplication.Tensor.FieldCoefficientExtraction
import Mathlib.Algebra.BigOperators.Option
import Mathlib.Tactic.IntervalCases

namespace OAI

/-! Coppersmith–Winograd tensors, tensor powers and local restrictions. -/

noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation Polynomial

namespace MatrixMultiplication.FieldCW

section Integral

variable (F : Type*) [CommRing F] (q : ℕ)

def zeroForm (x : Fin (q + 2)) : F := if x.val = 0 then 1 else 0

def interiorForm (i : Fin q) (x : Fin (q + 2)) : F :=
  if x.val = i.val + 1 then 1 else 0

def lastForm (x : Fin (q + 2)) : F := if x.val = q + 1 then 1 else 0

def interiorSum (x : Fin (q + 2)) : F := ∑ i, interiorForm F q i x

def tensor : Tensor F (Fin (q + 2)) (Fin (q + 2)) (Fin (q + 2)) :=
  fun x y z =>
    (∑ i : Fin q,
      (zeroForm F q x * interiorForm F q i y * interiorForm F q i z +
      interiorForm F q i x * zeroForm F q y * interiorForm F q i z +
      interiorForm F q i x * interiorForm F q i y * zeroForm F q z)) +
    lastForm F q x * zeroForm F q y * zeroForm F q z +
    zeroForm F q x * lastForm F q y * zeroForm F q z +
    zeroForm F q x * zeroForm F q y * lastForm F q z

theorem interior_pair_sum (x y : Fin (q + 2)) :
    (∑ i : Fin q, interiorForm F q i x * interiorForm F q i y) =
      if x = y ∧ 1 ≤ x.val ∧ x.val ≤ q then 1 else 0 := by
  classical
  by_cases hx : 1 ≤ x.val ∧ x.val ≤ q
  · let i : Fin q := ⟨x.val - 1, by omega⟩
    rw [Finset.sum_eq_single i]
    · simp [interiorForm, i, Nat.sub_add_cancel hx.1, hx.1, hx.2,
        Fin.ext_iff, eq_comm]
    · intro j hj hji
      have hne : x.val ≠ j.val + 1 := by
        intro h
        apply hji
        apply Fin.ext
        dsimp [i]
        omega
      simp [interiorForm, hne]
    · simp
  · have hsum : (∑ i : Fin q, interiorForm F q i x * interiorForm F q i y) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hne : x.val ≠ i.val + 1 := by
        intro h
        apply hx
        have := i.isLt
        omega
      simp [interiorForm, hne]
    rw [hsum, ite_eq_right]
    intro h
    exact hx ⟨h.2.1, h.2.2⟩

theorem tensor_zero_side (x y z : Fin (q + 2)) (hx : x.val = 0) :
    tensor F q x y z =
      if (y.val = 0 ∧ z.val = q + 1) ∨
          (y.val = q + 1 ∧ z.val = 0) ∨
          (1 ≤ y.val ∧ y.val ≤ q ∧ y = z) then 1 else 0 := by
  have hx0 : zeroForm F q x = 1 := by simp [zeroForm, hx]
  have hxlast : lastForm F q x = 0 := by simp [lastForm, hx]
  have hxmid (i : Fin q) : interiorForm F q i x = 0 := by
    simp [interiorForm, hx]
  simp only [tensor, hx0, hxlast, hxmid, one_mul, zero_mul, add_zero]
  rw [interior_pair_sum]
  by_cases hy0 : y.val = 0
  · simp [zeroForm, lastForm, hy0]
  · by_cases hylast : y.val = q + 1
    · have hyinter : ¬ y.val ≤ q := by omega
      simp [zeroForm, lastForm, hylast]
    · have hylo : 1 ≤ y.val := by omega
      have hyhi : y.val ≤ q := by have := y.isLt; omega
      simp [zeroForm, lastForm, hy0, hylast, hylo, hyhi]

theorem tensor_cyclic (x y z : Fin (q + 2)) :
    tensor F q x y z = tensor F q y z x := by
  unfold tensor
  have hsum :
      (∑ i : Fin q,
        (zeroForm F q x * interiorForm F q i y * interiorForm F q i z +
        interiorForm F q i x * zeroForm F q y * interiorForm F q i z +
        interiorForm F q i x * interiorForm F q i y * zeroForm F q z)) =
      ∑ i : Fin q,
        (zeroForm F q y * interiorForm F q i z * interiorForm F q i x +
        interiorForm F q i y * zeroForm F q z * interiorForm F q i x +
        interiorForm F q i y * interiorForm F q i z * zeroForm F q x) := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsum]
  ring

def form (e : ℕ) (u v : F) : Polynomial F := C u + X ^ e * C v

def left : Option (Option (Fin q)) → Fin (q + 2) → Polynomial F
  | some (some i), x => X * form F 1 (zeroForm F q x) (interiorForm F q i x)
  | some none, x => -form F 2 (zeroForm F q x) (interiorSum F q x)
  | none, x => (1 - C (q : F) * X) * form F 3 (zeroForm F q x) (lastForm F q x)

def other : Option (Option (Fin q)) → Fin (q + 2) → Polynomial F
  | some (some i), x => form F 1 (zeroForm F q x) (interiorForm F q i x)
  | some none, x => form F 2 (zeroForm F q x) (interiorSum F q x)
  | none, x => form F 3 (zeroForm F q x) (lastForm F q x)

def polynomial : Tensor (Polynomial F) (Fin (q + 2)) (Fin (q + 2)) (Fin (q + 2)) :=
  fun x y z => ∑ i, Tensor.rankOne (left F q i) (other F q i) (other F q i) x y z

theorem rank_bound : Tensor.RankAtMost (polynomial F q) (q + 2) := by
  have h := Tensor.rankAtMost_sum_rankOne (left F q) (other F q) (other F q)
  simp only [Fintype.card_option, Fintype.card_fin, Nat.add_assoc] at h
  convert h using 1
  rfl

theorem polynomial_apply (x y z : Fin (q + 2)) :
    polynomial F q x y z =
      (∑ i : Fin q, X * form F 1 (zeroForm F q x) (interiorForm F q i x) *
        form F 1 (zeroForm F q y) (interiorForm F q i y) *
        form F 1 (zeroForm F q z) (interiorForm F q i z)) -
      form F 2 (zeroForm F q x) (interiorSum F q x) *
        form F 2 (zeroForm F q y) (interiorSum F q y) *
        form F 2 (zeroForm F q z) (interiorSum F q z) +
      (1 - C (q : F) * X) * form F 3 (zeroForm F q x) (lastForm F q x) *
        form F 3 (zeroForm F q y) (lastForm F q y) *
        form F 3 (zeroForm F q z) (lastForm F q z) := by
  simp only [polynomial, Fintype.sum_option, Tensor.rankOne, left, other]
  ring

private theorem coeff_mul_two (a b : Polynomial F) :
    (a * b).coeff 2 = a.coeff 0 * b.coeff 2 + a.coeff 1 * b.coeff 1 +
      a.coeff 2 * b.coeff 0 := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ, add_assoc]

private theorem coeff_mul_three (a b : Polynomial F) :
    (a * b).coeff 3 = a.coeff 0 * b.coeff 3 + a.coeff 1 * b.coeff 2 +
      a.coeff 2 * b.coeff 1 + a.coeff 3 * b.coeff 0 := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ, add_assoc]

theorem vanishes (x y z : Fin (q + 2)) (k : ℕ) (hk : k < 3) :
    (polynomial F q x y z).coeff k = 0 := by
  interval_cases k <;>
    simp [polynomial_apply, Polynomial.mul_coeff_zero,
      Polynomial.mul_coeff_one, coeff_mul_two, form, Polynomial.coeff_add,
      Polynomial.coeff_sub, interiorSum,
      Polynomial.coeff_one, Polynomial.coeff_X,
      Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum] <;>
    simp only [mul_assoc, mul_comm] <;> ring_nf
  simp only [Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, mul_comm]
  ring

theorem leading (x y z : Fin (q + 2)) :
    (polynomial F q x y z).coeff 3 = tensor F q x y z := by
  simp [polynomial_apply, Polynomial.mul_coeff_zero,
    Polynomial.mul_coeff_one, coeff_mul_two, coeff_mul_three, form,
    Polynomial.coeff_add, Polynomial.coeff_sub,
    tensor, Polynomial.coeff_one, Polynomial.coeff_X,
    Finset.sum_add_distrib]
  simp only [mul_assoc, mul_comm, mul_left_comm]
  ring_nf
  simp only [Finset.sum_add_distrib, mul_assoc, mul_comm, mul_left_comm]
  ring

def degreeBound : ℕ := Finset.univ.sup fun xyz :
    Fin (q + 2) × Fin (q + 2) × Fin (q + 2) =>
      (polynomial F q xyz.1 xyz.2.1 xyz.2.2).natDegree

theorem degree_bound (x y z : Fin (q + 2)) :
    (polynomial F q x y z).degree ≤ degreeBound F q := by
  let f : (Fin (q + 2) × Fin (q + 2) × Fin (q + 2)) → ℕ :=
    fun xyz => (polynomial F q xyz.1 xyz.2.1 xyz.2.2).natDegree
  have h := Finset.le_sup (s := Finset.univ) (f := f) (b := (x, y, z))
    (Finset.mem_univ (x, y, z))
  exact Polynomial.degree_le_of_natDegree_le h

end Integral

variable (F : Type*) [Field F] (q : ℕ)

def approximation : Tensor.PolynomialApproximation (tensor F q) (q + 2) 3
    (degreeBound F q) where
  polynomial := polynomial F q
  rank_bound := rank_bound F q
  vanishes := vanishes F q
  leading := leading F q
  degree_bound := degree_bound F q

theorem rank_power (n : ℕ) :
    Tensor.RankAtMost (Tensor.power (tensor F q) n) ((3 * n + 1) ^ 2 * (q + 2) ^ n) :=
  FieldCoefficientExtraction.rank_power (approximation F q) n

end MatrixMultiplication.FieldCW

end

end OAI
