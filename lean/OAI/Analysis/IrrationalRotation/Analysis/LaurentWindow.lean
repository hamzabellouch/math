import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

namespace OAI

noncomputable section

namespace Invariant233.LaurentWindow

open Polynomial LaurentPolynomial

variable {R : Type*} [Semiring R]

@[simp] theorem coeff_trunc (A : LaurentPolynomial R) (n : ℕ) :
    (LaurentPolynomial.trunc A).coeff n = A.coeff (n : ℤ) := by
  rfl

@[simp] theorem coeff_trunc_mul_T (A : LaurentPolynomial R) (k : ℤ) (n : ℕ) :
    (LaurentPolynomial.trunc (A * LaurentPolynomial.T k)).coeff n =
      A.coeff ((n : ℤ) - k) := by
  rw [coeff_trunc, LaurentPolynomial.T, AddMonoidAlgebra.coeff_mul_single_apply]
  simp only [mul_one, sub_eq_add_neg]

@[simp] theorem coeff_toLaurent_nat (p : Polynomial R) (n : ℕ) :
    p.toLaurent.coeff (n : ℤ) = p.coeff n := by
  change (Finsupp.mapDomain (fun n : ℕ => (n : ℤ)) p.toFinsupp.coeff) n = _
  exact Finsupp.mapDomain_apply_of_injective Nat.cast_injective _ n

@[simp] theorem coeff_toLaurent_neg (p : Polynomial R) (n : ℤ) (hn : n < 0) :
    p.toLaurent.coeff n = 0 := by
  change (Finsupp.mapDomain (fun n : ℕ => (n : ℤ)) p.toFinsupp.coeff) n = 0
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨m, rfl⟩
  exact (not_lt_of_ge (Int.natCast_nonneg m)) hn

@[simp] theorem coeff_mul_T (A : LaurentPolynomial R) (k n : ℤ) :
    (A * LaurentPolynomial.T k).coeff n = A.coeff (n - k) := by
  rw [LaurentPolynomial.T, AddMonoidAlgebra.coeff_mul_single_apply]
  simp only [mul_one, sub_eq_add_neg]

theorem toLaurent_trunc_of_nonnegative (A : LaurentPolynomial R)
    (hA : ∀ n : ℤ, n < 0 → A.coeff n = 0) :
    (LaurentPolynomial.trunc A).toLaurent = A := by
  ext n
  by_cases hn : 0 ≤ n
  · lift n to ℕ using hn
    simp only [coeff_toLaurent_nat, coeff_trunc]
  · rw [coeff_toLaurent_neg _ n (lt_of_not_ge hn), hA n (lt_of_not_ge hn)]

theorem toLaurent_trunc_shift (K : ℕ) (A : LaurentPolynomial R)
    (hA : ∀ n : ℤ, n < -(K : ℤ) → A.coeff n = 0) :
    (LaurentPolynomial.trunc (A * LaurentPolynomial.T (K : ℤ))).toLaurent =
      A * LaurentPolynomial.T (K : ℤ) := by
  apply toLaurent_trunc_of_nonnegative
  intro n hn
  rw [coeff_mul_T]
  apply hA
  omega

theorem coeff_trunc_shift_above (K n : ℕ) (A : LaurentPolynomial R)
    (hA : ∀ i : ℤ, (K : ℤ) < i → A.coeff i = 0) (hn : 2 * K < n) :
    (LaurentPolynomial.trunc (A * LaurentPolynomial.T (K : ℤ))).coeff n = 0 := by
  rw [coeff_trunc_mul_T]
  apply hA
  omega

theorem coeff_fin_sum_monomial (N : ℕ) (a : Fin N → R) (i : Fin N) :
    (∑ j : Fin N, Polynomial.monomial (j : ℕ) (a j)).coeff (i : ℕ) = a i := by
  classical
  simp [Polynomial.coeff_monomial, Fin.val_inj]

theorem coeff_fin_sum_monomial_above (N n : ℕ) (a : Fin N → R) (hn : N ≤ n) :
    (∑ j : Fin N, Polynomial.monomial (j : ℕ) (a j)).coeff n = 0 := by
  classical
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  apply Finset.sum_eq_zero
  intro j _
  rw [ite_eq_right]
  omega

theorem trunc_shift_eq_fin_sum (K : ℕ) (A : LaurentPolynomial R)
    (hA : ∀ i : ℤ, (K : ℤ) < i → A.coeff i = 0) :
    LaurentPolynomial.trunc (A * LaurentPolynomial.T (K : ℤ)) =
      ∑ i : Fin (2 * K + 1), Polynomial.monomial (i : ℕ)
        (A.coeff ((i : ℤ) - (K : ℤ))) := by
  ext n
  by_cases hn : n < 2 * K + 1
  · exact (coeff_trunc_mul_T A (K : ℤ) n).trans
      (coeff_fin_sum_monomial (2 * K + 1)
        (fun i : Fin (2 * K + 1) => A.coeff ((i : ℤ) - (K : ℤ))) ⟨n, hn⟩).symm
  · rw [coeff_fin_sum_monomial_above _ n _ (le_of_not_gt hn),
      coeff_trunc_shift_above K n A hA (by omega)]

theorem coeff_window_sum (s : Finset ℤ) (a : ℤ → R) (n : ℤ) :
    (∑ i ∈ s, (AddMonoidAlgebra.single i (a i) : LaurentPolynomial R)).coeff n =
      if n ∈ s then a n else 0 := by
  classical
  simp only [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  simp

theorem coeff_window_product (s t : Finset ℤ) (a b : ℤ → R) (n : ℤ) :
    ((∑ i ∈ s, (AddMonoidAlgebra.single i (a i) : LaurentPolynomial R)) *
      (∑ j ∈ t, (AddMonoidAlgebra.single j (b j) : LaurentPolynomial R))).coeff n =
      ∑ i ∈ s, if n - i ∈ t then a i * b (n - i) else 0 := by
  classical
  simp only [Finset.sum_mul, Finset.mul_sum, AddMonoidAlgebra.single_mul_single,
    AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp_rw [show ∀ j : ℤ, i + j = n ↔ j = n - i by intro j; omega]
  simp

theorem coeff_symmetric_window_product (K : ℕ) (a b : ℤ → R) (n : ℤ) :
    ((∑ i ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
        (AddMonoidAlgebra.single i (a i) : LaurentPolynomial R)) *
      (∑ j ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
        (AddMonoidAlgebra.single j (b j) : LaurentPolynomial R))).coeff (-n) =
      ∑ i ∈ (Finset.Icc (-(K : ℤ)) (K : ℤ)).filter (fun i => |n + i| ≤ (K : ℤ)),
        a i * b (-n - i) := by
  classical
  rw [coeff_window_product, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  have hiff : -n - i ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) ↔ |n + i| ≤ (K : ℤ) := by
    simp only [Finset.mem_Icc, abs_le]
    omega
  simp only [hiff]


variable {S : Type*} [CommSemiring S]

theorem coeff_shifted_product (K n : ℕ) (A B : LaurentPolynomial S)
    (hA : ∀ i : ℤ, i < -(K : ℤ) → A.coeff i = 0)
    (hB : ∀ i : ℤ, i < -(K : ℤ) → B.coeff i = 0) :
    ((LaurentPolynomial.trunc (A * LaurentPolynomial.T (K : ℤ))) *
      (LaurentPolynomial.trunc (B * LaurentPolynomial.T (K : ℤ)))).coeff n =
      (A * B).coeff ((n : ℤ) - 2 * (K : ℤ)) := by
  rw [← coeff_toLaurent_nat, map_mul,
    toLaurent_trunc_shift K A hA, toLaurent_trunc_shift K B hB]
  rw [mul_mul_mul_comm, ← LaurentPolynomial.T_add, coeff_mul_T]
  congr 1
  omega


end Invariant233.LaurentWindow

end

end OAI
