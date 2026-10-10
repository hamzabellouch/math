import OAI.Combinatorics.BalancedRyser.Incidence.Affine
import OAI.Combinatorics.BalancedRyser.Incidence.StabilityRootDivisibility

namespace OAI

namespace Balanced.StabilityPolynomial

open Polynomial
open scoped BigOperators Classical

variable {F : Type*} [Field F]

theorem rootMultiplicity_linear_product
    {ι : Type*} (s : Finset ι) (a : ι → F) (c : F) :
    rootMultiplicity c (∏ i ∈ s, (X - C (a i))) =
      (s.filter fun i => a i = c).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hprod : (∏ j ∈ s, (X - C (a j) : F[X])) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun j _ => X_sub_C_ne_zero (a j)
    rw [Finset.prod_insert hi,
      rootMultiplicity_mul (mul_ne_zero (X_sub_C_ne_zero (a i)) hprod),
      rootMultiplicity_X_sub_C, ih]
    by_cases hc : a i = c
    · simp [hc, Finset.filter_insert, hi, Nat.add_comm]
    · simp [hc, Ne.symm hc, Finset.filter_insert]

theorem rootMultiplicity_le_natDegree (A : F[X]) (hA : A ≠ 0) (c : F) :
    rootMultiplicity c A ≤ A.natDegree := by
  have h := natDegree_le_of_dvd (pow_rootMultiplicity_dvd A c) hA
  simpa only [natDegree_pow, natDegree_X_sub_C, mul_one] using h

theorem power_dvd_linear_product_card_bound
    {ι : Type*} (s : Finset ι) (a : ι → F) {A : F[X]} (hA : A ≠ 0)
    (c : F) (n : ℕ)
    (hdiv : (X - C c) ^ n ∣ (∏ i ∈ s, (X - C (a i))) * A) :
    n ≤ (s.filter fun i => a i = c).card + A.natDegree := by
  classical
  have hprod : (∏ i ∈ s, (X - C (a i) : F[X])) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => X_sub_C_ne_zero (a i)
  have h := (le_rootMultiplicity_iff (mul_ne_zero hprod hA)).mpr hdiv
  rw [rootMultiplicity_mul (mul_ne_zero hprod hA), rootMultiplicity_linear_product] at h
  exact h.trans (Nat.add_le_add_left (rootMultiplicity_le_natDegree A hA c) _)

theorem large_fiber_of_power_dvd
    {ι : Type*} (s : Finset ι) (a : ι → F) {A : F[X]} (hA : A ≠ 0)
    (c : F) (n : ℕ)
    (hdiv : (X - C c) ^ n ∣ (∏ i ∈ s, (X - C (a i))) * A) :
    n - A.natDegree ≤ (s.filter fun i => a i = c).card := by
  have h := power_dvd_linear_product_card_bound s a hA c n hdiv
  omega

variable [Fintype F]

theorem linear_pow_card (c : F) :
    (X - C c : F[X]) ^ Fintype.card F = X ^ Fintype.card F - C c := by
  have h := map_sub (FiniteField.frobeniusAlgHom F F[X]) (X : F[X]) (C c)
  change (X - C c) ^ Fintype.card F =
    X ^ Fintype.card F - (C c) ^ Fintype.card F at h
  simpa only [← C_pow, FiniteField.pow_card] using h

theorem frobenius_linear_factorization (a b : F) (ha : a ≠ 0) :
    C a * X ^ Fintype.card F + C b =
      C a * (X - C (-b / a)) ^ Fintype.card F := by
  rw [linear_pow_card, mul_sub, ← C_mul]
  have h : a * (-b / a) = -b := by field_simp
  rw [h, C_neg]
  ring

theorem large_fiber_of_frobenius_divisor
    {ι : Type*} (s : Finset ι) (x : ι → F) {A : F[X]} (hA : A ≠ 0)
    (a b : F) (ha : a ≠ 0)
    (hdiv : C a * X ^ Fintype.card F + C b ∣
      (∏ i ∈ s, (X + C (x i))) * A) :
    Fintype.card F - A.natDegree ≤ (s.filter fun i => x i = b / a).card := by
  classical
  have hpower : (X - C (-b / a)) ^ Fintype.card F ∣
      (∏ i ∈ s, (X + C (x i))) * A := by
    apply dvd_trans _ hdiv
    rw [frobenius_linear_factorization a b ha]
    exact dvd_mul_left _ _
  have h := large_fiber_of_power_dvd s (fun i => -x i) hA (-b / a)
    (Fintype.card F) (by simpa only [C_neg, sub_neg_eq_add] using hpower)
  convert h using 1
  congr 1
  ext i
  simp only [Finset.mem_filter]
  rw [neg_div, neg_inj]

theorem redei_large_vertical_fiber
    (U : Finset (Point F)) {A : F[X]} (hA : A ≠ 0)
    (a b : F) (ha : a ≠ 0)
    (hdiv : C a * X ^ Fintype.card F + C b ∣
      (∏ p ∈ U, (X + C p.1)) * A) :
    Fintype.card F - A.natDegree ≤
      (U.filter fun p => OnLine p (none, b / a)).card := by
  have hfiber : U.filter (fun point => OnLine point (none, b / a)) =
      U.filter (fun point => point.1 = b / a) :=
    Finset.filter_congr fun point _ => Iff.rfl
  rw [hfiber]
  exact large_fiber_of_frobenius_divisor U Prod.fst hA a b ha hdiv

end Balanced.StabilityPolynomial

end OAI
