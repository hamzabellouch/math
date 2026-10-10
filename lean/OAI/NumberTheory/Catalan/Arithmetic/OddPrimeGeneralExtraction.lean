import OAI.NumberTheory.Catalan.Arithmetic.OddPrimeExtractionIndices
import OAI.NumberTheory.Catalan.Arithmetic.OddPrimeWeight

namespace OAI


namespace InternalCatalan

open Polynomial
open scoped BigOperators

theorem polynomial_eq_sum_range_of_coeff_ge_eq_zero {R : Type*} [CommSemiring R]
    (P : R[X]) (H : ℕ) (hP : ∀ i, H ≤ i → P.coeff i = 0) :
    P = ∑ i ∈ Finset.range H, C (P.coeff i) * X ^ i := by
  ext n
  simp only [finsetSum_coeff, coeff_C_mul_X_pow]
  by_cases hn : n < H
  · simp [Finset.mem_range, hn]
  · simp [Finset.mem_range, hn, hP n (by omega)]

theorem oddPrimeExtraction_coeff {p H : ℕ} (hp : 0 < p)
    (P : (ZMod p)[X]) (hP : ∀ i, H ≤ i → P.coeff i = 0) (n : ℕ) :
    (X * P * oddPrimeWeight p).coeff n =
      ∑ i ∈ Finset.range H, ∑ d ∈ Finset.range p,
        if n = i + 1 + d then P.coeff i * (oddPrimeWeight p).coeff d else 0 := by
  have hPexp := polynomial_eq_sum_range_of_coeff_ge_eq_zero P H hP
  have hEexp := polynomial_eq_sum_range_of_coeff_ge_eq_zero (oddPrimeWeight p) p
    (fun d hd => oddPrimeWeight_coeff_eq_zero_of_ge hp hd)
  have hXp : X * P = ∑ i ∈ Finset.range H, C (P.coeff i) * X ^ (i + 1) := by
    calc
      X * P = X * (∑ i ∈ Finset.range H, C (P.coeff i) * X ^ i) :=
        congrArg (fun Q : (ZMod p)[X] => X * Q) hPexp
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [pow_succ]
        ring
  have hpoly : X * P * oddPrimeWeight p =
      ∑ i ∈ Finset.range H, ∑ d ∈ Finset.range p,
        C (P.coeff i * (oddPrimeWeight p).coeff d) * X ^ (i + 1 + d) := by
    calc
      X * P * oddPrimeWeight p =
          (∑ i ∈ Finset.range H, C (P.coeff i) * X ^ (i + 1)) * oddPrimeWeight p :=
        congrArg (fun Q : (ZMod p)[X] => Q * oddPrimeWeight p) hXp
      _ = ∑ i ∈ Finset.range H,
          (C (P.coeff i) * X ^ (i + 1)) * oddPrimeWeight p := by rw [Finset.sum_mul]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        calc
          _ = (C (P.coeff i) * X ^ (i + 1)) *
              (∑ d ∈ Finset.range p, C ((oddPrimeWeight p).coeff d) * X ^ d) :=
            congrArg (fun Q : (ZMod p)[X] => (C (P.coeff i) * X ^ (i + 1)) * Q) hEexp
          _ = _ := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro d hd
            rw [map_mul, pow_add X (i + 1) d]
            ring
  rw [hpoly]
  simp only [finsetSum_coeff, coeff_C_mul_X_pow]

theorem oddPrime_P_coefficient_contraction {p B k ell : ℕ}
    (hp : 0 < p) (hell : ell < p) (P : (ZMod p)[X])
    (hP : ∀ i, B * p ≤ i → P.coeff i = 0) (f : ℤ → ZMod p) :
    (∑ i ∈ Finset.range (B * p),
      P.coeff i * (oddPrimeWeight p).coeff (oddPrimeDigitRemainder p i (k * p + ell)) *
        f (oddPrimeDigitRow p i (k * p + ell))) =
      ∑ v ∈ Finset.range (B + 1),
        (X * P * oddPrimeWeight p).coeff (v * p + ell) * f ((v : ℤ) - 1) := by
  have hsingle (i : ℕ) (hi : i ∈ Finset.range (B * p)) :
      (∑ d ∈ Finset.range p, ∑ v ∈ Finset.range (B + 1),
        (if v * p + ell = i + 1 + d then P.coeff i * (oddPrimeWeight p).coeff d else 0) *
          f ((v : ℤ) - 1)) =
        P.coeff i * (oddPrimeWeight p).coeff (oddPrimeDigitRemainder p i (k * p + ell)) *
          f (oddPrimeDigitRow p i (k * p + ell)) := by
    obtain ⟨v₀, hv₀loose, hindex, hrow⟩ :=
      oddPrimeExtractionIndices_exists (k := k) hp hell (Finset.mem_range.mp hi)
    have hdigit : oddPrimeDigitRemainder p i (k * p + ell) < p :=
      oddPrimeDigitRemainder_lt hp
    have hv₀ : v₀ ∈ Finset.range (B + 1) := by
      apply Finset.mem_range.mpr
      by_contra hnot
      have hle : B + 1 ≤ v₀ := by omega
      have hmul := Nat.mul_le_mul_right p hle
      have hi' := Finset.mem_range.mp hi
      nlinarith
    rw [Finset.sum_eq_single (oddPrimeDigitRemainder p i (k * p + ell))]
    · rw [Finset.sum_eq_single v₀]
      · rw [hindex, ite_eq_left rfl, hrow]
      · intro v hv hne
        have hneq : v * p + ell ≠ i + 1 + oddPrimeDigitRemainder p i (k * p + ell) := by
          intro heq
          have hu := oddPrimeExtractionIndices_unique (k := k) hp hell hdigit heq.symm
          have hvEq : v = v₀ := by have h := hu.2; omega
          exact hne hvEq
        simp only [ite_eq_right hneq, zero_mul]
      · intro hnot
        exact (hnot hv₀).elim
    · intro d hd hne
      apply Finset.sum_eq_zero
      intro v hv
      have hneq : v * p + ell ≠ i + 1 + d := by
        intro heq
        exact hne (oddPrimeExtractionIndices_unique (k := k) hp hell
          (Finset.mem_range.mp hd) heq.symm).1
      simp only [ite_eq_right hneq, zero_mul]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr hdigit)).elim
  calc
    _ = ∑ i ∈ Finset.range (B * p), ∑ d ∈ Finset.range p, ∑ v ∈ Finset.range (B + 1),
        (if v * p + ell = i + 1 + d then P.coeff i * (oddPrimeWeight p).coeff d else 0) *
          f ((v : ℤ) - 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (hsingle i hi).symm
    _ = ∑ i ∈ Finset.range (B * p), ∑ v ∈ Finset.range (B + 1), ∑ d ∈ Finset.range p,
        (if v * p + ell = i + 1 + d then P.coeff i * (oddPrimeWeight p).coeff d else 0) *
          f ((v : ℤ) - 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = ∑ v ∈ Finset.range (B + 1), ∑ i ∈ Finset.range (B * p), ∑ d ∈ Finset.range p,
        (if v * p + ell = i + 1 + d then P.coeff i * (oddPrimeWeight p).coeff d else 0) *
          f ((v : ℤ) - 1) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [oddPrimeExtraction_coeff hp P hP]
      simp only [Finset.sum_mul]

end InternalCatalan



namespace InternalCatalan

open Polynomial
open scoped BigOperators

theorem oddPrime_P_coefficient_contraction_support {p H k ell : ℕ}
    (hp : 0 < p) (hell : ell < p) (P : (ZMod p)[X])
    (hP : ∀ i, H ≤ i → P.coeff i = 0) (f : ℤ → ZMod p) :
    (∑ i ∈ Finset.range H,
      P.coeff i * (oddPrimeWeight p).coeff (oddPrimeDigitRemainder p i (k * p + ell)) *
        f (oddPrimeDigitRow p i (k * p + ell))) =
      ∑ v ∈ Finset.range (H + 1),
        (X * P * oddPrimeWeight p).coeff (v * p + ell) * f ((v : ℤ) - 1) := by
  classical
  have hbound : H ≤ H * p := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left H (show 1 ≤ p from hp)
  have hpad : ∀ i, H * p ≤ i → P.coeff i = 0 :=
    fun i hi => hP i (hbound.trans hi)
  calc
    _ = ∑ i ∈ Finset.range (H * p),
        P.coeff i * (oddPrimeWeight p).coeff (oddPrimeDigitRemainder p i (k * p + ell)) *
          f (oddPrimeDigitRow p i (k * p + ell)) := by
      apply Finset.sum_subset (Finset.range_mono hbound)
      intro i hi hnot
      have hiH : H ≤ i := by simpa only [Finset.mem_range, not_lt] using hnot
      rw [hP i hiH, zero_mul, zero_mul]
    _ = _ := oddPrime_P_coefficient_contraction hp hell P hpad f

end InternalCatalan

end OAI
