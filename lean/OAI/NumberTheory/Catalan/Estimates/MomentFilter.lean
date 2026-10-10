import Mathlib.Algebra.Polynomial.Coeff
import OAI.NumberTheory.Catalan.Polynomial.MixedPolynomial
import OAI.NumberTheory.Catalan.Polynomial.ZetaPolynomial

namespace OAI

section

open scoped BigOperators Polynomial

noncomputable section

namespace InternalCatalan

open Polynomial

def filteredColumnInt (N k : ℕ) : ℤ[X] :=
  X ^ (b N + k) * (1 - X) ^ q N

def filterCoeff (N j k : ℕ) : ℤ :=
  if b N + k ≤ j then
    (-1 : ℤ) ^ (j - b N - k) * (Nat.choose (q N) (j - b N - k) : ℤ)
  else 0

theorem one_sub_X_pow_expansion (Q : ℕ) :
    ((1 : ℤ[X]) - X) ^ Q =
      ∑ v ∈ Finset.range (Q + 1),
        C ((-1 : ℤ) ^ v * (Nat.choose Q v : ℤ)) * X ^ v := by
  calc
    ((1 : ℤ[X]) - X) ^ Q = (-X + 1) ^ Q := by
      congr 1
      ring
    _ = ∑ v ∈ Finset.range (Q + 1),
        (-X : ℤ[X]) ^ v * 1 ^ (Q - v) * (Nat.choose Q v : ℤ[X]) :=
      add_pow (-X : ℤ[X]) 1 Q
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [neg_pow]
      simp only [one_pow, mul_one, map_mul, map_pow, map_neg,
        map_one, C_eq_natCast]
      ring

theorem coeff_one_sub_X_pow (Q j : ℕ) :
    (((1 : ℤ[X]) - X) ^ Q).coeff j =
      (-1 : ℤ) ^ j * (Nat.choose Q j : ℤ) := by
  rw [one_sub_X_pow_expansion, finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single j]
  · simp
  · intro v hv hvj
    simp [Ne.symm hvj]
  · intro hj
    have hQj : Q < j := by
      simp only [Finset.mem_range] at hj
      omega
    simp [Nat.choose_eq_zero_of_lt hQj]

theorem filteredColumnInt_expansion (N k : ℕ) :
    filteredColumnInt N k =
      ∑ v ∈ Finset.range (q N + 1),
        C ((-1 : ℤ) ^ v * (Nat.choose (q N) v : ℤ)) *
          X ^ (b N + k + v) := by
  rw [filteredColumnInt, one_sub_X_pow_expansion, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [pow_add]
  ring

theorem filteredColumnInt_coeff (N j k : ℕ) :
    (filteredColumnInt N k).coeff j = filterCoeff N j k := by
  rw [filteredColumnInt, coeff_X_pow_mul', filterCoeff]
  simp only [coeff_one_sub_X_pow, Nat.sub_add_eq]

theorem filterCoeff_eq_zero_of_lt (N j k : ℕ) (hj : j < b N + k) :
    filterCoeff N j k = 0 := by
  simp [filterCoeff, Nat.not_le.mpr hj]

theorem filterCoeff_eq_zero_of_gt (N j k : ℕ)
    (hj : b N + k + q N < j) : filterCoeff N j k = 0 := by
  have hqj : q N < j - b N - k := by omega
  simp [filterCoeff, Nat.choose_eq_zero_of_lt hqj]

theorem filteredColumnInt_support (N k : ℕ) :
    (filteredColumnInt N k).support ⊆
      Finset.Icc (b N + k) (b N + k + q N) := by
  intro j hj
  rw [Finset.mem_Icc]
  have hcoeff : filterCoeff N j k ≠ 0 := by
    simpa only [mem_support_iff, filteredColumnInt_coeff] using hj
  constructor
  · by_contra h
    exact hcoeff (filterCoeff_eq_zero_of_lt N j k (Nat.lt_of_not_ge h))
  · by_contra h
    exact hcoeff (filterCoeff_eq_zero_of_gt N j k (Nat.lt_of_not_ge h))

theorem filteredColumnInt_support_contactRange (N k : ℕ) (hk : k < n N) :
    (filteredColumnInt N k).support ⊆ Finset.Ico (b N) (L N) := by
  intro j hj
  have hj' := filteredColumnInt_support N k hj
  rw [Finset.mem_Icc] at hj'
  rw [Finset.mem_Ico]
  have htop := rawColumn_lt_L (N := N) (k := k) (v := q N) hk (le_refl (q N))
  omega

theorem filteredColumnInt_eq_sum_contactRange (N k : ℕ) (hk : k < n N) :
    filteredColumnInt N k =
      ∑ j ∈ Finset.Ico (b N) (L N),
        C (filterCoeff N j k) * X ^ j := by
  calc
    filteredColumnInt N k =
        (filteredColumnInt N k).sum (fun j c => C c * X ^ j) :=
      (sum_C_mul_X_pow_eq _).symm
    _ = ∑ j ∈ Finset.Ico (b N) (L N),
        C ((filteredColumnInt N k).coeff j) * X ^ j :=
      sum_eq_of_subset (fun j c => C c * X ^ j)
        (by intro j; simp) (filteredColumnInt_support_contactRange N k hk)
    _ = _ := by simp only [filteredColumnInt_coeff]


variable {V : Type*} [AddCommGroup V]

theorem map_filteredColumnInt (F : ℤ[X] →ₗ[ℤ] V) (N k : ℕ) :
    F (filteredColumnInt N k) =
      ∑ v ∈ Finset.range (q N + 1),
        ((-1 : ℤ) ^ v * (Nat.choose (q N) v : ℤ)) •
          F (X ^ (b N + k + v)) := by
  rw [filteredColumnInt_expansion, map_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [← smul_eq_C_mul, F.map_smul]

theorem map_filteredColumnInt_contactRange (F : ℤ[X] →ₗ[ℤ] V)
    (N k : ℕ) (hk : k < n N) :
    F (filteredColumnInt N k) =
      ∑ j ∈ Finset.Ico (b N) (L N),
        filterCoeff N j k • F (X ^ j) := by
  rw [filteredColumnInt_eq_sum_contactRange N k hk, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← smul_eq_C_mul, F.map_smul]


end InternalCatalan

end

end


noncomputable section

open Polynomial
open scoped BigOperators

namespace InternalCatalan

theorem realPoly_filteredColumnInt (N k : ℕ) :
    realPoly (filteredColumnInt N k) = filteredColumn N k := by
  simp [realPoly, filteredColumnInt, filteredColumn]

theorem filteredColumn_expansion (N k : ℕ) :
    filteredColumn N k =
      ∑ v ∈ Finset.range (q N + 1),
        Polynomial.C (filterCoeffRat N v : ℝ) *
          Polynomial.X ^ (b N + k + v) := by
  rw [← realPoly_filteredColumnInt, filteredColumnInt_expansion]
  simp [realPoly, Polynomial.map_sum, filterCoeffRat]

def coefficientPairingRight (K : ℕ → ℕ → ℝ) (P : ℝ[X]) : ℝ[X] →ₗ[ℝ] ℝ :=
  Polynomial.lsum fun j =>
    { toFun := fun a => ∑ i ∈ P.support, (P.coeff i * a) * K i j
      map_add' := by
        intro a b
        simp only [mul_add, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c a
        change (∑ i ∈ P.support, (P.coeff i * (c * a)) * K i j) =
          c * ∑ i ∈ P.support, (P.coeff i * a) * K i j
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring }

theorem coefficientPairingRight_apply (K : ℕ → ℕ → ℝ) (P Q : ℝ[X]) :
    coefficientPairingRight K P Q =
      ∑ i ∈ P.support, ∑ j ∈ Q.support,
        (P.coeff i * Q.coeff j) * K i j := by
  change (∑ j ∈ Q.support, ∑ i ∈ P.support,
    (P.coeff i * Q.coeff j) * K i j) = _
  exact Finset.sum_comm

def mixedMomentRightLinear (P : ℝ[X]) : ℝ[X] →ₗ[ℝ] ℝ :=
  coefficientPairingRight
    (fun i j => mixedMoment (Polynomial.X ^ i) (Polynomial.X ^ j)) P

theorem mixedMomentRightLinear_apply (P Q : ℝ[X]) :
    mixedMomentRightLinear P Q = mixedMoment P Q := by
  rw [mixedMomentRightLinear, coefficientPairingRight_apply, mixedMoment_eq_sum]

def zetaMomentRightLinear (P : ℝ[X]) : ℝ[X] →ₗ[ℝ] ℝ :=
  coefficientPairingRight zetaSeries P

theorem zetaMomentRightLinear_apply (P Q : ℝ[X]) :
    zetaMomentRightLinear P Q = zetaMoment P Q := by
  rw [zetaMomentRightLinear, coefficientPairingRight_apply, zetaMoment_eq_sum]

theorem map_filteredColumn (F : ℝ[X] →ₗ[ℝ] ℝ) (N k : ℕ) :
    F (filteredColumn N k) =
      ∑ v ∈ Finset.range (q N + 1),
        (filterCoeffRat N v : ℝ) * F (Polynomial.X ^ (b N + k + v)) := by
  rw [filteredColumn_expansion, map_sum]
  apply Finset.sum_congr rfl
  intro v hv
  simpa only [Polynomial.smul_eq_C_mul, smul_eq_mul] using
    F.map_smul (filterCoeffRat N v : ℝ) (Polynomial.X ^ (b N + k + v))

theorem mixedMoment_filteredColumn (P : ℝ[X]) (N k : ℕ) :
    mixedMoment P (filteredColumn N k) =
      ∑ v ∈ Finset.range (q N + 1),
        (filterCoeffRat N v : ℝ) *
          mixedMoment P (Polynomial.X ^ (b N + k + v)) := by
  rw [← mixedMomentRightLinear_apply P (filteredColumn N k), map_filteredColumn]
  apply Finset.sum_congr rfl
  intro v hv
  rw [mixedMomentRightLinear_apply]

theorem zetaMoment_filteredColumn (P : ℝ[X]) (N k : ℕ) :
    zetaMoment P (filteredColumn N k) =
      ∑ v ∈ Finset.range (q N + 1),
        (filterCoeffRat N v : ℝ) *
          zetaMoment P (Polynomial.X ^ (b N + k + v)) := by
  rw [← zetaMomentRightLinear_apply P (filteredColumn N k), map_filteredColumn]
  apply Finset.sum_congr rfl
  intro v hv
  rw [zetaMomentRightLinear_apply]

end InternalCatalan

end

end OAI
