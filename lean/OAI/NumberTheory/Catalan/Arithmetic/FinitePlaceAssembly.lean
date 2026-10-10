import Mathlib.Algebra.BigOperators.Intervals
import OAI.NumberTheory.Catalan.Arithmetic.FinitePlaceNumerics
import OAI.NumberTheory.Catalan.Arithmetic.FinitePlacePartialAssembly
import OAI.NumberTheory.Catalan.Arithmetic.OddPrimeLossNormalization
import OAI.NumberTheory.Catalan.Arithmetic.OddPrimeUpperPoolEnumeration
import OAI.NumberTheory.Catalan.Determinants.OddLowerMinorTransfer

namespace OAI


noncomputable section

namespace InternalCatalan

open scoped BigOperators

def momentStartingRat (i j : ℕ) : ℚ :=
  if j ≤ i then boundaryMinus (i - j) else boundaryPlus (j - i)

theorem momentRat_reverse_diagonal (i j : ℕ) :
    momentRat i j = momentStartingRat i j -
      ∑ ell ∈ Finset.range (min i j),
        momentScalarPred (i - ell) / ((j - ell : ℕ) : ℚ) := by
  by_cases hji : j ≤ i
  · rw [momentRat_of_le hji, momentStartingRat, ite_eq_left hji, min_eq_right hji]
    congr 1
    calc
      _ = ∑ ell ∈ Finset.range j,
          momentScalar (i - j + (j - 1 - ell)) / (((j - 1 - ell) + 1 : ℕ) : ℚ) :=
        (Finset.sum_range_reflect
          (fun k => momentScalar (i - j + k) / ((k + 1 : ℕ) : ℚ)) j).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro ell hell
        have he := Finset.mem_range.mp hell
        rw [momentScalarPred, ite_eq_right (by omega : i - ell ≠ 0)]
        congr 2 <;> omega
  · have hij : i < j := by omega
    rw [momentRat_of_lt hij, momentStartingRat, ite_eq_right hji, min_eq_left (Nat.le_of_lt hij)]
    congr 1
    calc
      _ = ∑ ell ∈ Finset.range i,
          momentScalar (i - 1 - ell) / ((j - i + (i - 1 - ell) + 1 : ℕ) : ℚ) :=
        (Finset.sum_range_reflect
          (fun k => momentScalar k / ((j - i + k + 1 : ℕ) : ℚ)) i).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro ell hell
        have he := Finset.mem_range.mp hell
        rw [momentScalarPred, ite_eq_right (by omega : i - ell ≠ 0)]
        congr 2 <;> omega

theorem momentScalarPred_central_reduction {p z : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hz : z < 2 * p) :
    (((p : ℚ) * momentScalarPred z).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) * momentScalarPred z) =
        if p ≤ z then 2 * (oddPrimeWeight p).coeff (2 * p - 1 - z) else 0 := by
  have hz2 : z < p ^ 2 := by nlinarith [hp.out.two_le]
  have h := momentScalarPred_prime_digit_reduction hp2 hz2
  refine ⟨h.1, ?_⟩
  have hres : palindromicRatResidue p ((p : ℚ) * momentScalarPred z) =
      (oddPrimeWeight p).coeff (p - 1 - z % p) *
        palindromicRatResidue p (momentScalarPred (z / p)) := h.2.2
  rw [hres]
  by_cases hpz : p ≤ z
  · have hq : z / p = 1 := by
      rw [show z = p * 1 + (z - p) by omega, Nat.mul_add_div hp.out.pos,
        Nat.div_eq_of_lt (by omega : z - p < p), add_zero]
    have hr : z % p = z - p := by
      have he := Nat.mod_add_div z p
      rw [hq, Nat.mul_one] at he
      omega
    have he : p - 1 - (z - p) = 2 * p - 1 - z := by omega
    rw [ite_eq_left hpz, hq, hr, he]
    have hs : palindromicRatResidue p (momentScalarPred 1) = 2 := by
      norm_num [momentScalarPred, momentScalar_zero, palindromicRatResidue]
    rw [hs, mul_comm]
  · rw [ite_eq_right hpz, Nat.div_eq_of_lt (by omega : z < p), momentScalarPred_zero]
    norm_num [palindromicRatResidue]

theorem momentStartingRat_central_den_ne_zero {p i j : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hj : j < p) (hi : i < p + j) :
    ((momentStartingRat i j).den : ZMod p) ≠ 0 := by
  apply rational_den_ne_zero_of_valuation_nonneg
  unfold momentStartingRat
  split_ifs with hji
  · exact boundaryMinus_odd_prime_valuation_nonneg hp.out hp2 _ (by omega)
  · exact boundaryPlus_odd_prime_valuation_nonneg hp.out hp2 _ (by omega)

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open scoped BigOperators

theorem momentScalarPred_central_div_reduction {p i j ell : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hj : j < p) (hi : i < p + j) (hell : ell < min i j) :
    (((p : ℚ) * (momentScalarPred (i - ell) / ((j - ell : ℕ) : ℚ))).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p
        ((p : ℚ) * (momentScalarPred (i - ell) / ((j - ell : ℕ) : ℚ))) =
          if p + ell ≤ i then
            (2 * (oddPrimeWeight p).coeff (2 * p + ell - 1 - i)) /
              ((j - ell : ℕ) : ZMod p)
          else 0 := by
  have helli : ell < i := lt_of_lt_of_le hell (Nat.min_le_left i j)
  have hellj : ell < j := lt_of_lt_of_le hell (Nat.min_le_right i j)
  have hden0 : 0 < j - ell := by omega
  have hdenlt : j - ell < p := by omega
  have hden : ((j - ell : ℕ) : ZMod p) ≠ 0 := by
    intro hzero
    exact (Nat.not_dvd_of_pos_of_lt hden0 hdenlt)
      ((ZMod.natCast_eq_zero_iff (j - ell) p).mp hzero)
  have hscalar := momentScalarPred_central_reduction hp2
    (show i - ell < 2 * p by omega)
  have hrecip := nat_fraction_reduced_residue (p := p) 1 (j - ell) hden
  have hrecipden : ((1 / ((j - ell : ℕ) : ℚ)).den : ZMod p) ≠ 0 := by
    simpa only [Nat.cast_one] using hrecip.1
  have hrecipR : palindromicRatResidue p (1 / ((j - ell : ℕ) : ℚ)) =
      1 / ((j - ell : ℕ) : ZMod p) := by
    simpa only [palindromicRatResidue, Nat.cast_one] using hrecip.2
  have hprod := rational_residue_mul hscalar.1 hrecipden
  have heq : (p : ℚ) * (momentScalarPred (i - ell) / ((j - ell : ℕ) : ℚ)) =
      ((p : ℚ) * momentScalarPred (i - ell)) * (1 / ((j - ell : ℕ) : ℚ)) := by ring
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact hprod.1
  · rw [heq, palindromicRatResidue_mul hscalar.1 hrecipden, hscalar.2, hrecipR]
    by_cases hle : p + ell ≤ i
    · have hscalarle : p ≤ i - ell := by omega
      have hindex : 2 * p - 1 - (i - ell) = 2 * p + ell - 1 - i := by omega
      rw [ite_eq_left hle, ite_eq_left hscalarle, hindex]
      ring
    · have hscalarnot : ¬p ≤ i - ell := by omega
      rw [ite_eq_right hle, ite_eq_right hscalarnot, zero_mul]

theorem momentRat_central_reduction {p i j : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hj : j < p) (hi : i < p + j) :
    (((p : ℚ) * momentRat i j).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) * momentRat i j) =
        -(∑ ell ∈ Finset.range (min i j),
          if p + ell ≤ i then
            (2 * (oddPrimeWeight p).coeff (2 * p + ell - 1 - i)) /
              ((j - ell : ℕ) : ZMod p)
          else 0) := by
  let f : ℕ → ℚ := fun ell =>
    (p : ℚ) * (momentScalarPred (i - ell) / ((j - ell : ℕ) : ℚ))
  have hterm (ell : ℕ) (hell : ell ∈ Finset.range (min i j)) :
      ((f ell).den : ZMod p) ≠ 0 ∧
        palindromicRatResidue p (f ell) =
          if p + ell ≤ i then
            (2 * (oddPrimeWeight p).coeff (2 * p + ell - 1 - i)) /
              ((j - ell : ℕ) : ZMod p)
          else 0 :=
    momentScalarPred_central_div_reduction hp2 hj hi (Finset.mem_range.mp hell)
  have hsum := rational_residue_sum (Finset.range (min i j)) f
    (fun ell hell => (hterm ell hell).1)
  have hstart := momentStartingRat_central_den_ne_zero hp2 hj hi
  have hstartmul := rational_residue_mul (a := (p : ℚ)) (by simp) hstart
  have hstartR : palindromicRatResidue p ((p : ℚ) * momentStartingRat i j) = 0 := by
    rw [palindromicRatResidue_mul (by simp) hstart]
    simp [palindromicRatResidue]
  have hstrip : (p : ℚ) * momentRat i j =
      (p : ℚ) * momentStartingRat i j - ∑ ell ∈ Finset.range (min i j), f ell := by
    simp only [momentRat_reverse_diagonal, mul_sub, Finset.mul_sum, f]
  have hdiff := rational_residue_sub hstartmul.1 hsum.1
  refine ⟨?_, ?_⟩
  · rw [hstrip]
    exact hdiff.1
  · rw [hstrip, palindromicRatResidue_sub hstartmul.1 hsum.1, hstartR, zero_sub]
    congr 1
    calc
      palindromicRatResidue p (∑ ell ∈ Finset.range (min i j), f ell) =
          ∑ ell ∈ Finset.range (min i j), palindromicRatResidue p (f ell) := hsum.2
      _ = _ := Finset.sum_congr rfl (fun ell hell => (hterm ell hell).2)

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Polynomial
open scoped BigOperators

theorem oddPrime_central_strip_range {R : Type*} [Semiring R] {p H i j : ℕ}
    (hp : 0 < p) (hpH : p ≤ H) (hi : i < H) (hj : H - p ≤ j) (f : ℕ → R) :
    (∑ ell ∈ Finset.range (min i j), if p + ell ≤ i then f ell else 0) =
      ∑ ell ∈ Finset.range (H - p), if p + ell ≤ i then f ell else 0 := by
  classical
  refine Finset.sum_bij_ne_zero (fun ell _ _ => ell) ?_ ?_ ?_ ?_
  · intro ell hell hf
    have hactive : p + ell ≤ i := by
      by_contra h
      exact hf (ite_eq_right h)
    exact Finset.mem_range.mpr (by omega)
  · intro ell hell hf ell' hell' hf' heq
    exact heq
  · intro ell hell hf
    have hactive : p + ell ≤ i := by
      by_contra h
      exact hf (ite_eq_right h)
    have hell' := Finset.mem_range.mp hell
    refine ⟨ell, Finset.mem_range.mpr (by omega), hf, rfl⟩
  · intro ell hell hf
    rfl

theorem rowP_momentRat_central_reduction {p N r j : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hpH : p ≤ H N) (hH : H N ≤ 2 * p)
    (hjlo : H N - p ≤ j) (hj : j < p) :
    (((p : ℚ) * (∑ t ∈ Finset.range (H N),
      ((rowP N r).coeff t : ℚ) * momentRat t j)).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) * (∑ t ∈ Finset.range (H N),
        ((rowP N r).coeff t : ℚ) * momentRat t j)) =
        -(∑ ell ∈ Finset.range (H N - p),
          (2 * oddPrimeExtractedP p N r ell 2) / ((j - ell : ℕ) : ZMod p)) := by
  let f : ℕ → ℚ := fun t => ((rowP N r).coeff t : ℚ) * ((p : ℚ) * momentRat t j)
  let c : ℕ → ℕ → ZMod p := fun t ell =>
    if p + ell ≤ t then (2 * (oddPrimeWeight p).coeff (2 * p + ell - 1 - t)) /
      ((j - ell : ℕ) : ZMod p) else 0
  have hterm (t : ℕ) (ht : t ∈ Finset.range (H N)) :
      ((f t).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p (f t) = ((rowP N r).coeff t : ZMod p) *
        (-(∑ ell ∈ Finset.range (H N - p), c t ell)) := by
    have ht' := Finset.mem_range.mp ht
    have hm := momentRat_central_reduction hp2 hj (show t < p + j by omega)
    have hprod := rational_residue_mul (p := p) (a := ((rowP N r).coeff t : ℚ))
      (by simp) hm.1
    have htrim := oddPrime_central_strip_range hp.out.pos hpH ht' hjlo
      (fun ell => (2 * (oddPrimeWeight p).coeff (2 * p + ell - 1 - t)) /
        ((j - ell : ℕ) : ZMod p))
    refine ⟨hprod.1, ?_⟩
    change palindromicRatResidue p
      (((rowP N r).coeff t : ℚ) * ((p : ℚ) * momentRat t j)) = _
    rw [palindromicRatResidue_mul (by simp) hm.1, palindromicRatResidue_intCast,
      hm.2, htrim]
  have hs := rational_residue_sum (Finset.range (H N)) f (fun t ht => (hterm t ht).1)
  have hscale : (p : ℚ) * (∑ t ∈ Finset.range (H N),
      ((rowP N r).coeff t : ℚ) * momentRat t j) = ∑ t ∈ Finset.range (H N), f t := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    dsimp only [f]
    ring
  let P : (ZMod p)[X] := (rowP N r).map (Int.castRingHom (ZMod p))
  have hP : ∀ t, H N ≤ t → P.coeff t = 0 := by
    intro t ht
    simp only [P, coeff_map, rowP_coeff_eq_zero_of_ge hN ht, map_zero]
  have hcast (a : ℤ) : (Int.castRingHom (ZMod p)) a = (a : ZMod p) := rfl
  have hcoefficient (ell : ℕ) :
      (∑ t ∈ Finset.range (H N), ((rowP N r).coeff t : ZMod p) * c t ell) =
        (2 * oddPrimeExtractedP p N r ell 2) / ((j - ell : ℕ) : ZMod p) := by
    have hcoef := oddPrime_central_P_coefficient (ell := ell) hp.out.pos hH P hP
    have hcoef' :
        (∑ t ∈ Finset.range (H N), ((rowP N r).coeff t : ZMod p) *
          (if p + ell ≤ t then 2 * (oddPrimeWeight p).coeff (2 * p + ell - 1 - t) else 0)) =
          2 * oddPrimeExtractedP p N r ell 2 := by
      simpa only [P, coeff_map, hcast, oddPrimeExtractedP] using hcoef
    rw [← hcoef']
    simp only [div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t ht
    dsimp only [c]
    split_ifs <;> ring
  refine ⟨?_, ?_⟩
  · rw [hscale]
    exact hs.1
  · rw [hscale]
    calc
      palindromicRatResidue p (∑ t ∈ Finset.range (H N), f t) =
          ∑ t ∈ Finset.range (H N), palindromicRatResidue p (f t) := hs.2
      _ = ∑ t ∈ Finset.range (H N), ((rowP N r).coeff t : ZMod p) *
          (-(∑ ell ∈ Finset.range (H N - p), c t ell)) :=
        Finset.sum_congr rfl (fun t ht => (hterm t ht).2)
      _ = -(∑ ell ∈ Finset.range (H N - p), ∑ t ∈ Finset.range (H N),
          ((rowP N r).coeff t : ZMod p) * c t ell) := by
        simp only [mul_neg, Finset.mul_sum, Finset.sum_neg_distrib]
        rw [Finset.sum_comm]
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro ell hell
        exact hcoefficient ell

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open scoped BigOperators

def oddPrimeLeadingV (p N r ell : ℕ) [Fact p.Prime] : ZMod p :=
  2 * oddPrimeExtractedP p N r ell 2 -
    (3 / 2 : ZMod p) * oddPrimeExtractedD p N r ell 1

theorem rawCatalanTerm_prime_reduction {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) (N r j : ℕ) :
    (((p : ℚ) * z * rawCatalanCoeffRat N r j).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) * z * rawCatalanCoeffRat N r j) = 0 := by
  have hpz := rational_residue_mul (p := p) (a := (p : ℚ)) (by simp) hz
  have hfull := rational_residue_mul hpz.1
    (rawCatalanCoeffRat_odd_prime_den_ne_zero hp2 N r j)
  refine ⟨hfull.1, ?_⟩
  change (((p : ℚ) * z * rawCatalanCoeffRat N r j).num : ZMod p) /
    (((p : ℚ) * z * rawCatalanCoeffRat N r j).den : ZMod p) = 0
  rw [hfull.2, hpz.2]
  simp

theorem rawEntryRat_central_layer {p N r j : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hpH : p ≤ H N) (hH : H N ≤ 2 * p)
    (hjlo : H N - p ≤ j) (hj : j < p) (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    (((p : ℚ) * rawEntryRat z N r j).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) * rawEntryRat z N r j) =
        -(∑ ell ∈ Finset.range (H N - p),
          oddPrimeLeadingV p N r ell / ((j - ell : ℕ) : ZMod p)) := by
  let A : ℚ := (p : ℚ) * (∑ t ∈ Finset.range (H N),
    ((rowP N r).coeff t : ℚ) * momentRat t j)
  let B : ℚ := (p : ℚ) * (∑ t ∈ Finset.range (H N),
    ((rowD N r).coeff t : ℚ) * zetaRat t j)
  let C : ℚ := (p : ℚ) * z * rawCatalanCoeffRat N r j
  have hA := rowP_momentRat_central_reduction (r := r) hp2 hN hpH hH hjlo hj
  have hB := rowD_zetaRat_central_reduction (r := r) hN hpH hH hjlo hj
  have hC := rawCatalanTerm_prime_reduction hp2 z hz N r j
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hdiv := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
    have hpgt : 2 < p := by have := hp.out.two_le; omega
    exact (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) hpgt) hdiv
  have h32 := nat_fraction_reduced_residue (p := p) 3 2 htwo
  have hBprod := rational_residue_mul h32.1 hB.1
  have hdiff := rational_residue_sub hA.1 hBprod.1
  have hsum := rational_residue_add hdiff.1 hC.1
  have hsplit : (p : ℚ) * rawEntryRat z N r j = A - (3 / 2 : ℚ) * B + C := by
    dsimp only [A, B, C]
    rw [rawEntryRat_affine, rawEntryRat_zero]
    ring
  have hAR : palindromicRatResidue p A =
      -(∑ ell ∈ Finset.range (H N - p),
        (2 * oddPrimeExtractedP p N r ell 2) / ((j - ell : ℕ) : ZMod p)) := hA.2
  have hBR : palindromicRatResidue p B =
      -(∑ ell ∈ Finset.range (H N - p),
        oddPrimeExtractedD p N r ell 1 / ((j - ell : ℕ) : ZMod p)) := hB.2
  have hCR : palindromicRatResidue p C = 0 := hC.2
  have h32R : palindromicRatResidue p (3 / 2 : ℚ) = (3 / 2 : ZMod p) := h32.2
  have hsumR : palindromicRatResidue p (A - (3 / 2 : ℚ) * B + C) =
      palindromicRatResidue p (A - (3 / 2 : ℚ) * B) + palindromicRatResidue p C := hsum.2
  have hdiffR : palindromicRatResidue p (A - (3 / 2 : ℚ) * B) =
      palindromicRatResidue p A - palindromicRatResidue p ((3 / 2 : ℚ) * B) := hdiff.2
  have hprodR : palindromicRatResidue p ((3 / 2 : ℚ) * B) =
      palindromicRatResidue p (3 / 2 : ℚ) * palindromicRatResidue p B := hBprod.2
  refine ⟨?_, ?_⟩
  · rw [hsplit]
    exact hsum.1
  · rw [hsplit, hsumR, hdiffR, hprodR, hAR, hBR, hCR, h32R, add_zero]
    simp only [oddPrimeLeadingV, sub_div, Finset.sum_sub_distrib,
      mul_div_assoc, ← Finset.mul_sum]
    ring

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open scoped BigOperators

theorem rawEntryRat_low_leading {p N r ell : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hell : ell < p)
    (hwidth : H N ≤ ell + 2 * p) (hhigh : p + ell < H N)
    (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    (((p : ℚ) ^ 2 * rawEntryRat z N r ell).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) ^ 2 * rawEntryRat z N r ell) =
        oddPrimeLeadingV p N r ell := by
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  have hH : H N < p ^ 2 := by nlinarith
  have hH2 : 2 ≤ H N := by unfold H; omega
  have hraw := rawEntryRat_general_column_layer (k := 0) (N := N) (r := r)
    hp2 hN hH hell (by simpa using (show ell < H N by omega)) z hz
  simp only [Nat.zero_mul, zero_add] at hraw
  have hM :
      (∑ v ∈ Finset.range (H N + 1), oddPrimeExtractedP p N r ell v *
        palindromicRatResidue p (momentRatSigned ((v : ℤ) - 1) 0)) =
          2 * oddPrimeExtractedP p N r ell 2 := by
    rw [Finset.sum_eq_single 2]
    · norm_num [palindromicRatResidue, momentRatSigned, momentRat,
        boundaryMinus]
      ring
    · intro v hv hne
      by_cases hv3 : 3 ≤ v
      · rw [oddPrimeExtractedP_eq_zero_of_ge_three hp.out.pos hN hwidth hv3, zero_mul]
      · have hcases : v = 0 ∨ v = 1 := by omega
        rcases hcases with rfl | rfl <;>
          norm_num [palindromicRatResidue, momentRatSigned, momentRatNegOne,
            momentRat, boundaryPlus, boundaryMinus]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (by omega : 2 < H N + 1))).elim
  have hD :
      (∑ u ∈ Finset.range (H N), oddPrimeExtractedD p N r ell u *
        palindromicRatResidue p (zetaRat u 0)) = oddPrimeExtractedD p N r ell 1 := by
    rw [Finset.sum_eq_single 1]
    · norm_num [palindromicRatResidue, zetaRat, harmonicRat, Finset.sum_range_succ]
    · intro u hu hne
      by_cases hu2 : 2 ≤ u
      · rw [oddPrimeExtractedD_eq_zero_of_ge_two hN hwidth hu2, zero_mul]
      · have hu0 : u = 0 := by omega
        subst u
        norm_num [palindromicRatResidue, zetaRat, harmonicRat]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (by omega : 1 < H N))).elim
  refine ⟨hraw.1, ?_⟩
  rw [hraw.2, hM, hD]
  rfl

theorem rawEntryRat_high_leading {p N r ell : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hell : ell < p)
    (hwidth : H N ≤ ell + 2 * p) (hhigh : p + ell < H N)
    (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    (((p : ℚ) ^ 2 * rawEntryRat z N r (p + ell)).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) ^ 2 * rawEntryRat z N r (p + ell)) =
        oddPrimeLeadingU p N r ell - oddPrimeLeadingV p N r ell := by
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  have hH : H N < p ^ 2 := by nlinarith
  have hlo := rawEntryRat_low_leading (r := r) hp2 hN hell hwidth hhigh z hz
  have hhi := rawEntryRat_prime_digit_reduction (N := N) (r := r) hp2 hH hhigh z hz
  have hpair := rawEntryRat_pair_leading (r := r) hp2 hN hell hwidth hhigh z hz
  have hadd := palindromicRatResidue_add hlo.1 hhi.1
  have hsum : oddPrimeLeadingV p N r ell +
      palindromicRatResidue p ((p : ℚ) ^ 2 * rawEntryRat z N r (p + ell)) =
        oddPrimeLeadingU p N r ell := by
    rw [← hlo.2, ← hadd, ← mul_add]
    exact hpair.2
  refine ⟨hhi.1, ?_⟩
  calc
    _ = (oddPrimeLeadingV p N r ell +
        palindromicRatResidue p ((p : ℚ) ^ 2 * rawEntryRat z N r (p + ell))) -
          oddPrimeLeadingV p N r ell := by ring
    _ = _ := by rw [hsum]

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

def oddPrimeRepresented (p N ell : ℕ) : Prop :=
  b N ≤ ell ∨ ell < L N - p

instance oddPrimeRepresented_decidable (p N ell : ℕ) : Decidable (oddPrimeRepresented p N ell) :=
  inferInstanceAs (Decidable (b N ≤ ell ∨ ell < L N - p))

def oddPrimeRepresentativeRat (z : ℚ) (p N r ell : ℕ) : ℚ :=
  if b N ≤ ell then rawEntryRat z N r ell else -rawEntryRat z N r (p + ell)

theorem oddPrimeRepresentativeRat_scaled_reduction {p N r ell : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hr : r < n N)
    (hpH : p ≤ H N) (hH : H N ≤ 2 * p) (hell : ell < H N - p)
    (_hrep : oddPrimeRepresented p N ell) (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    (((p : ℚ) ^ 2 * oddPrimeRepresentativeRat z p N r ell).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) ^ 2 * oddPrimeRepresentativeRat z p N r ell) =
        oddPrimeLeadingV p N r ell := by
  have hellp : ell < p := by omega
  have hwidth : H N ≤ ell + 2 * p := by omega
  have hhigh : p + ell < H N := by omega
  by_cases hb : b N ≤ ell
  · rw [oddPrimeRepresentativeRat, ite_eq_left hb]
    exact rawEntryRat_low_leading (r := r) hp2 hN hellp hwidth hhigh z hz
  · have hellA : ell ≤ A N := by
      unfold b A at *
      omega
    have hU := oddPrimeLeadingU_eq_zero (p := p) hp.out.pos hN hr hellA
    have hraw := rawEntryRat_high_leading (r := r) hp2 hN hellp hwidth hhigh z hz
    rw [oddPrimeRepresentativeRat, ite_eq_right hb, mul_neg]
    refine ⟨?_, ?_⟩
    · simpa only [Rat.neg_den] using hraw.1
    · have hneg :
          palindromicRatResidue p (-((p : ℚ) ^ 2 * rawEntryRat z N r (p + ell))) =
            -palindromicRatResidue p ((p : ℚ) ^ 2 * rawEntryRat z N r (p + ell)) := by
        simp only [palindromicRatResidue, Rat.neg_num, Rat.neg_den, Int.cast_neg, neg_div]
      rw [hneg, hraw.2, hU, zero_sub, neg_neg]







open scoped BigOperators

def oddPrimeShearedRat (z : ℚ) (p N r j : ℕ) : ℚ := by
  classical
  exact rawEntryRat z N r j + (p : ℚ) *
    ∑ ell ∈ Finset.range (H N - p),
      if oddPrimeRepresented p N ell then
        oddPrimeRepresentativeRat z p N r ell / ((j - ell : ℕ) : ℚ)
      else 0

theorem oddPrimeShearedRat_scaled_reduction {p N r j : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hr : r < n N)
    (hpH : p ≤ H N) (hH : H N ≤ 2 * p)
    (hjlo : H N - p ≤ j) (hj : j < p) (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    (((p : ℚ) * oddPrimeShearedRat z p N r j).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) * oddPrimeShearedRat z p N r j) =
        -(∑ ell ∈ Finset.range (H N - p),
          if ¬oddPrimeRepresented p N ell then
            oddPrimeLeadingV p N r ell / ((j - ell : ℕ) : ZMod p)
          else 0) := by
  classical
  let f : ℕ → ℚ := fun ell =>
    if oddPrimeRepresented p N ell then
      (p : ℚ) ^ 2 * oddPrimeRepresentativeRat z p N r ell /
        ((j - ell : ℕ) : ℚ)
    else 0
  have hterm (ell : ℕ) (hell : ell ∈ Finset.range (H N - p)) :
      ((f ell).den : ZMod p) ≠ 0 ∧
        palindromicRatResidue p (f ell) =
          if oddPrimeRepresented p N ell then
            oddPrimeLeadingV p N r ell / ((j - ell : ℕ) : ZMod p)
          else 0 := by
    by_cases hrep : oddPrimeRepresented p N ell
    · have hellJ := Finset.mem_range.mp hell
      have hrepR := oddPrimeRepresentativeRat_scaled_reduction
        hp2 hN hr hpH hH hellJ hrep z hz
      have hellj : ell < j := hellJ.trans_le hjlo
      have hdpos : 0 < j - ell := by omega
      have hdlt : j - ell < p := by omega
      have hden : ((j - ell : ℕ) : ZMod p) ≠ 0 := by
        intro hzero
        exact (Nat.not_dvd_of_pos_of_lt hdpos hdlt)
          ((ZMod.natCast_eq_zero_iff (j - ell) p).mp hzero)
      have hinv := nat_fraction_reduced_residue (p := p) 1 (j - ell) hden
      simp only [Nat.cast_one] at hinv
      have hinvR : palindromicRatResidue p (1 / ((j - ell : ℕ) : ℚ)) =
          1 / ((j - ell : ℕ) : ZMod p) := hinv.2
      have hprod := rational_residue_mul hrepR.1 hinv.1
      have heq : f ell =
          ((p : ℚ) ^ 2 * oddPrimeRepresentativeRat z p N r ell) *
            (1 / ((j - ell : ℕ) : ℚ)) := by
        dsimp only [f]
        rw [ite_eq_left hrep]
        ring
      refine ⟨?_, ?_⟩
      · rw [heq]
        exact hprod.1
      · rw [heq, palindromicRatResidue_mul hrepR.1 hinv.1,
          hrepR.2, hinvR, ite_eq_left hrep]
        ring
    · simp [f, hrep, palindromicRatResidue]
  have hsum := rational_residue_sum (Finset.range (H N - p)) f
    (fun ell hell => (hterm ell hell).1)
  have hsumR : palindromicRatResidue p (∑ ell ∈ Finset.range (H N - p), f ell) =
      ∑ ell ∈ Finset.range (H N - p),
        if oddPrimeRepresented p N ell then
          oddPrimeLeadingV p N r ell / ((j - ell : ℕ) : ZMod p)
        else 0 := by
    calc
      _ = ∑ ell ∈ Finset.range (H N - p), palindromicRatResidue p (f ell) := hsum.2
      _ = _ := Finset.sum_congr rfl (fun ell hell => (hterm ell hell).2)
  have hcentral := rawEntryRat_central_layer (r := r) hp2 hN hpH hH hjlo hj z hz
  have hadd := rational_residue_add hcentral.1 hsum.1
  have hscale : (p : ℚ) * oddPrimeShearedRat z p N r j =
      (p : ℚ) * rawEntryRat z N r j + ∑ ell ∈ Finset.range (H N - p), f ell := by
    unfold oddPrimeShearedRat
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro ell hell
    dsimp only [f]
    split_ifs <;> ring
  have hpartition :
      (∑ ell ∈ Finset.range (H N - p),
        oddPrimeLeadingV p N r ell / ((j - ell : ℕ) : ZMod p)) =
      (∑ ell ∈ Finset.range (H N - p),
        if oddPrimeRepresented p N ell then
          oddPrimeLeadingV p N r ell / ((j - ell : ℕ) : ZMod p) else 0) +
      (∑ ell ∈ Finset.range (H N - p),
        if ¬oddPrimeRepresented p N ell then
          oddPrimeLeadingV p N r ell / ((j - ell : ℕ) : ZMod p) else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ell hell
    by_cases hrep : oddPrimeRepresented p N ell <;> simp [hrep]
  refine ⟨?_, ?_⟩
  · rw [hscale]
    exact hadd.1
  · rw [hscale, palindromicRatResidue_add hcentral.1 hsum.1,
      hcentral.2, hsumR, hpartition]
    ring

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open scoped BigOperators

def oddPrimeLeadingLiftRat (p N r ell : ℕ) [Fact p.Prime] : ℚ :=
  ((oddPrimeLeadingV p N r ell).val : ℚ)

def oddPrimeExceptionalPartRat (_z : ℚ) (p N r j : ℕ) [Fact p.Prime] : ℚ := by
  classical
  exact ∑ ell ∈ Finset.range (H N - p),
    if ¬oddPrimeRepresented p N ell then
      -(oddPrimeLeadingLiftRat p N r ell / ((j - ell : ℕ) : ℚ)) else 0

def oddPrimeCentralRemainderRat (z : ℚ) (p N r j : ℕ) [Fact p.Prime] : ℚ :=
  oddPrimeShearedRat z p N r j - oddPrimeExceptionalPartRat z p N r j / (p : ℚ)

theorem oddPrimeLeadingLiftRat_reduction {p N r ell : ℕ} [Fact p.Prime] :
    ((oddPrimeLeadingLiftRat p N r ell).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p (oddPrimeLeadingLiftRat p N r ell) =
        oddPrimeLeadingV p N r ell :=
  zmod_val_rat_reduction (oddPrimeLeadingV p N r ell)

theorem oddPrimeExceptionalPartRat_reduction {p N r j : ℕ} [hp : Fact p.Prime]
    (hjlo : H N - p ≤ j) (hj : j < p) (z : ℚ) :
    ((oddPrimeExceptionalPartRat z p N r j).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p (oddPrimeExceptionalPartRat z p N r j) =
        -(∑ ell ∈ Finset.range (H N - p),
          if ¬oddPrimeRepresented p N ell then
            oddPrimeLeadingV p N r ell / ((j - ell : ℕ) : ZMod p) else 0) := by
  classical
  let f : ℕ → ℚ := fun ell => if ¬oddPrimeRepresented p N ell then
    -(oddPrimeLeadingLiftRat p N r ell / ((j - ell : ℕ) : ℚ)) else 0
  have ht (ell : ℕ) (hell : ell ∈ Finset.range (H N - p)) :
      ((f ell).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p (f ell) =
        -(if ¬oddPrimeRepresented p N ell then
          oddPrimeLeadingV p N r ell / ((j - ell : ℕ) : ZMod p) else 0) := by
    by_cases hex : ¬oddPrimeRepresented p N ell
    · have hell' : ell < H N - p := Finset.mem_range.mp hell
      have hd0 : 0 < j - ell := by omega
      have hdlt : j - ell < p := by omega
      have hd : ((j - ell : ℕ) : ZMod p) ≠ 0 := by
        intro hzero
        exact (Nat.not_dvd_of_pos_of_lt hd0 hdlt)
          ((ZMod.natCast_eq_zero_iff _ _).mp hzero)
      have hf := nat_fraction_reduced_residue (p := p) 1 (j - ell) hd
      simp only [Nat.cast_one] at hf
      have hl := oddPrimeLeadingLiftRat_reduction (p := p) (N := N) (r := r) (ell := ell)
      have hm := rational_residue_mul hl.1 hf.1
      have hn := rational_residue_sub (p := p) (a := 0) (by norm_num) hm.1
      have heq : -(oddPrimeLeadingLiftRat p N r ell / ((j - ell : ℕ) : ℚ)) =
          0 - oddPrimeLeadingLiftRat p N r ell * (1 / ((j - ell : ℕ) : ℚ)) := by ring
      have hfr : palindromicRatResidue p (1 / ((j - ell : ℕ) : ℚ)) =
          1 / ((j - ell : ℕ) : ZMod p) := hf.2
      refine ⟨?_, ?_⟩
      · dsimp only [f]
        rw [ite_eq_left hex, heq]
        exact hn.1
      · dsimp only [f]
        rw [ite_eq_left hex, ite_eq_left hex, heq,
          palindromicRatResidue_sub (by norm_num) hm.1,
          palindromicRatResidue_mul hl.1 hf.1, hl.2, hfr]
        norm_num [palindromicRatResidue]
        ring
    · simp only [f, ite_eq_right hex]
      norm_num [palindromicRatResidue]
  have hs := rational_residue_sum (Finset.range (H N - p)) f (fun ell hell => (ht ell hell).1)
  refine ⟨hs.1, ?_⟩
  change palindromicRatResidue p (∑ ell ∈ Finset.range (H N - p), f ell) = _
  calc
    _ = ∑ ell ∈ Finset.range (H N - p), palindromicRatResidue p (f ell) := hs.2
    _ = ∑ ell ∈ Finset.range (H N - p),
        -(if ¬oddPrimeRepresented p N ell then
          oddPrimeLeadingV p N r ell / ((j - ell : ℕ) : ZMod p) else 0) :=
      Finset.sum_congr rfl (fun ell hell => (ht ell hell).2)
    _ = _ := by rw [Finset.sum_neg_distrib]

theorem oddPrimeCentralRemainderRat_den_ne_zero {p N r j : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hr : r < n N) (hpH : p ≤ H N)
    (hH : H N ≤ 2 * p) (hjlo : H N - p ≤ j) (hj : j < p)
    (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    ((oddPrimeCentralRemainderRat z p N r j).den : ZMod p) ≠ 0 := by
  have hc := oddPrimeShearedRat_scaled_reduction hp2 hN hr hpH hH hjlo hj z hz
  have he := oddPrimeExceptionalPartRat_reduction (r := r) hjlo hj z
  exact rational_remainder_den_ne_zero_of_scaled_residue_eq hc.1 he.1
    (hc.2.trans he.2.symm)

theorem oddPrimeShearedRat_eq_remainder_add_exceptional
    {p : ℕ} [Fact p.Prime] (z : ℚ) (N r j : ℕ) :
    oddPrimeShearedRat z p N r j = oddPrimeCentralRemainderRat z p N r j +
      (p : ℚ)⁻¹ * oddPrimeExceptionalPartRat z p N r j := by
  unfold oddPrimeCentralRemainderRat
  ring

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open scoped BigOperators

def oddPrimeUpperPairIndex (p N j : ℕ) : Prop :=
  p + b N ≤ j ∧ j < p + min (A N) (L N - p)

def oddPrimeUpperCentralIndex (p N j : ℕ) : Prop :=
  max (b N) (H N - p) ≤ j ∧ j < min p (L N)

instance oddPrimeUpperPairIndex_decidable (p N j : ℕ) :
    Decidable (oddPrimeUpperPairIndex p N j) :=
  inferInstanceAs (Decidable (p + b N ≤ j ∧ j < p + min (A N) (L N - p)))

instance oddPrimeUpperCentralIndex_decidable (p N j : ℕ) :
    Decidable (oddPrimeUpperCentralIndex p N j) :=
  inferInstanceAs (Decidable (max (b N) (H N - p) ≤ j ∧ j < min p (L N)))

def oddPrimeUpperPoolRat (z : ℚ) (p N r j : ℕ) : ℚ :=
  if oddPrimeUpperPairIndex p N j then
    rawEntryRat z N r j + rawEntryRat z N r (j - p)
  else if oddPrimeUpperCentralIndex p N j then oddPrimeShearedRat z p N r j
  else rawEntryRat z N r j

def oddPrimeUpperRepresentativePoolRat (z : ℚ) (p N r ell : ℕ) : ℚ :=
  if b N ≤ ell then oddPrimeUpperPoolRat z p N r ell
  else -oddPrimeUpperPoolRat z p N r (p + ell)

theorem oddPrimeUpperPoolRat_pair_low {p N j : ℕ} (hH : H N ≤ 2 * p)
    (hpair : oddPrimeUpperPairIndex p N j) (z : ℚ) (r : ℕ) :
    oddPrimeUpperPoolRat z p N r (j - p) = rawEntryRat z N r (j - p) := by
  have hpair' := hpair
  unfold oddPrimeUpperPairIndex at hpair'
  have hLH : L N ≤ H N := by unfold L H; omega
  have hKJ : L N - p ≤ H N - p := Nat.sub_le_sub_right hLH p
  have hellJ : j - p < H N - p := by omega
  have hellp : j - p < p := by omega
  have hnotpair : ¬oddPrimeUpperPairIndex p N (j - p) := by
    unfold oddPrimeUpperPairIndex
    omega
  have hnotcentral : ¬oddPrimeUpperCentralIndex p N (j - p) := by
    unfold oddPrimeUpperCentralIndex
    omega
  rw [oddPrimeUpperPoolRat, ite_eq_right hnotpair, ite_eq_right hnotcentral]

theorem oddPrimeUpperRepresentativePoolRat_eq {p N ell : ℕ}
    (hH : H N ≤ 2 * p) (hell : ell < H N - p) (z : ℚ) (r : ℕ) :
    oddPrimeUpperRepresentativePoolRat z p N r ell =
      oddPrimeRepresentativeRat z p N r ell := by
  have hellp : ell < p := by omega
  by_cases hb : b N ≤ ell
  · have hpnot : ¬oddPrimeUpperPairIndex p N ell := by
      unfold oddPrimeUpperPairIndex
      omega
    have hcnot : ¬oddPrimeUpperCentralIndex p N ell := by
      unfold oddPrimeUpperCentralIndex
      omega
    rw [oddPrimeUpperRepresentativePoolRat, ite_eq_left hb, oddPrimeUpperPoolRat,
      ite_eq_right hpnot, ite_eq_right hcnot, oddPrimeRepresentativeRat, ite_eq_left hb]
  · have hpnot : ¬oddPrimeUpperPairIndex p N (p + ell) := by
      unfold oddPrimeUpperPairIndex
      omega
    have hcnot : ¬oddPrimeUpperCentralIndex p N (p + ell) := by
      unfold oddPrimeUpperCentralIndex
      omega
    rw [oddPrimeUpperRepresentativePoolRat, ite_eq_right hb, oddPrimeUpperPoolRat,
      ite_eq_right hpnot, ite_eq_right hcnot, oddPrimeRepresentativeRat, ite_eq_right hb]

theorem rawEntryRat_eq_upper_pool_inverse {p N : ℕ} (hH : H N ≤ 2 * p)
    (z : ℚ) (r j : ℕ) :
    rawEntryRat z N r j = oddPrimeUpperPoolRat z p N r j -
      (if oddPrimeUpperPairIndex p N j then oddPrimeUpperPoolRat z p N r (j - p) else 0) -
      (if oddPrimeUpperCentralIndex p N j then
        (p : ℚ) * ∑ ell ∈ Finset.range (H N - p),
          if oddPrimeRepresented p N ell then
            oddPrimeUpperRepresentativePoolRat z p N r ell / ((j - ell : ℕ) : ℚ)
          else 0
        else 0) := by
  classical
  by_cases hpair : oddPrimeUpperPairIndex p N j
  · have hcentral : ¬oddPrimeUpperCentralIndex p N j := by
      unfold oddPrimeUpperPairIndex at hpair
      unfold oddPrimeUpperCentralIndex
      omega
    rw [ite_eq_left hpair, ite_eq_right hcentral, oddPrimeUpperPoolRat, ite_eq_left hpair,
      oddPrimeUpperPoolRat_pair_low hH hpair, sub_zero]
    ring
  · by_cases hcentral : oddPrimeUpperCentralIndex p N j
    · have hsum :
          (∑ ell ∈ Finset.range (H N - p), if oddPrimeRepresented p N ell then
            oddPrimeUpperRepresentativePoolRat z p N r ell / ((j - ell : ℕ) : ℚ) else 0) =
          ∑ ell ∈ Finset.range (H N - p), if oddPrimeRepresented p N ell then
            oddPrimeRepresentativeRat z p N r ell / ((j - ell : ℕ) : ℚ) else 0 := by
        apply Finset.sum_congr rfl
        intro ell hell
        rw [oddPrimeUpperRepresentativePoolRat_eq hH (Finset.mem_range.mp hell)]
      rw [ite_eq_right hpair, ite_eq_left hcentral, sub_zero, hsum,
        oddPrimeUpperPoolRat, ite_eq_right hpair, ite_eq_left hcentral, oddPrimeShearedRat]
      ring
    · rw [ite_eq_right hpair, ite_eq_right hcentral, sub_zero, sub_zero,
        oddPrimeUpperPoolRat, ite_eq_right hpair, ite_eq_right hcentral]

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Classical
open scoped BigOperators

abbrev oddPrimeUpperExceptionalSize (p N : ℕ) :=
  Fintype.card ↥(oddPrimeUpperExceptionalSet p N)

theorem oddPrimeUpperExceptional_sum_eq (p N : ℕ) (f : ℕ → ℚ) :
    (∑ l : Fin (oddPrimeUpperExceptionalSize p N),
      f (((Fintype.equivFin ↥(oddPrimeUpperExceptionalSet p N)).symm l).val)) =
        ∑ ell ∈ Finset.range (H N - p),
          if ¬oddPrimeRepresented p N ell then f ell else 0 := by
  have hs : oddPrimeUpperExceptionalSet p N =
      (Finset.range (H N - p)).filter (fun ell => ¬oddPrimeRepresented p N ell) := by
    ext ell
    constructor
    · intro h
      have he := (oddPrimeUpperExceptionalSet_mem_iff p N ell).mp h
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr he.1, he.2⟩
    · intro h
      have he := Finset.mem_filter.mp h
      exact (oddPrimeUpperExceptionalSet_mem_iff p N ell).mpr
        ⟨Finset.mem_range.mp he.1, he.2⟩
  calc
    _ = ∑ ell : ↥(oddPrimeUpperExceptionalSet p N), f ell.val :=
      Equiv.sum_comp (Fintype.equivFin ↥(oddPrimeUpperExceptionalSet p N)).symm
        (fun ell => f ell.val)
    _ = ∑ ell ∈ oddPrimeUpperExceptionalSet p N, f ell :=
      Finset.sum_coe_sort (oddPrimeUpperExceptionalSet p N) f
    _ = _ := by rw [hs, Finset.sum_filter]

theorem oddPrimeUpperExceptional_combination_eq {p : ℕ} [Fact p.Prime]
    (z : ℚ) (N r j : ℕ) :
    (∑ l : Fin (oddPrimeUpperExceptionalSize p N),
      (-1 / ((j - ((Fintype.equivFin ↥(oddPrimeUpperExceptionalSet p N)).symm l).val : ℕ) : ℚ)) *
        oddPrimeLeadingLiftRat p N r
          ((Fintype.equivFin ↥(oddPrimeUpperExceptionalSet p N)).symm l).val) =
      oddPrimeExceptionalPartRat z p N r j := by
  rw [oddPrimeUpperExceptional_sum_eq p N
    (fun ell => (-1 / ((j - ell : ℕ) : ℚ)) * oddPrimeLeadingLiftRat p N r ell)]
  unfold oddPrimeExceptionalPartRat
  apply Finset.sum_congr rfl
  intro ell hell
  by_cases hex : ¬oddPrimeRepresented p N ell
  · rw [ite_eq_left hex, ite_eq_left hex]
    ring
  · rw [ite_eq_right hex, ite_eq_right hex]

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Classical
open scoped BigOperators

abbrev oddPrimeUpperRetainedSize (p N : ℕ) := Fintype.card ↥(oddPrimeUpperRetainedSet p N)
abbrev oddPrimeUpperPairedSize (p N : ℕ) := Fintype.card ↥(oddPrimeUpperPairHighSet p N)
abbrev oddPrimeUpperCentralSize (p N : ℕ) := Fintype.card ↥(oddPrimeUpperCentralSet p N)
abbrev oddPrimeUpperPhysicalIndex (p N : ℕ) :=
  oddPhysicalIndex (oddPrimeUpperRetainedSize p N) (oddPrimeUpperPairedSize p N)
    (oddPrimeUpperCentralSize p N)

def oddPrimeUpperRetainedVector (z : ℚ) (p N : ℕ)
    (j : Fin (oddPrimeUpperRetainedSize p N)) (r : Fin (n N)) : ℚ :=
  (p : ℚ) ^ 2 * rawEntryRat z N r.val
    (((Fintype.equivFin ↥(oddPrimeUpperRetainedSet p N)).symm j).val)

def oddPrimeUpperPairedVector (z : ℚ) (p N : ℕ)
    (j : Fin (oddPrimeUpperPairedSize p N)) (r : Fin (n N)) : ℚ :=
  let v := ((Fintype.equivFin ↥(oddPrimeUpperPairHighSet p N)).symm j).val
  (p : ℚ) * (rawEntryRat z N r.val v + rawEntryRat z N r.val (v - p))

def oddPrimeUpperIntegralVector (z : ℚ) (p N : ℕ) [Fact p.Prime]
    (j : Fin (oddPrimeUpperCentralSize p N)) (r : Fin (n N)) : ℚ :=
  oddPrimeCentralRemainderRat z p N r.val
    (((Fintype.equivFin ↥(oddPrimeUpperCentralSet p N)).symm j).val)

def oddPrimeUpperExceptionalVector (p N : ℕ) [Fact p.Prime]
    (ell : Fin (oddPrimeUpperExceptionalSize p N)) (r : Fin (n N)) : ℚ :=
  oddPrimeLeadingLiftRat p N r.val
    (((Fintype.equivFin ↥(oddPrimeUpperExceptionalSet p N)).symm ell).val)

def oddPrimeUpperExceptionalCoeff (p N : ℕ)
    (j : Fin (oddPrimeUpperCentralSize p N))
    (ell : Fin (oddPrimeUpperExceptionalSize p N)) : ℚ :=
  let v := ((Fintype.equivFin ↥(oddPrimeUpperCentralSet p N)).symm j).val
  let l := ((Fintype.equivFin ↥(oddPrimeUpperExceptionalSet p N)).symm ell).val
  (-1 : ℚ) / ((v - l : ℕ) : ℚ)

def oddPrimeUpperPhysicalColumn (z : ℚ) (p N : ℕ) [Fact p.Prime]
    (j : oddPrimeUpperPhysicalIndex p N) (r : Fin (n N)) : ℚ :=
  oddPhysicalColumn p (oddPrimeUpperRetainedVector z p N)
    (oddPrimeUpperPairedVector z p N) (oddPrimeUpperIntegralVector z p N)
    (oddPrimeUpperExceptionalVector p N) (oddPrimeUpperExceptionalCoeff p N) j r

theorem oddPrimeUpperRetainedVector_den_ne_zero {p N : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hHsq : H N < p ^ 2) (z : ℚ) (hz : (z.den : ZMod p) ≠ 0)
    (j : Fin (oddPrimeUpperRetainedSize p N)) (r : Fin (n N)) :
    ((oddPrimeUpperRetainedVector z p N j r).den : ZMod p) ≠ 0 := by
  let v := (Fintype.equivFin ↥(oddPrimeUpperRetainedSet p N)).symm j
  have hraw := oddPrimeUpperRetainedSet_subset_raw p N v.property
  have hvL := (Finset.mem_Ico.mp hraw).2
  have hvH : v.val < H N := by unfold L H at *; omega
  exact (rawEntryRat_prime_digit_reduction (r := r.val) hp2 hHsq hvH z hz).1

theorem oddPrimeUpperPairedVector_den_ne_zero {p N : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hpH : p ≤ H N) (hH : H N ≤ 2 * p)
    (z : ℚ) (hz : (z.den : ZMod p) ≠ 0)
    (j : Fin (oddPrimeUpperPairedSize p N)) (r : Fin (n N)) :
    ((oddPrimeUpperPairedVector z p N j r).den : ZMod p) ≠ 0 := by
  let v := (Fintype.equivFin ↥(oddPrimeUpperPairHighSet p N)).symm j
  obtain ⟨ell, hb, hell, hveq⟩ :=
    (oddPrimeUpperPairHighSet_mem_iff p N v.val).mp v.property
  have hbounds := oddPrimeUpperPairIndex_bounds hN hpH hH
    (Finset.mem_Ico.mpr ⟨hb, hell⟩)
  have hsub : v.val - p = ell := by omega
  have hwidth : H N ≤ ell + 2 * p := by omega
  have hhigh : p + ell < H N := by have := hbounds.2.2.2; omega
  have hA : ell ≤ A N := by omega
  have hpair := rawEntryRat_pair_prime_scaled_den_ne_zero hp2 hN r.isLt
    hbounds.2.2.1 hwidth hhigh hA z hz
  change (((p : ℚ) * (rawEntryRat z N r.val v.val +
    rawEntryRat z N r.val (v.val - p))).den : ZMod p) ≠ 0
  rw [hsub, hveq, add_comm (rawEntryRat z N r.val (p + ell)) (rawEntryRat z N r.val ell)]
  exact hpair

theorem oddPrimeUpperIntegralVector_den_ne_zero {p N : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hpH : p ≤ H N) (hH : H N ≤ 2 * p)
    (z : ℚ) (hz : (z.den : ZMod p) ≠ 0)
    (j : Fin (oddPrimeUpperCentralSize p N)) (r : Fin (n N)) :
    ((oddPrimeUpperIntegralVector z p N j r).den : ZMod p) ≠ 0 := by
  let v := (Fintype.equivFin ↥(oddPrimeUpperCentralSet p N)).symm j
  have hv := (oddPrimeUpperCentralSet_mem_iff p N v.val).mp v.property
  exact oddPrimeCentralRemainderRat_den_ne_zero hp2 hN r.isLt hpH hH
    hv.2.2.1 hv.2.2.2 z hz

theorem oddPrimeUpperExceptionalVector_den_ne_zero {p N : ℕ} [Fact p.Prime]
    (ell : Fin (oddPrimeUpperExceptionalSize p N)) (r : Fin (n N)) :
    ((oddPrimeUpperExceptionalVector p N ell r).den : ZMod p) ≠ 0 :=
  (oddPrimeLeadingLiftRat_reduction (p := p) (N := N) (r := r.val)
    (ell := ((Fintype.equivFin ↥(oddPrimeUpperExceptionalSet p N)).symm ell).val)).1

theorem oddPrimeUpperExceptionalCoeff_den_ne_zero {p N : ℕ} [Fact p.Prime]
    (j : Fin (oddPrimeUpperCentralSize p N))
    (ell : Fin (oddPrimeUpperExceptionalSize p N)) :
    ((oddPrimeUpperExceptionalCoeff p N j ell).den : ZMod p) ≠ 0 := by
  let v := (Fintype.equivFin ↥(oddPrimeUpperCentralSet p N)).symm j
  let l := (Fintype.equivFin ↥(oddPrimeUpperExceptionalSet p N)).symm ell
  have hv := (oddPrimeUpperCentralSet_mem_iff p N v.val).mp v.property
  have hl := (oddPrimeUpperExceptionalSet_mem_iff p N l.val).mp l.property
  have hdpos : 0 < v.val - l.val := by omega
  have hdlt : v.val - l.val < p := by omega
  have hd : ((v.val - l.val : ℕ) : ZMod p) ≠ 0 := by
    intro hzero
    exact (Nat.not_dvd_of_pos_of_lt hdpos hdlt)
      ((ZMod.natCast_eq_zero_iff _ _).mp hzero)
  have hf := nat_fraction_reduced_residue (p := p) 1 (v.val - l.val) hd
  change (((-1 : ℚ) / ((v.val - l.val : ℕ) : ℚ)).den : ZMod p) ≠ 0
  simpa only [Nat.cast_one, neg_div, Rat.neg_den] using hf.1

theorem oddPrimeUpperExceptionalVector_combination {p N : ℕ} [Fact p.Prime]
    (z : ℚ) (j : Fin (oddPrimeUpperCentralSize p N)) (r : Fin (n N)) :
    (∑ ell : Fin (oddPrimeUpperExceptionalSize p N),
      oddPrimeUpperExceptionalCoeff p N j ell * oddPrimeUpperExceptionalVector p N ell r) =
      oddPrimeExceptionalPartRat z p N r.val
        (((Fintype.equivFin ↥(oddPrimeUpperCentralSet p N)).symm j).val) := by
  simpa only [oddPrimeUpperExceptionalCoeff, oddPrimeUpperExceptionalVector] using
    oddPrimeUpperExceptional_combination_eq (p := p) z N r.val
      (((Fintype.equivFin ↥(oddPrimeUpperCentralSet p N)).symm j).val)

theorem oddPrimeUpperPhysicalColumn_eq_pool {p N : ℕ} [hp : Fact p.Prime]
    (z : ℚ) (phys : oddPrimeUpperPhysicalIndex p N) (r : Fin (n N)) :
    oddPrimeUpperPhysicalColumn z p N phys r =
      oddPrimeUpperPoolRat z p N r.val ((oddPrimeUpperPoolEnumeration p N phys).val) := by
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rcases phys with j | (j | j)
  · let v := (Fintype.equivFin ↥(oddPrimeUpperRetainedSet p N)).symm j
    have hnot := (Finset.mem_sdiff.mp v.property).2
    have hnotpair : ¬oddPrimeUpperPairIndex p N v.val := by
      intro hpair
      have hmem : v.val ∈ oddPrimeUpperPairHighSet p N := by
        simpa only [oddPrimeUpperPairIndex, oddPrimeUpperPairHighSet, Finset.mem_Ico] using hpair
      exact hnot (Finset.mem_union.mpr (Or.inl hmem))
    have hnotcentral : ¬oddPrimeUpperCentralIndex p N v.val := by
      intro hcentral
      have hmem : v.val ∈ oddPrimeUpperCentralSet p N := by
        simpa only [oddPrimeUpperCentralIndex, oddPrimeUpperCentralSet, Finset.mem_Ico] using hcentral
      exact hnot (Finset.mem_union.mpr (Or.inr hmem))
    simp only [oddPrimeUpperPhysicalColumn, oddPhysicalColumn,
      oddPrimeUpperRetainedVector, oddPrimeUpperPoolEnumeration_retained_val]
    change ((p : ℚ) ^ 2)⁻¹ * ((p : ℚ) ^ 2 * rawEntryRat z N r.val v.val) =
      oddPrimeUpperPoolRat z p N r.val v.val
    rw [oddPrimeUpperPoolRat, ite_eq_right hnotpair, ite_eq_right hnotcentral]
    field_simp [hpq]
  · let v := (Fintype.equivFin ↥(oddPrimeUpperPairHighSet p N)).symm j
    have hpair : oddPrimeUpperPairIndex p N v.val := by
      simpa only [oddPrimeUpperPairIndex, oddPrimeUpperPairHighSet, Finset.mem_Ico] using v.property
    simp only [oddPrimeUpperPhysicalColumn, oddPhysicalColumn,
      oddPrimeUpperPairedVector, oddPrimeUpperPoolEnumeration_pairHigh_val]
    change (p : ℚ)⁻¹ * ((p : ℚ) * (rawEntryRat z N r.val v.val +
      rawEntryRat z N r.val (v.val - p))) = oddPrimeUpperPoolRat z p N r.val v.val
    rw [oddPrimeUpperPoolRat, ite_eq_left hpair]
    field_simp [hpq]
  · let v := (Fintype.equivFin ↥(oddPrimeUpperCentralSet p N)).symm j
    have hcentral : oddPrimeUpperCentralIndex p N v.val := by
      simpa only [oddPrimeUpperCentralIndex, oddPrimeUpperCentralSet, Finset.mem_Ico] using v.property
    have hnotpair : ¬oddPrimeUpperPairIndex p N v.val := by
      intro hpair
      have hmem : v.val ∈ oddPrimeUpperPairHighSet p N := by
        simpa only [oddPrimeUpperPairIndex, oddPrimeUpperPairHighSet, Finset.mem_Ico] using hpair
      exact (Finset.disjoint_left.mp (oddPrimeUpperPairHighSet_disjoint_central p N)) hmem v.property
    have hsum := oddPrimeUpperExceptionalVector_combination (p := p) (N := N) z j r
    simp only [oddPrimeUpperPhysicalColumn, oddPhysicalColumn,
      oddPrimeUpperPoolEnumeration_central_val]
    rw [hsum]
    change oddPrimeCentralRemainderRat z p N r.val v.val +
      (p : ℚ)⁻¹ * oddPrimeExceptionalPartRat z p N r.val v.val =
        oddPrimeUpperPoolRat z p N r.val v.val
    rw [oddPrimeUpperPoolRat, ite_eq_right hnotpair, ite_eq_left hcentral]
    exact (oddPrimeShearedRat_eq_remainder_add_exceptional (p := p) z N r.val v.val).symm

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Classical
open scoped BigOperators

def oddPrimeUpperDelta (p N : ℕ) (phys : oddPrimeUpperPhysicalIndex p N)
    (j : ℕ) : ℚ :=
  if (oddPrimeUpperPoolEnumeration p N phys).val = j then 1 else 0

def oddPrimeUpperRepresentativeNumber (p N ell : ℕ) : ℕ :=
  if b N ≤ ell then ell else p + ell

def oddPrimeUpperRepresentativeSign (N ell : ℕ) : ℚ :=
  if b N ≤ ell then 1 else -1

def oddPrimeUpperShearCoeff (p N : ℕ) (phys : oddPrimeUpperPhysicalIndex p N)
    (j ell : ℕ) : ℚ :=
  if oddPrimeRepresented p N ell then
    (oddPrimeUpperRepresentativeSign N ell / ((j - ell : ℕ) : ℚ)) *
      oddPrimeUpperDelta p N phys (oddPrimeUpperRepresentativeNumber p N ell)
  else 0

def oddPrimeUpperInverseCoeff (p N : ℕ) (phys : oddPrimeUpperPhysicalIndex p N)
    (j : ℕ) : ℚ :=
  oddPrimeUpperDelta p N phys j -
    (if oddPrimeUpperPairIndex p N j then oddPrimeUpperDelta p N phys (j - p) else 0) -
    (if oddPrimeUpperCentralIndex p N j then
      (p : ℚ) * ∑ ell ∈ Finset.range (H N - p),
        oddPrimeUpperShearCoeff p N phys j ell
    else 0)

end InternalCatalan

end



namespace InternalCatalan

open Classical
open scoped BigOperators

private theorem upper_delta_den_ne_zero {p N : ℕ} [Fact p.Prime]
    (phys : oddPrimeUpperPhysicalIndex p N) (j : ℕ) :
    ((oddPrimeUpperDelta p N phys j).den : ZMod p) ≠ 0 := by
  unfold oddPrimeUpperDelta
  split_ifs <;> norm_num

private theorem upper_sign_den_ne_zero {p : ℕ} [Fact p.Prime] (N ell : ℕ) :
    ((oddPrimeUpperRepresentativeSign N ell).den : ZMod p) ≠ 0 := by
  unfold oddPrimeUpperRepresentativeSign
  split_ifs <;> norm_num

private theorem upper_shearCoeff_den_ne_zero {p N : ℕ} [Fact p.Prime]
    (phys : oddPrimeUpperPhysicalIndex p N) (j ell : ℕ)
    (hc : oddPrimeUpperCentralIndex p N j) (hell : ell ∈ Finset.range (H N - p)) :
    ((oddPrimeUpperShearCoeff p N phys j ell).den : ZMod p) ≠ 0 := by
  have hc' : max (b N) (H N - p) ≤ j ∧ j < min p (L N) := hc
  have he : ell < H N - p := Finset.mem_range.mp hell
  have hjlo : H N - p ≤ j := (Nat.le_max_right _ _).trans hc'.1
  have hj : j < p := hc'.2.trans_le (Nat.min_le_left _ _)
  have hdpos : 0 < j - ell := by omega
  have hdlt : j - ell < p := by omega
  have hd : ((j - ell : ℕ) : ZMod p) ≠ 0 := by
    intro hzero
    exact (Nat.not_dvd_of_pos_of_lt hdpos hdlt)
      ((ZMod.natCast_eq_zero_iff _ _).mp hzero)
  unfold oddPrimeUpperShearCoeff
  split_ifs with hrep
  · have hinv := nat_fraction_reduced_residue (p := p) 1 (j - ell) hd
    simp only [Nat.cast_one] at hinv
    have hsign := upper_sign_den_ne_zero (p := p) N ell
    have hmul := rational_residue_mul hsign hinv.1
    have hfrac :
        ((oddPrimeUpperRepresentativeSign N ell / ((j - ell : ℕ) : ℚ)).den : ZMod p) ≠ 0 := by
      have heq : oddPrimeUpperRepresentativeSign N ell / ((j - ell : ℕ) : ℚ) =
          oddPrimeUpperRepresentativeSign N ell * (1 / ((j - ell : ℕ) : ℚ)) := by ring
      rw [heq]
      exact hmul.1
    exact (rational_residue_mul hfrac
      (upper_delta_den_ne_zero phys (oddPrimeUpperRepresentativeNumber p N ell))).1
  · norm_num

theorem oddPrimeUpperInverseCoeff_den_ne_zero {p N : ℕ} [Fact p.Prime]
    (phys : oddPrimeUpperPhysicalIndex p N) (j : ℕ) :
    ((oddPrimeUpperInverseCoeff p N phys j).den : ZMod p) ≠ 0 := by
  have hbase := upper_delta_den_ne_zero phys j
  have hpair :
      ((if oddPrimeUpperPairIndex p N j then oddPrimeUpperDelta p N phys (j - p)
        else 0).den : ZMod p) ≠ 0 := by
    split_ifs
    · exact upper_delta_den_ne_zero phys (j - p)
    · norm_num
  have hleft := rational_residue_sub hbase hpair
  have hcentral :
      ((if oddPrimeUpperCentralIndex p N j then
          (p : ℚ) * ∑ ell ∈ Finset.range (H N - p), oddPrimeUpperShearCoeff p N phys j ell
        else 0).den : ZMod p) ≠ 0 := by
    split_ifs with hc
    · have hsum := rational_residue_sum (Finset.range (H N - p))
        (fun ell => oddPrimeUpperShearCoeff p N phys j ell)
        (fun ell hell => upper_shearCoeff_den_ne_zero phys j ell hc hell)
      exact (rational_residue_mul (a := (p : ℚ)) (by simp) hsum.1).1
    · norm_num
  exact (rational_residue_sub hleft.1 hcentral).1

end InternalCatalan



noncomputable section

namespace InternalCatalan

open Classical
open scoped BigOperators

theorem oddPrimeUpperDelta_sum {p N : ℕ} [Fact p.Prime]
    (z : ℚ) (r : Fin (n N)) (j : ℕ) (hj : j ∈ Finset.Ico (b N) (L N)) :
    (∑ phys : oddPrimeUpperPhysicalIndex p N,
      oddPrimeUpperPhysicalColumn z p N phys r * oddPrimeUpperDelta p N phys j) =
        oddPrimeUpperPoolRat z p N r.val j := by
  let e := oddPrimeUpperPoolEnumeration p N
  let v : ↥(Finset.Ico (b N) (L N)) := ⟨j, hj⟩
  have htag (phys : oddPrimeUpperPhysicalIndex p N) :
      (oddPrimeUpperPoolEnumeration p N phys).val = j ↔ phys = e.symm v := by
    constructor
    · intro h
      have he : e phys = v := Subtype.ext h
      calc
        phys = e.symm (e phys) := (e.symm_apply_apply phys).symm
        _ = e.symm v := congrArg e.symm he
    · rintro rfl
      exact congrArg Subtype.val (e.apply_symm_apply v)
  simp only [oddPrimeUpperDelta, htag, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simpa only [e, Equiv.apply_symm_apply] using
    oddPrimeUpperPhysicalColumn_eq_pool z (e.symm v) r

theorem oddPrimeUpperRepresentativeNumber_mem {p N ell : ℕ}
    (hN : 0 < N) (hH : H N ≤ 2 * p) (hell : ell < H N - p)
    (hrep : oddPrimeRepresented p N ell) :
    oddPrimeUpperRepresentativeNumber p N ell ∈ Finset.Ico (b N) (L N) := by
  have hbp : b N < p := by unfold b H at *; omega
  have hJL : H N - p ≤ L N := by unfold H L at *; omega
  unfold oddPrimeUpperRepresentativeNumber
  by_cases hb : b N ≤ ell
  · rw [ite_eq_left hb]
    exact Finset.mem_Ico.mpr ⟨hb, by omega⟩
  · rw [ite_eq_right hb]
    unfold oddPrimeRepresented at hrep
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩

theorem oddPrimeUpperRepresentativePoolRat_eq_sign (z : ℚ) (p N r ell : ℕ) :
    oddPrimeUpperRepresentativePoolRat z p N r ell =
      oddPrimeUpperRepresentativeSign N ell *
        oddPrimeUpperPoolRat z p N r (oddPrimeUpperRepresentativeNumber p N ell) := by
  by_cases hb : b N ≤ ell <;>
    simp only [oddPrimeUpperRepresentativePoolRat, oddPrimeUpperRepresentativeSign,
      oddPrimeUpperRepresentativeNumber, hb, ite_true, ite_false, one_mul, neg_one_mul]

theorem oddPrimeUpperShearCoeff_sum {p N : ℕ} [Fact p.Prime]
    (hN : 0 < N) (hH : H N ≤ 2 * p) (z : ℚ) (r : Fin (n N))
    (j ell : ℕ) (hell : ell < H N - p) :
    (∑ phys : oddPrimeUpperPhysicalIndex p N,
      oddPrimeUpperPhysicalColumn z p N phys r * oddPrimeUpperShearCoeff p N phys j ell) =
      if oddPrimeRepresented p N ell then
        oddPrimeUpperRepresentativePoolRat z p N r.val ell / ((j - ell : ℕ) : ℚ)
      else 0 := by
  by_cases hrep : oddPrimeRepresented p N ell
  · simp only [oddPrimeUpperShearCoeff, ite_eq_left hrep]
    calc
      _ = (oddPrimeUpperRepresentativeSign N ell / ((j - ell : ℕ) : ℚ)) *
          ∑ phys : oddPrimeUpperPhysicalIndex p N,
            oddPrimeUpperPhysicalColumn z p N phys r *
              oddPrimeUpperDelta p N phys (oddPrimeUpperRepresentativeNumber p N ell) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro phys _
        ring
      _ = _ := by
        rw [oddPrimeUpperDelta_sum z r _
          (oddPrimeUpperRepresentativeNumber_mem hN hH hell hrep),
          oddPrimeUpperRepresentativePoolRat_eq_sign]
        ring
  · simp only [oddPrimeUpperShearCoeff, ite_eq_right hrep, mul_zero, Finset.sum_const_zero]

theorem rawEntryRat_eq_upper_physical_sum {p N : ℕ} [Fact p.Prime]
    (hN : 0 < N) (hH : H N ≤ 2 * p) (z : ℚ)
    (j : ↥(Finset.Ico (b N) (L N))) (r : Fin (n N)) :
    rawEntryRat z N r.val j.val =
      ∑ phys : oddPrimeUpperPhysicalIndex p N,
        oddPrimeUpperPhysicalColumn z p N phys r * oddPrimeUpperInverseCoeff p N phys j.val := by
  have hpairSum :
      (∑ phys : oddPrimeUpperPhysicalIndex p N,
        oddPrimeUpperPhysicalColumn z p N phys r *
          (if oddPrimeUpperPairIndex p N j.val then
            oddPrimeUpperDelta p N phys (j.val - p) else 0)) =
      if oddPrimeUpperPairIndex p N j.val then
        oddPrimeUpperPoolRat z p N r.val (j.val - p) else 0 := by
    by_cases hp : oddPrimeUpperPairIndex p N j.val
    · simp only [ite_eq_left hp]
      apply oddPrimeUpperDelta_sum
      have hj := Finset.mem_Ico.mp j.property
      unfold oddPrimeUpperPairIndex at hp
      exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    · simp only [ite_eq_right hp, mul_zero, Finset.sum_const_zero]
  have hcentralSum :
      (∑ phys : oddPrimeUpperPhysicalIndex p N,
        oddPrimeUpperPhysicalColumn z p N phys r *
          (if oddPrimeUpperCentralIndex p N j.val then
            (p : ℚ) * ∑ ell ∈ Finset.range (H N - p),
              oddPrimeUpperShearCoeff p N phys j.val ell else 0)) =
      if oddPrimeUpperCentralIndex p N j.val then
        (p : ℚ) * ∑ ell ∈ Finset.range (H N - p),
          if oddPrimeRepresented p N ell then
            oddPrimeUpperRepresentativePoolRat z p N r.val ell / ((j.val - ell : ℕ) : ℚ)
          else 0
      else 0 := by
    by_cases hc : oddPrimeUpperCentralIndex p N j.val
    · simp only [ite_eq_left hc]
      calc
        _ = (p : ℚ) * ∑ phys : oddPrimeUpperPhysicalIndex p N,
              ∑ ell ∈ Finset.range (H N - p),
                oddPrimeUpperPhysicalColumn z p N phys r *
                  oddPrimeUpperShearCoeff p N phys j.val ell := by
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro phys _
          apply Finset.sum_congr rfl
          intro ell _
          ring
        _ = (p : ℚ) * ∑ ell ∈ Finset.range (H N - p),
              ∑ phys : oddPrimeUpperPhysicalIndex p N,
                oddPrimeUpperPhysicalColumn z p N phys r *
                  oddPrimeUpperShearCoeff p N phys j.val ell := by
          rw [Finset.sum_comm]
        _ = _ := by
          congr 1
          apply Finset.sum_congr rfl
          intro ell hell
          exact oddPrimeUpperShearCoeff_sum hN hH z r j.val ell (Finset.mem_range.mp hell)
    · simp only [ite_eq_right hc, mul_zero, Finset.sum_const_zero]
  rw [rawEntryRat_eq_upper_pool_inverse hH]
  symm
  simp only [oddPrimeUpperInverseCoeff, mul_sub, Finset.sum_sub_distrib]
  rw [oddPrimeUpperDelta_sum z r j.val j.property, hpairSum, hcentralSum]

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Classical
open scoped BigOperators

theorem oddPrimeUpperPhysical_loss_eq {N p : ℕ} (hN : 0 < N)
    (hpH : p ≤ H N) (hH : H N ≤ 2 * p) :
    min (2 * n N) (min (n N + oddPrimeUpperRetainedSize p N)
      (2 * oddPrimeUpperRetainedSize p N + oddPrimeUpperPairedSize p N +
        oddPrimeUpperExceptionalSize p N)) = oddUpperCountLoss N p := by
  have hR : oddPrimeUpperRetainedSize p N = oddUpperRankCount N p := by
    simpa only [oddPrimeUpperRetainedSize, Fintype.card_coe,
      oddPrimeUpperRetainedSet_card] using oddUpperRetainedCount_eq N p hN hpH hH
  have hS : oddPrimeUpperPairedSize p N + oddPrimeUpperExceptionalSize p N =
      oddUpperSimpleCount N p := by
    simpa only [oddPrimeUpperPairedSize, oddPrimeUpperExceptionalSize, Fintype.card_coe,
      oddPrimeUpperPairHighSet_card, oddPrimeUpperExceptionalSet_card] using
        oddUpperSimplePhysicalCount_eq N p
  unfold oddUpperCountLoss
  omega

theorem oddPrimeUpperPhysicalCombination_valuation_lower {N p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hpH : p ≤ H N) (hH : H N ≤ 2 * p)
    (hHsq : H N < p ^ 2) (z : ℚ) (hz : (z.den : ZMod p) ≠ 0)
    (g : oddPrimeUpperPhysicalIndex p N → Fin (n N) → ℚ)
    (hg : ∀ i k, ((g i k).den : ZMod p) ≠ 0) :
    -(oddUpperCountLoss N p : ℤ) ≤ padicValRat p
      (Matrix.det (Matrix.of fun r k : Fin (n N) =>
        ∑ i, oddPrimeUpperPhysicalColumn z p N i r * g i k)) := by
  have h := oddPhysicalCombination_valuation_lower
    (p := p) (n := n N) (R := oddPrimeUpperRetainedSize p N)
    (B := oddPrimeUpperPairedSize p N) (C := oddPrimeUpperCentralSize p N)
    (e := oddPrimeUpperExceptionalSize p N)
    (oddPrimeUpperRetainedVector z p N) (oddPrimeUpperPairedVector z p N)
    (oddPrimeUpperIntegralVector z p N) (oddPrimeUpperExceptionalVector p N)
    (oddPrimeUpperExceptionalCoeff p N) g
    (oddPrimeUpperRetainedVector_den_ne_zero hp2 hHsq z hz)
    (oddPrimeUpperPairedVector_den_ne_zero hp2 hN hpH hH z hz)
    (oddPrimeUpperIntegralVector_den_ne_zero hp2 hN hpH hH z hz)
    oddPrimeUpperExceptionalVector_den_ne_zero
    oddPrimeUpperExceptionalCoeff_den_ne_zero hg
  simpa only [oddPrimeUpperPhysical_loss_eq hN hpH hH, oddPrimeUpperPhysicalColumn] using h

theorem rawMinorRat_odd_upper_valuation {N p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hpH : p ≤ H N) (hH : H N ≤ 2 * p)
    (hHsq : H N < p ^ 2) (z : ℚ) (hz : (z.den : ZMod p) ≠ 0)
    (c : Fin (n N) → ↥(Finset.Ico (b N) (L N))) :
    -(oddUpperCountLoss N p : ℤ) ≤ padicValRat p (rawMinorRat z N c) := by
  have hmatrix :
      (Matrix.of fun r k : Fin (n N) => rawEntryRat z N r.val (c k).val) =
        (Matrix.of fun r k : Fin (n N) => ∑ i : oddPrimeUpperPhysicalIndex p N,
          oddPrimeUpperPhysicalColumn z p N i r * oddPrimeUpperInverseCoeff p N i (c k).val) := by
    ext r k
    exact rawEntryRat_eq_upper_physical_sum hN hH z (c k) r
  rw [rawMinorRat, hmatrix]
  exact oddPrimeUpperPhysicalCombination_valuation_lower hp2 hN hpH hH hHsq z hz
    (fun i k => oddPrimeUpperInverseCoeff p N i (c k).val)
    (fun i k => oddPrimeUpperInverseCoeff_den_ne_zero i (c k).val)

theorem determinantRat_odd_upper_valuation {N p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hpH : p ≤ H N) (hH : H N ≤ 2 * p)
    (hHsq : H N < p ^ 2) (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    -(oddUpperCountLoss N p : ℤ) ≤ padicValRat p (determinantRat z N) := by
  rw [determinantRat_eq_sum_raw_choices]
  apply prime_sum_valuation_lower _ _ _ (by omega)
  intro c hc
  have hminor := rawMinorRat_odd_upper_valuation hp2 hN hpH hH hHsq z hz c
  have hint := int_prime_valuation_nonneg p (∏ k, rawFilterInt N (c k) k)
  simpa only [zero_add] using prime_mul_valuation_lower
    (((∏ k, rawFilterInt N (c k) k : ℤ) : ℚ)) (rawMinorRat z N c)
    0 (-(oddUpperCountLoss N p : ℤ)) (by omega) hint hminor

theorem determinantRat_odd_prime_loss_upper {N p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hpH : p ≤ H N) (hH : H N ≤ 2 * p)
    (hHsq : H N < p ^ 2) (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    -(N : ℝ) * oddPrimeLoss ((p : ℝ) / N) ≤
      (padicValRat p (determinantRat z N) : ℝ) := by
  have hv : -(oddUpperCountLoss N p : ℝ) ≤
      (padicValRat p (determinantRat z N) : ℝ) := by
    exact_mod_cast determinantRat_odd_upper_valuation hp2 hN hpH hH hHsq z hz
  rw [oddUpperCountLoss_eq N p hN hH] at hv
  simpa only [neg_mul] using hv

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open Filter
open scoped Topology BigOperators

theorem determinantRat_odd_prime_large_loss_lower {p N : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N)
    (hcut : 2 * Real.sqrt (H N) < (p : ℝ))
    (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    -(N : ℝ) * oddPrimeLoss ((p : ℝ) / N) ≤
      (padicValRat p (determinantRat z N) : ℝ) := by
  have hsquare : H N < p ^ 2 := by
    have h := large_prime_cutoff_square hcut
    omega
  by_cases hbelow : p ≤ H N
  · by_cases hlower : 2 * p ≤ H N
    · exact determinantRat_odd_lower_loss hp2 hN hlower hsquare z hz
    · exact determinantRat_odd_prime_loss_upper hp2 hN hbelow (by omega) hsquare z hz
  · exact determinantRat_odd_prime_loss_above_degrees hp2 hN (by omega) z hz

theorem largeOddPrimeContribution_eventually_lower (z : ℚ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      -(8609 / 4608 : ℝ) - ε ≤ largeOddPrimeContribution z N / (n N : ℝ) ^ 2 := by
  filter_upwards [large_prime_witness_den_eventually z,
    oddPrimeLoss_large_prime_normalized_eventually_upper hε,
    eventually_gt_atTop (0 : ℕ)] with N hden hloss hN
  have hn : 0 < (n N : ℝ) ^ 2 := by unfold n; positivity
  have hsum : -(N : ℝ) *
      (∑ p ∈ (Finset.Ioc 0 (H N)).filter
        (fun p : ℕ => p.Prime ∧ 2 * Real.sqrt (H N) < (p : ℝ)),
        oddPrimeLoss ((p : ℝ) / N) * Real.log p) ≤ largeOddPrimeContribution z N := by
    unfold largeOddPrimeContribution
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨_, hprime, hcut⟩ := Finset.mem_filter.mp hp
    have : Fact p.Prime := ⟨hprime⟩
    have hp2 : p ≠ 2 := by
      intro heq
      subst p
      have h := (smallOddPrimeCutoff_bounds hN).1
      norm_num only [Nat.cast_ofNat] at hcut
      linarith
    have hv := determinantRat_odd_prime_large_loss_lower hp2 hN hcut z (hden p hcut)
    have hlog : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hprime.one_lt.le)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hv hlog
  have hnorm := div_le_div_of_nonneg_right hsum hn.le
  have heq : -(N : ℝ) *
      (∑ p ∈ (Finset.Ioc 0 (H N)).filter
        (fun p : ℕ => p.Prime ∧ 2 * Real.sqrt (H N) < (p : ℝ)),
        oddPrimeLoss ((p : ℝ) / N) * Real.log p) / (n N : ℝ) ^ 2 =
      -((N : ℝ) *
      (∑ p ∈ (Finset.Ioc 0 (H N)).filter
        (fun p : ℕ => p.Prime ∧ 2 * Real.sqrt (H N) < (p : ℝ)),
        oddPrimeLoss ((p : ℝ) / N) * Real.log p) / (n N : ℝ) ^ 2) := by ring
  rw [heq] at hnorm
  linarith

end InternalCatalan

end



namespace InternalCatalan
open Filter
open scoped Topology

theorem determinantRat_finite_place_eventually_lower (z : ℚ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, determinantRat z N ≠ 0 →
      -(8609 / 4608 : ℝ) - (505 / 4608 : ℝ) * Real.log 2 - ε ≤
        Real.log |(determinantRat z N : ℝ)| / (n N : ℝ) ^ 2 := by
  have he : (0 : ℝ) < ε / 2 := by positivity
  filter_upwards [determinantRat_without_large_primes_eventually_lower z he,
    largeOddPrimeContribution_eventually_lower z he] with N hpartial hlarge
  intro hdet
  have h := hpartial hdet
  rw [sub_div] at h
  linarith

theorem determinantRat_finite_place_threshold (z : ℚ) :
    ∀ᶠ N : ℕ in atTop, determinantRat z N ≠ 0 →
      -(229084 / 100000 : ℝ) <
        Real.log |(determinantRat z N : ℝ)| / (n N : ℝ) ^ 2 -
          (1 / 2 : ℝ) * Real.log 2 := by
  let gap : ℝ := -(8609 / 4608 : ℝ) -
    ((1 / 2 : ℝ) + (505 / 4608 : ℝ)) * Real.log 2 + 229084 / 100000
  have hgap : 0 < gap := by
    dsimp [gap]
    linarith [finitePlace_constant_gt_threshold]
  filter_upwards [determinantRat_finite_place_eventually_lower z
    (show 0 < gap / 2 by positivity)] with N hN
  intro hdet
  have h := hN hdet
  dsimp [gap] at hgap h
  nlinarith

end InternalCatalan

end OAI
