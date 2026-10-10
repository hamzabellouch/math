import Mathlib.Tactic.Ring
import OAI.NumberTheory.Catalan.Determinants.PalindromicRowFrobenius
import OAI.NumberTheory.Catalan.Estimates.PalindromicBlockInverse

namespace OAI


noncomputable section

namespace InternalCatalan

open Polynomial

theorem palindromicZModIntCast_apply (p : ℕ) (z : ℤ) :
    (Int.castRingHom (ZMod p)) z = (z : ZMod p) := rfl

theorem palindromic_actual_P_extraction {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {r0 : ℕ} (hr : r0 < 48) (i ell : Fin p) (u : ℕ) :
    (X * (rowP p (p * r0 + i.val)).map (Int.castRingHom (ZMod p)) *
        (1 - X ^ 2) ^ ((p - 1) / 2)).coeff ((u + 1) * p + ell.val) =
      palindromicTransitionMatrix p ell i * ((rowP 1 r0).coeff u : ZMod p) +
        palindromicReversedTransitionMatrix p ell i *
          ((rowP 1 (r0 + 1)).coeff u : ZMod p) := by
  have h := palindromicPResidueSum_coeff p r0 u i ell
  rw [← palindromic_rowP_frobenius hp2 hr i] at h
  simpa only [palindromicPBase, coeff_map, palindromicZModIntCast_apply] using h

theorem palindromic_actual_D_extraction {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {r0 : ℕ} (hr : r0 < 48) (i ell : Fin p) (u : ℕ) :
    ((rowD p (p * r0 + i.val)).coeff (u * p + ell.val) : ZMod p) =
      palindromicTransitionMatrix p ell i * ((rowD 1 r0).coeff u : ZMod p) +
        palindromicReversedTransitionMatrix p ell i *
          ((rowD 1 (r0 + 1)).coeff u : ZMod p) := by
  have h := palindromicDResidueSum_coeff p r0 u i ell
  rw [← palindromic_rowD_frobenius hp2 hr i] at h
  simpa only [palindromicDBase, coeff_map, palindromicZModIntCast_apply] using h

theorem palindromic_actual_P_extraction_below {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {r0 : ℕ} (hr : r0 < 48) (i ell : Fin p) :
    (X * (rowP p (p * r0 + i.val)).map (Int.castRingHom (ZMod p)) *
        (1 - X ^ 2) ^ ((p - 1) / 2)).coeff ell.val = 0 := by
  rw [palindromic_rowP_frobenius hp2 hr i]
  exact palindromicPResidueSum_coeff_below p r0 i ell

theorem palindromic_actual_extracted_rows {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {r0 : ℕ} (hr : r0 < 48) (i ell : Fin p) (u : ℕ) :
    ((X * (rowP p (p * r0 + i.val)).map (Int.castRingHom (ZMod p)) *
          (1 - X ^ 2) ^ ((p - 1) / 2)).coeff ((u + 1) * p + ell.val),
      ((rowD p (p * r0 + i.val)).coeff (u * p + ell.val) : ZMod p)) =
      (palindromicTransitionMatrix p ell i * ((rowP 1 r0).coeff u : ZMod p) +
        palindromicReversedTransitionMatrix p ell i *
          ((rowP 1 (r0 + 1)).coeff u : ZMod p),
       palindromicTransitionMatrix p ell i * ((rowD 1 r0).coeff u : ZMod p) +
        palindromicReversedTransitionMatrix p ell i *
          ((rowD 1 (r0 + 1)).coeff u : ZMod p)) := by
  exact Prod.ext (palindromic_actual_P_extraction hp2 hr i ell u)
    (palindromic_actual_D_extraction hp2 hr i ell u)

end InternalCatalan





namespace InternalCatalan

open Polynomial
open scoped BigOperators

def palindromicBaseRawContraction (p : ℕ) [Fact p.Prime] (r k : ℕ) : ZMod p :=
  (∑ u ∈ Finset.range 65, ((rowP 1 r).coeff u : ZMod p) *
    palindromicRatResidue p (momentRat u k)) -
  (3 / 2 : ZMod p) *
    ∑ u ∈ Finset.range 65, ((rowD 1 r).coeff u : ZMod p) *
      palindromicRatResidue p (zetaRat u k)

def palindromicExtractedRawContraction (p : ℕ) [Fact p.Prime] (r0 : ℕ)
    (i ell : Fin p) (k : ℕ) :
    ZMod p :=
  (∑ u ∈ Finset.range 65,
    (X * (rowP p (p * r0 + i.val)).map (Int.castRingHom (ZMod p)) *
        (1 - X ^ 2) ^ ((p - 1) / 2)).coeff ((u + 1) * p + ell.val) *
      palindromicRatResidue p (momentRat u k)) -
  (3 / 2 : ZMod p) *
    ∑ u ∈ Finset.range 65,
      ((rowD p (p * r0 + i.val)).coeff (u * p + ell.val) : ZMod p) *
        palindromicRatResidue p (zetaRat u k)

theorem palindromicExtractedRawContraction_factor {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {r0 : ℕ} (hr : r0 < 48) (i ell : Fin p) (k : ℕ) :
    palindromicExtractedRawContraction p r0 i ell k =
      palindromicTransitionMatrix p ell i * palindromicBaseRawContraction p r0 k +
        palindromicReversedTransitionMatrix p ell i *
          palindromicBaseRawContraction p (r0 + 1) k := by
  simp only [palindromicExtractedRawContraction, palindromicBaseRawContraction]
  simp_rw [palindromic_actual_P_extraction hp2 hr i ell,
    palindromic_actual_D_extraction hp2 hr i ell,
    add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

def palindromicBaseFilterWeight (p v : ℕ) : ZMod p :=
  (-1 : ZMod p) ^ v * (Nat.choose 4 v : ZMod p)

def palindromicBaseFilteredContraction (p : ℕ) [Fact p.Prime] (r : ℕ)
    (k0 : Fin 48) : ZMod p :=
  ∑ v ∈ Finset.range 5, palindromicBaseFilterWeight p v *
    palindromicBaseRawContraction p r (7 + k0.val + v)

def palindromicExtractedFilteredEntry (p : ℕ) [Fact p.Prime] (r0 : Fin 48)
    (i ell : Fin p) (k0 : Fin 48) : ZMod p :=
  ∑ v ∈ Finset.range 5, palindromicBaseFilterWeight p v *
    palindromicExtractedRawContraction p r0.val i ell (7 + k0.val + v)

theorem palindromicExtractedFilteredEntry_factor {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (r0 : Fin 48) (i ell : Fin p) (k0 : Fin 48) :
    palindromicExtractedFilteredEntry p r0 i ell k0 =
      palindromicTransitionMatrix p ell i *
          palindromicBaseFilteredContraction p r0.val k0 +
        palindromicReversedTransitionMatrix p ell i *
          palindromicBaseFilteredContraction p (r0.val + 1) k0 := by
  unfold palindromicExtractedFilteredEntry palindromicBaseFilteredContraction
  simp_rw [palindromicExtractedRawContraction_factor hp2 r0.isLt i ell,
    mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro v hv
    ring
  · apply Finset.sum_congr rfl
    intro v hv
    ring

theorem palindromicBaseRawContraction_eq_residue {p : ℕ} [Fact p.Prime]
    (hp : 260 < p) (r k : ℕ) (hk : k < p) :
    palindromicBaseRawContraction p r k =
      palindromicRatResidue p (rawEntryRat 0 1 r k) := by
  simpa only [palindromicBaseRawContraction, H, mul_one] using
    (fixed_rawEntryRat_residue hp r k hk).symm

theorem palindromicBaseFilteredContraction_eq_fixedBase {p : ℕ} [Fact p.Prime]
    (hp : 260 < p) (r : Fin 49) (k0 : Fin 48) :
    palindromicBaseFilteredContraction p r.val k0 =
      palindromicRatResidue p (fixedBaseEntryRat r k0) := by
  rw [fixedBaseEntryRat_residue hp r k0]
  simp only [palindromicBaseFilteredContraction, palindromicBaseFilterWeight,
    q, b, mul_one]
  apply Finset.sum_congr rfl
  intro v hv
  have hv' : v < 5 := Finset.mem_range.mp hv
  have hk := k0.isLt
  rw [palindromicBaseRawContraction_eq_residue hp r.val (7 + k0.val + v) (by omega)]

theorem palindromicBaseFilteredContraction_eq_fixedB0 {p : ℕ} [Fact p.Prime]
    (hp : 260 < p) (r0 k0 : Fin 48) :
    palindromicBaseFilteredContraction p r0.val k0 = fixedB0Residue p r0 k0 := by
  rw [fixedB0Residue_apply]
  exact palindromicBaseFilteredContraction_eq_fixedBase hp r0.castSucc k0

theorem palindromicBaseFilteredContraction_eq_fixedB1 {p : ℕ} [Fact p.Prime]
    (hp : 260 < p) (r0 k0 : Fin 48) :
    palindromicBaseFilteredContraction p (r0.val + 1) k0 = fixedB1Residue p r0 k0 := by
  rw [fixedB1Residue_apply]
  exact palindromicBaseFilteredContraction_eq_fixedBase hp r0.succ k0

theorem palindromicExtractedFilteredEntry_eq_fixedB {p : ℕ} [Fact p.Prime]
    (hp : 260 < p) (r0 : Fin 48) (i ell : Fin p) (k0 : Fin 48) :
    palindromicExtractedFilteredEntry p r0 i ell k0 =
      palindromicTransitionMatrix p ell i * fixedB0Residue p r0 k0 +
        palindromicReversedTransitionMatrix p ell i * fixedB1Residue p r0 k0 := by
  have hp2 : p ≠ 2 := by omega
  rw [palindromicExtractedFilteredEntry_factor hp2,
    palindromicBaseFilteredContraction_eq_fixedB0 hp,
    palindromicBaseFilteredContraction_eq_fixedB1 hp]

end InternalCatalan

end

end OAI
