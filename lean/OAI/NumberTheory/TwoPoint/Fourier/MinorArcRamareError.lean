import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTGeneralPrimeError

namespace OAI

/-! The combined denominator and prime-extraction error for the additive
short-window argument. Both errors are supported on prime squares. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def minorArcRamareApprox (P : Finset ℕ) (A B : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ p ∈ P, if p ∣ n then
    A p * B (n / p) / ((finitePrimeDivisorCount P (n / p) + 1 : ℕ) : ℂ) else 0

lemma minor_arc_ramare_pointwise (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (C A B : ℕ → ℂ) (hC : OneBounded C) (hA : OneBounded A) (hB : OneBounded B)
    (hproduct : ∀ p ∈ P, ∀ m, 0 < m → ¬p ∣ m → C (p * m) = A p * B m)
    {n : ℕ} (hn : 0 < n) :
    ‖(if finitePrimeDivisorCount P n = 0 then 0 else C n) -
      minorArcRamareApprox P A B n‖ ≤ 3 * mrtPrimeSquareCount P n := by
  have he : (if finitePrimeDivisorCount P n = 0 then 0 else C n) -
      minorArcRamareApprox P A B n =
      mrtRamareCorrection P C n + mrtPrimeProductError P (fun _ _ => True) C A B n := by
    have hterm (p : ℕ) :
        (if p ∣ n ∧ True then
          (C n - A p * B (n / p)) / ((finitePrimeDivisorCount P (n / p) + 1 : ℕ) : ℂ)
        else 0) =
        (if p ∣ n then C n / ((finitePrimeDivisorCount P (n / p) + 1 : ℕ) : ℂ) else 0) -
        (if p ∣ n then A p * B (n / p) /
          ((finitePrimeDivisorCount P (n / p) + 1 : ℕ) : ℂ) else 0) := by
      by_cases hp : p ∣ n <;> simp [hp, sub_div]
    have hsum : mrtPrimeProductError P (fun _ _ => True) C A B n =
        ∑ p ∈ P,
          ((if p ∣ n then C n / ((finitePrimeDivisorCount P (n / p) + 1 : ℕ) : ℂ) else 0) -
          (if p ∣ n then A p * B (n / p) /
            ((finitePrimeDivisorCount P (n / p) + 1 : ℕ) : ℂ) else 0)) := by
      unfold mrtPrimeProductError
      apply sum_congr rfl
      intro p _
      simpa only [and_true] using hterm p
    rw [hsum, sum_sub_distrib]
    unfold minorArcRamareApprox mrtRamareCorrection
    ring
  rw [he]
  have hden := mrt_ramare_correction_oneBounded P hP C hC hn
  have hprod := mrt_prime_product_error_bound P hP (fun _ _ => True) C A B hC hA hB hproduct hn
  exact (norm_add_le _ _).trans (by linarith)

lemma minor_arc_typical_ramare_pointwise {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (hdis : Set.PairwiseDisjoint (J : Set ι) P) {j : ι} (hj : j ∈ J)
    (F : ℕ → ℂ) (hF : Multiplicative F) (hFb : OneBounded F)
    {n : ℕ} (hn : 0 < n) :
    ‖mrtTypicalCoefficient J P F n -
      minorArcRamareApprox (P j) F (mrtTypicalCoefficient (J.erase j) P F) n‖ ≤
      3 * mrtPrimeSquareCount (P j) n := by
  have hh := minor_arc_ramare_pointwise (P j) (hP j hj)
    (mrtTypicalCoefficient J P F) F (mrtTypicalCoefficient (J.erase j) P F)
    (mrtTypicalCoefficient_oneBounded J P F hFb) hFb
    (mrtTypicalCoefficient_oneBounded (J.erase j) P F hFb)
    (fun p hp m hm hpm => mrtTypicalCoefficient_prime_mul_coprime J P hP hdis hj F hF hp hm hpm)
    hn
  simpa only [mrtTypicalCoefficient, mrtTypical_ramare_supported J P hj F] using hh

end TwoPointCorrelations

end OAI
