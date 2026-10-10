import OAI.NumberTheory.TwoPoint.Bounds.FullTupleBinIdentity
import OAI.NumberTheory.TwoPoint.Walks.CanonicalPartialCentering

namespace OAI

/-! The graph bin and the analytic centering bin are the same finite sum,
with the literal real denominator and no floor-normalization error. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma prefix_scalar_real_denominator (f : ℕ → ℂ) (N : ℕ) (T : ℝ) :
    ((N : ℂ) / (T : ℂ)) * (positivePrefix f N / (N : ℂ)) =
      positivePrefix f N / (T : ℂ) := by
  by_cases hN : N = 0
  · subst N
    simp only [positivePrefix, range_zero, sum_empty, Nat.cast_zero, zero_div, mul_zero]
  · have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN
    field_simp

lemma weighted_uncut_sub_full_bin {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (R : Finset ℕ) (hR : ∀ q ∈ R, 0 < q) (L η : ℝ) (j : ℤ)
    (h l b : ℕ) [NeZero l] (hh : 0 < h) (T : ℝ) :
    ((⌊T⌋₊ : ℂ) / (T : ℂ)) *
        uncutPrimePrefix P R (numericalBinEligible L η j) h (progressionEdgeGate h l b) ⌊T⌋₊ -
      fullNumericalBin (primeTupleDivisors P) R L η j l (b : ZMod l) h T =
        tupleNonrawBin P R actualPaddingCoefficient (numericalBinEligible L η j)
          l (b : ZMod l) h T := by
  rw [uncutPrimePrefix_centered P hprime hdisjoint R hR _ h l b _ hh,
    prefix_scalar_real_denominator, fullNumericalBin_tuple P hprime hdisjoint]
  rw [positivePrefix_sum_finite, sum_div]
  simp only [positivePrefix_const_mul, tupleNonrawBin, mul_div_assoc]
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro q _
  ring

end TwoPointCorrelations

end OAI
