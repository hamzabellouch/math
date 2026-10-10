import OAI.NumberTheory.TwoPoint.Bounds.FullNumericalBins
import OAI.NumberTheory.TwoPoint.Bounds.UncutCenteredProfile
import OAI.NumberTheory.TwoPoint.Bounds.PartialCenteringSum

namespace OAI

/-! The empty supply subset is exactly the full numerical divisor sum. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma positivePrefix_ite_const (p : Prop) (f : ℕ → ℂ) (N : ℕ) :
    positivePrefix (fun n => if p then f n else 0) N =
      if p then positivePrefix f N else 0 := by
  by_cases hp : p <;> simp only [hp, ite_true, ite_false, positivePrefix, sum_const_zero]

lemma fullNumericalBin_tuple {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (R : Finset ℕ) (L η : ℝ) (j : ℤ)
    (l : ℕ) [NeZero l] (b : ZMod l) (h : ℕ) (T : ℝ) :
    fullNumericalBin (primeTupleDivisors P) R L η j l b h T =
      ∑ q ∈ R, (actualPaddingCoefficient q : ℂ) *
        (positivePrefix (tuplePartialProfile P ∅ q (numericalBinEligible L η j) l b h) ⌊T⌋₊ /
          (T : ℂ)) := by
  simp only [fullNumericalBin, numericalBinPairs, sum_filter, sum_product]
  rw [sum_comm]
  apply sum_congr rfl
  intro q _
  rw [primeTupleDivisors, sum_image]
  · have hf : tuplePartialProfile P ∅ q (numericalBinEligible L η j) l b h =
        fun n => ∑ x : (i : Fin J) → P i,
          if numericalBinEligible L η j (∏ i, (x i).val) q then
            fullLiouvilleProfile l b (q * ∏ i, (x i).val) h n else 0 := by
      funext n
      exact tuplePartialProfile_empty P q (numericalBinEligible L η j) l b h n
    rw [hf, positivePrefix_sum_finite, sum_div, mul_sum]
    simp_rw [positivePrefix_ite_const]
    apply sum_congr rfl
    intro x _
    split_ifs <;> simp_all only [zero_div, mul_zero]
  · intro x _ y _ hxy
    exact primeTuple_injective hprime hdisjoint hxy

end TwoPointCorrelations

end OAI
