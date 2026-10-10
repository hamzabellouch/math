import OAI.NumberTheory.TwoPoint.Bounds.PrimeDegreeTail
import OAI.NumberTheory.TwoPoint.Walks.TuplePrimeArithmetic

namespace OAI

/-! Specialize the arithmetic-geometric mean bound to the literal tuple
centers and the degree projection of the integer graph. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma actualPaddingDegree_biUnion {J : ℕ} (P : Fin J → Finset ℕ)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) (n : ℤ) :
    actualPaddingDegree (univ.biUnion P) n = ∑ j, actualPaddingDegree (P j) n := by
  have he : (univ.biUnion P).filter (fun p : ℕ => (p : ℤ) ∣ n) =
      univ.biUnion (fun j => (P j).filter (fun p : ℕ => (p : ℤ) ∣ n)) := by
    ext p
    simp only [mem_filter, mem_biUnion, mem_univ, true_and]
    aesop
  unfold actualPaddingDegree
  rw [he, card_biUnion]
  intro j _ l _ hjl
  exact (hdisjoint j l (Ne.symm hjl)).mono (filter_subset _ _) (filter_subset _ _)

lemma prime_band_indicator_sum {J : ℕ} (P : Fin J → Finset ℕ)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) (n : ℤ) :
    (∑ j : Fin J, ∑ p : P j, if (p.val : ℤ) ∣ n then (1 : ℝ) else 0) =
      (actualPaddingDegree (univ.biUnion P) n : ℝ) := by
  rw [actualPaddingDegree_biUnion P hdisjoint, Nat.cast_sum]
  simp [actualPrimeDegree_eq_count, booleanCount]

theorem actual_centeredTuple_square_sum_le {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) (n : ℤ) (W : ℝ)
    (hV : ∀ j, primeHarmonicMass (P j) ≤ 2 * W)
    (hdegree : (actualPaddingDegree (univ.biUnion P) n : ℝ) ≤ 6 * W * J) :
    (∑ d : (j : Fin J) → P j,
      |centeredTuple (∏ j, (d j).val).primeFactors n| ^ 2) ≤ (8 * W) ^ J := by
  have hd : (∑ j : Fin J, ∑ p : P j,
      if (p.val : ℤ) ∣ n then (1 : ℝ) else 0) ≤ 6 * W * J := by
    rw [actualPaddingDegree_biUnion P hdisjoint, Nat.cast_sum] at hdegree
    simpa [actualPrimeDegree_eq_count, booleanCount] using hdegree
  have hb := familyCenter_square_sum_le (fun j (p : P j) => p.val)
    (fun j p => hprime j _ p.property) (fun _ _ => 0) n W
    (fun j => hV j) (by simpa only [zero_add, Fintype.card_fin] using hd)
  simpa only [familyCenter_zero_eq_centeredTuple _ (fun j p => hprime j _ p.property)
    _ (selectedPrimeValues_injective _ hdisjoint), familyTuple, Fintype.card_fin] using hb

end TwoPointCorrelations

end OAI
