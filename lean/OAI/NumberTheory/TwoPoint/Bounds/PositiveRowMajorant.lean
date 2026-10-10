import OAI.NumberTheory.TwoPoint.Bounds.PrimeRowMoments
import OAI.NumberTheory.TwoPoint.Bounds.PrimeTupleMass
import OAI.NumberTheory.TwoPoint.Bounds.ActualCenterDegree

namespace OAI

/-! The literal sum of positive tuple weights is the row majorant
whose second moment was estimated under the product law. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma positivePrimeWeight_tuple {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (d : (j : Fin J) → P j) (n : ℤ) :
    positivePrimeWeight (∏ j, (d j).val).primeFactors n =
      ∏ j, ((if ((d j).val : ℤ) ∣ n then 1 else 0) + 1 / ((d j).val : ℝ)) := by
  have hinj := selectedPrimeValues_injective d hdisjoint
  have hf : (∏ j, (d j).val).primeFactors = univ.image (fun j => (d j).val) :=
    familyTuple_primeFactors (fun j (p : P j) => p.val)
      (fun j p => hprime j _ p.property) d hinj
  rw [positivePrimeWeight, hf]
  rw [prod_image]
  intro i _ j _ hij
  exact hinj hij

lemma positivePrimeWeight_tuple_sum {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) (n : ℤ) :
    (∑ d ∈ primeTupleDivisors P, positivePrimeWeight d.primeFactors n) =
      ∏ j, ((actualPaddingDegree (P j) n : ℝ) + primeHarmonicMass (P j)) := by
  rw [primeTupleDivisors, sum_image]
  · simp_rw [positivePrimeWeight_tuple P hprime hdisjoint]
    have he := (Fintype.prod_sum (fun j (p : P j) =>
      (if (p.val : ℤ) ∣ n then (1 : ℝ) else 0) + 1 / (p.val : ℝ))).symm
    apply he.trans
    apply prod_congr rfl
    intro j _
    rw [sum_add_distrib, actualPrimeDegree_eq_count]
    simp only [booleanCount, primeHarmonicMass, decide_eq_true_eq, one_div]
  · intro x _ y _ hxy
    exact primeTuple_injective hprime hdisjoint hxy

lemma positivePrimeWeight_tuple_sum_le {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) (n : ℤ) (W : ℝ)
    (hV : ∀ j, primeHarmonicMass (P j) ≤ 2 * W)
    (hdegree : (actualPaddingDegree (univ.biUnion P) n : ℝ) ≤ 6 * W * J) :
    (∑ d ∈ primeTupleDivisors P, positivePrimeWeight d.primeFactors n) ≤ (8 * W) ^ J := by
  rw [positivePrimeWeight_tuple_sum P hprime hdisjoint]
  have hd : (∑ j, (actualPaddingDegree (P j) n : ℝ)) ≤ 6 * W * J := by
    rw [← Nat.cast_sum, ← actualPaddingDegree_biUnion P hdisjoint]
    exact hdegree
  have hb := nonneg_product_le_power_card
    (fun j => (actualPaddingDegree (P j) n : ℝ) + primeHarmonicMass (P j)) (8 * W)
    (fun j => add_nonneg (Nat.cast_nonneg _) (by unfold primeHarmonicMass; positivity))
    (sum_degree_budget (fun j => (actualPaddingDegree (P j) n : ℝ))
      (fun j => primeHarmonicMass (P j)) W hV (by simpa only [Fintype.card_fin] using hd))
  simpa only [Fintype.card_fin] using hb

/-- The deterministic first-power bound needed when testing the graph
against bounded vectors. The degree projection is the only site restriction. -/
lemma abs_centeredTuple_sum_le {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) (n : ℤ) (W : ℝ)
    (hV : ∀ j, primeHarmonicMass (P j) ≤ 2 * W)
    (hdegree : (actualPaddingDegree (univ.biUnion P) n : ℝ) ≤ 6 * W * J) :
    (∑ d ∈ primeTupleDivisors P, |centeredTuple d.primeFactors n|) ≤ (8 * W) ^ J := by
  exact (sum_le_sum (fun d _ => abs_centeredTuple_le_positivePrimeWeight d.primeFactors n)).trans
    (positivePrimeWeight_tuple_sum_le P hprime hdisjoint n W hV hdegree)

lemma positive_tuple_padding_row_bound {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (Q D : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (hD : D ⊆ primeTupleDivisors P)
    (padding : ℕ → Finset ℕ) (hpadding : ∀ d ∈ D, padding d ⊆ retainedPrimeDivisors Q)
    (n : ℤ) :
    (∑ d ∈ D, ∑ q ∈ padding d,
      actualPaddingCoefficient q * positivePrimeWeight d.primeFactors n *
        if (q : ℤ) ∣ n then 1 else 0) ≤ primeRowMajorant P Q n := by
  calc
    _ ≤ ∑ d ∈ D, positivePrimeWeight d.primeFactors n * actualPaddingWeight Q n := by
      apply sum_le_sum
      intro d hd
      calc
        _ = positivePrimeWeight d.primeFactors n *
            (∑ q ∈ padding d, if (q : ℤ) ∣ n then actualPaddingCoefficient q else 0) := by
          rw [mul_sum]
          apply sum_congr rfl
          intro q _
          split_ifs <;> ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (by
          rw [actualPaddingWeight_eq_divisor_sum Q hQ n]
          exact sum_le_sum_of_subset_of_nonneg (hpadding d hd) (by
            intro q _ _
            split_ifs
            · exact actualPaddingCoefficient_nonneg q
            · exact le_rfl)) (positivePrimeWeight_nonneg _ _)
    _ ≤ ∑ d ∈ primeTupleDivisors P,
        positivePrimeWeight d.primeFactors n * actualPaddingWeight Q n :=
      sum_le_sum_of_subset_of_nonneg hD (by
        intro d _ _
        exact mul_nonneg (positivePrimeWeight_nonneg _ _) (by
          exact zero_le_one.trans (actualPaddingWeight_one_le Q n)))
    _ = _ := by
      rw [← sum_mul, positivePrimeWeight_tuple_sum P hprime hdisjoint]
      exact mul_comm _ _

end TwoPointCorrelations

end OAI
