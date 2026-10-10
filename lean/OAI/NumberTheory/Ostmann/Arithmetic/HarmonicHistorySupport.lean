import OAI.NumberTheory.Ostmann.Construction.HarmonicProductDomination
import OAI.NumberTheory.Ostmann.Arithmetic.SingleHistorySupport

namespace OAI

/-! # The arithmetic support bound under the original prime priors

The residue modulus is allowed to depend on the entire fixed frequency
history. Only the prime samples are averaged, with their original priors.
-/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def harmonicHistorySupportSum (P : Finset ℕ) (S : Finset ℤ) (V n : ℕ)
    (Q : FrequencyTree S n → ℕ) [∀ t, NeZero (Q t)]
    (T : TreeLeafIndex n → Finset ℕ)
    (hunit : ∀ t, ∀ p : P, (p : ℕ).Coprime (Q t))
    (data : (t : FrequencyTree S n) → (ZMod (Q t))ˣ →
      List (ZMod (Q t))ˣ → Option (ArithmeticSplitData (Q t))) : ℝ :=
  ∑ t : FrequencyTree S n, frequencyLeafWeight (singleFrequencyLeaf S V) n t *
    (∑ x : TreeLeafIndex n → P, (∏ i, primeSubsetPrior P (T i) (x i)) *
      singleArithmeticLeafSupport n (data t)
        ((treeLeafTupleEquiv (ZMod (Q t))ˣ n).symm
          (fun i => ZMod.unitOfCoprime (x i : ℕ) (hunit t (x i)))))

theorem harmonic_history_support_le (P : Finset ℕ) (S : Finset ℤ) (N V n : ℕ)
    (D : ℝ) (hD : 0 ≤ D) (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N)
    (hdiv : ∀ q : ℕ, q ≠ 0 → q ≤ N ^ 2 → (q.divisors.card : ℝ) ≤ D)
    (Q : FrequencyTree S n → ℕ) [∀ t, NeZero (Q t)]
    (T : TreeLeafIndex n → Finset ℕ) (h J : TreeLeafIndex n → ℕ)
    (hunit : ∀ t, ∀ p : P, (p : ℕ).Coprime (Q t))
    (hsmall : ∀ t i, Q t ≤ 2 ^ h i)
    (hrange : ∀ i p, p ∈ T i → 2 ^ h i ≤ p ∧ p < 2 ^ (h i + J i))
    (data : (t : FrequencyTree S n) → (ZMod (Q t))ˣ →
      List (ZMod (Q t))ˣ → Option (ArithmeticSplitData (Q t)))
    (hmatch : ∀ t R past d, data t R past = some d →
      d.hasFrequencies (singleTreeNodeFrequencies S n t past.length)) :
    (∑ t : FrequencyTree S n, frequencyLeafWeight (singleFrequencyLeaf S V) n t *
      (∑ x : TreeLeafIndex n → P, (∏ i, primeSubsetPrior P (T i) (x i)) *
        singleArithmeticLeafSupport n (data t)
          ((treeLeafTupleEquiv (ZMod (Q t))ˣ n).symm
            (fun i => ZMod.unitOfCoprime (x i : ℕ) (hunit t (x i)))))) ≤
      (∏ i, (∑ p ∈ T i, (p : ℝ)⁻¹)⁻¹ * (3 * J i)) *
        ((4 * D ^ 3 * (1 + Real.log N)) ^ (2 ^ n - 1) *
          (2 * (V : ℝ)) ^ (2 ^ n)) := by
  let C := ∏ i, (∑ p ∈ T i, (p : ℝ)⁻¹)⁻¹ * (3 * J i)
  have hC : 0 ≤ C := Finset.prod_nonneg fun i _ => by positivity
  have hlocal (t : FrequencyTree S n) := harmonic_leaf_residue_domination P (Q t) n T h J
    (hunit t) (hsmall t) hrange (singleArithmeticLeafSupport n (data t))
    (singleArithmeticLeafSupport_nonneg n (data t))
  calc
    _ ≤ ∑ t : FrequencyTree S n, frequencyLeafWeight (singleFrequencyLeaf S V) n t *
        (C * ((singleFrequencySplitList S n t).map (singleFrequencySupportBound D)).prod) := by
      apply Finset.sum_le_sum
      intro t _
      apply mul_le_mul_of_nonneg_left _ (frequencyLeafWeight_nonneg _
        (fun _ => by unfold singleFrequencyLeaf; split_ifs <;> norm_num) n t)
      exact (hlocal t).trans (mul_le_mul_of_nonneg_left
        (single_arithmetic_leaf_average_le S N n D hD hS hdiv t (data t) (hmatch t)) hC)
    _ = C * ∑ t : FrequencyTree S n,
        frequencyTreeWeight (singleFrequencyKernel S D) (singleFrequencyLeaf S V) n t := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      rw [singleFrequencyTreeWeight_eq]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (single_frequency_tree_sum_le S N V n D hD hS
      (gcd_frequency_divisor_bound S N D hS hdiv)) hC

end Ostmann

end OAI
