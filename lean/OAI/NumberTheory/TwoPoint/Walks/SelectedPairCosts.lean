import OAI.NumberTheory.TwoPoint.Walks.SelectedRawComparison

namespace OAI

/-! Passing the proved prime-cost moments to arbitrary selected pair subfamilies. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma selected_pair_mass_le (D Q : Finset ℕ) (A : Finset (ℕ × ℕ))
    (L η : ℝ) (hη : 0 < η)
    (hA : A ⊆ eligibleComplexPairs D Q (PaddingPairEligible L η)) :
    (∑ dq ∈ A, complexPairWeight dq) ≤ totalPaddingBinMass D Q L η := by
  rw [← eligibleComplexPairs_mass D Q L η hη]
  exact sum_le_sum_of_subset_of_nonneg hA (fun dq _ _ => complexPairWeight_nonneg dq)

lemma selected_pair_prime_cost_le {J : ℕ} (P : Fin J → Finset ℕ) (Q : Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (hQ : ∀ p ∈ Q, p.Prime) (hPQ : Disjoint (primeTuplePool P) Q)
    (c : ℕ → ℝ) (hc : ∀ p, 0 ≤ c p)
    (W : ℝ) (hW : 0 < W) (hmass : ∀ j, W ≤ primeHarmonicMass (P j))
    (A : Finset (ℕ × ℕ)) (hA : A ⊆ primeTupleDivisors P ×ˢ retainedPrimeDivisors Q) :
    (∑ dq ∈ A, complexPairWeight dq * ∑ p ∈ (dq.1 * dq.2).primeFactors, c p) ≤
      paddingTiltNormalizer Q * (∏ j, primeHarmonicMass (P j)) *
        ((∑ p ∈ primeTuplePool P, c p / (p : ℝ)) / W +
          ∑ p ∈ Q, (4 / ((p : ℝ) + 4)) * c p) := by
  apply le_trans _ (tuple_padding_prime_cost_bound P Q hprime hdisjoint hQ hPQ c
    (fun p _ => hc p) W hW hmass)
  have hs := sum_le_sum_of_subset_of_nonneg
    (f := fun dq : ℕ × ℕ => complexPairWeight dq *
      ∑ p ∈ (dq.1 * dq.2).primeFactors, c p) hA
    (fun dq _ _ => mul_nonneg (complexPairWeight_nonneg dq)
      (sum_nonneg (fun p _ => hc p)))
  rw [sum_product] at hs
  exact hs

lemma selected_pair_reciprocal_cost_le {J : ℕ} (P : Fin J → Finset ℕ) (Q : Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (hQ : ∀ p ∈ Q, p.Prime) (hPQ : Disjoint (primeTuplePool P) Q)
    (W : ℝ) (hW : 0 < W) (hmass : ∀ j, W ≤ primeHarmonicMass (P j))
    (A : Finset (ℕ × ℕ)) (hA : A ⊆ primeTupleDivisors P ×ˢ retainedPrimeDivisors Q) :
    (∑ dq ∈ A, complexPairWeight dq * ∑ p ∈ (dq.1 * dq.2).primeFactors, 1 / (p : ℝ)) ≤
      paddingTiltNormalizer Q * (∏ j, primeHarmonicMass (P j)) *
        ((∑ p ∈ primeTuplePool P, 1 / (p : ℝ) ^ 2) / W +
          4 * ∑ p ∈ Q, 1 / (p : ℝ) ^ 2) := by
  have hb := selected_pair_prime_cost_le P Q hprime hdisjoint hQ hPQ
    (fun p => 1 / (p : ℝ)) (fun p => by positivity) W hW hmass A hA
  have hp : (∑ p ∈ Q, (4 / ((p : ℝ) + 4)) * (1 / (p : ℝ))) ≤
      4 * ∑ p ∈ Q, 1 / (p : ℝ) ^ 2 := by
    rw [mul_sum]
    apply sum_le_sum
    intro p hmem
    have hpR : (0 : ℝ) < p := by exact_mod_cast (hQ p hmem).pos
    calc
      _ ≤ (4 / (p : ℝ)) * (1 / (p : ℝ)) :=
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_left (by norm_num) hpR (by linarith)) (by positivity)
      _ = _ := by ring
  have hv : 0 ≤ paddingTiltNormalizer Q * ∏ j, primeHarmonicMass (P j) :=
    mul_nonneg (paddingTiltNormalizer_pos Q).le
      (prod_nonneg (fun j _ => (hW.trans_le (hmass j)).le))
  have he : (∑ p ∈ primeTuplePool P, (1 / (p : ℝ)) / (p : ℝ)) =
      ∑ p ∈ primeTuplePool P, 1 / (p : ℝ) ^ 2 := by
    apply sum_congr rfl
    intro p _
    ring
  rw [he] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (add_le_add
    (le_refl ((∑ p ∈ primeTuplePool P, 1 / (p : ℝ) ^ 2) / W)) hp) hv)

end TwoPointCorrelations

end OAI
