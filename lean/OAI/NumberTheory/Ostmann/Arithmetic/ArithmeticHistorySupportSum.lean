import OAI.NumberTheory.Ostmann.Arithmetic.FrequencyTreeNodes

namespace OAI

/-! # Summing the original two-history congruence support over frequencies -/

namespace Ostmann

open scoped BigOperators Classical

theorem gcd_frequency_divisor_bound (S : Finset ℤ) (N : ℕ) (D : ℝ)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N)
    (hdiv : ∀ q : ℕ, q ≠ 0 → q ≤ N ^ 2 → (q.divisors.card : ℝ) ≤ D)
    (v : ℤ) (hv : v ∈ S) (w : ℤ) (_hw : w ∈ S) :
    ((v.natAbs.gcd w.natAbs).divisors.card : ℝ) ≤ D := by
  have hv0 : 0 < v.natAbs := Int.natAbs_pos.mpr (hS v hv).1
  have hN : 0 < N := hv0.trans_le (hS v hv).2
  apply hdiv
  · exact Nat.ne_of_gt (Nat.gcd_pos_of_pos_left _ hv0)
  · calc
      _ ≤ v.natAbs := Nat.gcd_le_left _ hv0
      _ ≤ N := (hS v hv).2
      _ ≤ N ^ 2 := by simpa only [pow_two] using Nat.le_mul_of_pos_right N hN

/-- The bulk residue variables are still sampled from the original Haar
law. Data at each node depend only on earlier split products; the only
extra weights are the restrictions on the leaf frequencies. -/
theorem arithmetic_history_support_sum_le {Q : ℕ} [NeZero Q]
    (S : Finset ℤ) (N V n : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N)
    (hdiv : ∀ q : ℕ, q ≠ 0 → q ≤ N ^ 2 → (q.divisors.card : ℝ) ≤ D)
    (P : FrequencyTree (S × S) n → (ZMod Q)ˣ)
    (data : FrequencyTree (S × S) n → List (ZMod Q)ˣ →
      Option (ArithmeticSplitData Q × ArithmeticSplitData Q))
    (hmatch : ∀ t past d e, data t past = some (d, e) →
      d.hasFrequencies (treeNodeFrequencies S n t past.length).1 ∧
        e.hasFrequencies (treeNodeFrequencies S n t past.length).2) :
    (∑ t : FrequencyTree (S × S) n,
      frequencyLeafWeight (pairedFrequencyLeaf S V) n t *
        ((Fintype.card (TreeLeafFiber (ZMod Q)ˣ n (P t)) : ℝ)⁻¹ *
          ∑ x : TreeLeafFiber (ZMod Q)ˣ n (P t),
            sequentialSupport (fun past y => arithmeticPairSplitTest (data t past) y) []
              (2 ^ n - 1) (treeLeafSplitEquiv n (P t) x))) ≤
      (8 * D ^ 4 * (1 + Real.log N) ^ 3) ^ (2 ^ n - 1) * (2 * (V : ℝ)) ^ (2 * 2 ^ n) := by
  apply le_trans _ (arithmetic_frequency_tree_sum_le S N V D hD hS
    (gcd_frequency_divisor_bound S N D hS hdiv) n)
  apply Finset.sum_le_sum
  intro t _
  have hlocal := arithmetic_leaf_support_fixed_frequencies (data t) (treeNodeFrequencies S n t)
    D hD (hmatch t) (treeNodeFrequencies_divisor_bound S N D hD hS hdiv n t) n (P t)
  have hprod : (∏ j ∈ Finset.range (2 ^ n - 1),
      pairFrequencySupportBound D (treeNodeFrequencies S n t j)) =
      ((frequencySplitList S n t).map (pairFrequencySupportBound D)).prod := by
    rw [← frequencySplitList_length S n t]
    exact prod_range_list_getD _ _ _
  rw [hprod] at hlocal
  calc
    _ ≤ frequencyLeafWeight (pairedFrequencyLeaf S V) n t *
        ((frequencySplitList S n t).map (pairFrequencySupportBound D)).prod :=
      mul_le_mul_of_nonneg_left hlocal (frequencyLeafWeight_nonneg _
        (fun _ => by unfold pairedFrequencyLeaf; split_ifs <;> norm_num) n t)
    _ = _ := by rw [frequencyTreeWeight_eq_splitList]; ring

end Ostmann

end OAI
