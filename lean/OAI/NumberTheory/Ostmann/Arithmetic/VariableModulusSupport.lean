import OAI.NumberTheory.Ostmann.Arithmetic.CompensatedPairSupport

namespace OAI

/-! # Paired frequency bounds when each history pair has its own modulus

The common frequency modulus can depend on the two fixed histories. The
upper bound is independent of its size; it comes from the reduced moduli at
the individual nodes under the original independent unit law.
-/

namespace Ostmann
open Filter
open scoped BigOperators Classical

noncomputable def variableModulusSupportSum (S : Finset ℤ) (V n : ℕ)
    (Q : FrequencyTree (S × S) n → ℕ) [∀ t, NeZero (Q t)]
    (data : (t : FrequencyTree (S × S) n) → (ZMod (Q t))ˣ →
      List (ZMod (Q t))ˣ → Option (ArithmeticSplitData (Q t) × ArithmeticSplitData (Q t))) : ℝ :=
  ∑ t, frequencyLeafWeight (pairedFrequencyLeaf S V) n t *
    ((Fintype.card (TreeLeafTuple (ZMod (Q t))ˣ n) : ℝ)⁻¹ *
      ∑ y : TreeLeafTuple (ZMod (Q t))ˣ n, arithmeticLeafSupport n (data t) y)

theorem variableModulusSupportSum_le (S : Finset ℤ) (N V n : ℕ)
    (D : ℝ) (hD : 0 ≤ D) (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N)
    (hdiv : ∀ q : ℕ, q ≠ 0 → q ≤ N ^ 2 → (q.divisors.card : ℝ) ≤ D)
    (Q : FrequencyTree (S × S) n → ℕ) [∀ t, NeZero (Q t)]
    (data : (t : FrequencyTree (S × S) n) → (ZMod (Q t))ˣ →
      List (ZMod (Q t))ˣ → Option (ArithmeticSplitData (Q t) × ArithmeticSplitData (Q t)))
    (hmatch : ∀ t P past d e, data t P past = some (d, e) →
      d.hasFrequencies (treeNodeFrequencies S n t past.length).1 ∧
        e.hasFrequencies (treeNodeFrequencies S n t past.length).2) :
    variableModulusSupportSum S V n Q data ≤
      (8 * D ^ 4 * (1 + Real.log N) ^ 3) ^ (2 ^ n - 1) * (2 * (V : ℝ)) ^ (2 * 2 ^ n) := by
  have hlocal (t : FrequencyTree (S × S) n) :
      (Fintype.card (TreeLeafTuple (ZMod (Q t))ˣ n) : ℝ)⁻¹ *
          (∑ y : TreeLeafTuple (ZMod (Q t))ˣ n, arithmeticLeafSupport n (data t) y) ≤
        ((frequencySplitList S n t).map (pairFrequencySupportBound D)).prod := by
    have hprod : (∏ j ∈ Finset.range (2 ^ n - 1),
        pairFrequencySupportBound D (treeNodeFrequencies S n t j)) =
        ((frequencySplitList S n t).map (pairFrequencySupportBound D)).prod := by
      rw [← frequencySplitList_length S n t]
      exact prod_range_list_getD _ _ _
    unfold arithmeticLeafSupport
    apply treeLeaf_average_le (G := (ZMod (Q t))ˣ) n
      (fun P x => sequentialSupport (fun past y => arithmeticPairSplitTest (data t P past) y)
        [] (2 ^ n - 1) (treeLeafSplitEquiv n P x)) _
    intro P
    exact (arithmetic_leaf_support_fixed_frequencies (data t P) (treeNodeFrequencies S n t)
      D hD (hmatch t P) (treeNodeFrequencies_divisor_bound S N D hD hS hdiv n t) n P).trans_eq hprod
  apply le_trans _ (arithmetic_frequency_tree_sum_le S N V D hD hS
    (gcd_frequency_divisor_bound S N D hS hdiv) n)
  unfold variableModulusSupportSum
  apply Finset.sum_le_sum
  intro t _
  calc
    _ ≤ frequencyLeafWeight (pairedFrequencyLeaf S V) n t *
        ((frequencySplitList S n t).map (pairFrequencySupportBound D)).prod :=
      mul_le_mul_of_nonneg_left (hlocal t) (frequencyLeafWeight_nonneg _
        (fun _ => by unfold pairedFrequencyLeaf; split_ifs <;> norm_num) n t)
    _ = _ := by rw [frequencyTreeWeight_eq_splitList]; ring

/-- The sufficiently-large cutoff is uniform in the history-dependent
moduli, including their full denominator powers. -/
theorem variableModulusSupportSum_rate (n : ℕ) (K C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ m : ℝ in atTop, ∀ N V : ℕ, ∀ Δ : ℝ, ∀ S : Finset ℤ,
      (N : ℝ) ≤ Real.exp (C * m) →
      (V : ℝ) ≤ Real.exp (Δ + Real.sqrt m) →
      (∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N) →
      ∀ Q : FrequencyTree (S × S) n → ℕ, ∀ [_hQ : ∀ t, NeZero (Q t)],
      ∀ data : (t : FrequencyTree (S × S) n) → (ZMod (Q t))ˣ →
        List (ZMod (Q t))ˣ → Option (ArithmeticSplitData (Q t) × ArithmeticSplitData (Q t)),
      (∀ t P past d e, data t P past = some (d, e) →
        d.hasFrequencies (treeNodeFrequencies S n t past.length).1 ∧
          e.hasFrequencies (treeNodeFrequencies S n t past.length).2) →
      Real.exp (-(2 ^ n : ℕ) * Δ + K) * variableModulusSupportSum S V n Q data ≤
        Real.exp ((2 ^ n : ℕ) * Δ + ε * m) := by
  let r : ℕ := 2 ^ n
  have hr : (0 : ℝ) < r := by exact_mod_cast (Nat.two_pow_pos n)
  let δ : ℝ := ε / (2 * r)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδr : δ * r = ε / 2 := by dsimp [δ]; field_simp
  obtain ⟨M, hM⟩ := leaf_frequency_budget_sublinear r K (ε / 2) (by positivity)
  filter_upwards [frequency_budget_subexponential C δ hC hδ,
    eventually_ge_atTop M, eventually_ge_atTop (0 : ℝ)] with m hrate hm hm0
  intro N V Δ S hN hV hS Q _hQ data hmatch
  obtain ⟨D, hD, hdiv, hcost⟩ := hrate
  have hdivN (q : ℕ) (hq : q ≠ 0) (hqN : q ≤ N ^ 2) : (q.divisors.card : ℝ) ≤ D := by
    apply hdiv q hq
    calc
      (q : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hqN
      _ ≤ Real.exp (C * m) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hN 2
      _ = Real.exp (2 * C * m) := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hsum := variableModulusSupportSum_le S N V n D hD hS hdivN Q data hmatch
  have hC0 : 0 ≤ 8 * D ^ 4 * (1 + Real.log N) ^ 3 := by
    have hlog := Real.log_natCast_nonneg N
    positivity
  have hnode : (8 * D ^ 4 * (1 + Real.log N) ^ 3) ^ (r - 1) ≤
      Real.exp ((ε / 2) * m) := by
    calc
      _ ≤ Real.exp (δ * m) ^ (r - 1) := pow_le_pow_left₀ hC0 (hcost N hN) _
      _ = Real.exp ((r - 1 : ℕ) * (δ * m)) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hcount : ((r - 1 : ℕ) : ℝ) ≤ r := by exact_mod_cast Nat.sub_le r 1
        have h := mul_le_mul_of_nonneg_right hcount (mul_nonneg hδ.le hm0)
        nlinarith [hδr]
  have hleaf := hM m hm Δ V hV
  calc
    _ ≤ Real.exp (-(r : ℝ) * Δ + K) *
        ((8 * D ^ 4 * (1 + Real.log N) ^ 3) ^ (r - 1) * (2 * (V : ℝ)) ^ (2 * r)) :=
      mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le
    _ = (8 * D ^ 4 * (1 + Real.log N) ^ 3) ^ (r - 1) *
        ((2 * (V : ℝ)) ^ (2 * r) * Real.exp (-(r : ℝ) * Δ + K)) := by ring
    _ ≤ Real.exp ((ε / 2) * m) * Real.exp ((r : ℝ) * Δ + (ε / 2) * m) :=
      mul_le_mul hnode hleaf (by positivity) (Real.exp_pos _).le
    _ = Real.exp ((2 ^ n : ℕ) * Δ + ε * m) := by
      rw [← Real.exp_add]
      dsimp [r]
      congr 1
      ring

end Ostmann

end OAI
