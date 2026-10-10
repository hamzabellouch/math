import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticHistorySupportSum
import OAI.NumberTheory.Ostmann.Arithmetic.FrequencyBudgetRates
import OAI.NumberTheory.Ostmann.Arithmetic.LeafFrequencyBudget

namespace OAI

/-! # The asymptotic frequency-support cost under the original Haar law -/

namespace Ostmann

open scoped BigOperators Classical
open Filter

noncomputable def arithmeticHistorySupportSum {Q : ℕ} [NeZero Q]
    (S : Finset ℤ) (V n : ℕ) (P : FrequencyTree (S × S) n → (ZMod Q)ˣ)
    (data : FrequencyTree (S × S) n → List (ZMod Q)ˣ →
      Option (ArithmeticSplitData Q × ArithmeticSplitData Q)) : ℝ :=
  ∑ t : FrequencyTree (S × S) n,
    frequencyLeafWeight (pairedFrequencyLeaf S V) n t *
      ((Fintype.card (TreeLeafFiber (ZMod Q)ˣ n (P t)) : ℝ)⁻¹ *
        ∑ x : TreeLeafFiber (ZMod Q)ˣ n (P t),
          sequentialSupport (fun past y => arithmeticPairSplitTest (data t past) y) []
            (2 ^ n - 1) (treeLeafSplitEquiv n (P t) x))

theorem arithmetic_history_support_rate {Q : ℕ} [NeZero Q]
    (n : ℕ) (K C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ m : ℝ in atTop, ∀ N V : ℕ, ∀ Δ : ℝ, ∀ S : Finset ℤ,
      (N : ℝ) ≤ Real.exp (C * m) →
      (V : ℝ) ≤ Real.exp (Δ + Real.sqrt m) →
      (∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N) →
      ∀ P : FrequencyTree (S × S) n → (ZMod Q)ˣ,
      ∀ data : FrequencyTree (S × S) n → List (ZMod Q)ˣ →
        Option (ArithmeticSplitData Q × ArithmeticSplitData Q),
      (∀ t past d e, data t past = some (d, e) →
        d.hasFrequencies (treeNodeFrequencies S n t past.length).1 ∧
          e.hasFrequencies (treeNodeFrequencies S n t past.length).2) →
      Real.exp (-(2 ^ n : ℕ) * Δ + K) * arithmeticHistorySupportSum S V n P data ≤
        Real.exp ((2 ^ n : ℕ) * Δ + ε * m) := by
  let r : ℕ := 2 ^ n
  have hr : (0 : ℝ) < r := by exact_mod_cast (Nat.two_pow_pos n)
  let δ : ℝ := ε / (2 * r)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδr : δ * r = ε / 2 := by dsimp [δ]; field_simp
  obtain ⟨M, hM⟩ := leaf_frequency_budget_sublinear r K (ε / 2) (by positivity)
  filter_upwards [frequency_budget_subexponential C δ hC hδ,
    eventually_ge_atTop M, eventually_ge_atTop (0 : ℝ)] with m hrate hm hm0
  intro N V Δ S hN hV hS P data hmatch
  obtain ⟨D, hD, hdiv, hcost⟩ := hrate
  have hdivN (q : ℕ) (hq : q ≠ 0) (hqN : q ≤ N ^ 2) : (q.divisors.card : ℝ) ≤ D := by
    apply hdiv q hq
    calc
      (q : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hqN
      _ ≤ Real.exp (C * m) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hN 2
      _ = Real.exp (2 * C * m) := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hsum := arithmetic_history_support_sum_le S N V n D hD hS hdivN P data hmatch
  change arithmeticHistorySupportSum S V n P data ≤
    (8 * D ^ 4 * (1 + Real.log N) ^ 3) ^ (r - 1) * (2 * (V : ℝ)) ^ (2 * r) at hsum
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
  change Real.exp (-(r : ℝ) * Δ + K) * arithmeticHistorySupportSum S V n P data ≤ _
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
