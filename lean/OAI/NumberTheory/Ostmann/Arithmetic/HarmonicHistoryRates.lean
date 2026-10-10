import OAI.NumberTheory.Ostmann.Arithmetic.SingleHistoryRates
import OAI.NumberTheory.Ostmann.Construction.HarmonicPriorCost

namespace OAI

/-! # The single-history arithmetic rate under the actual prime priors -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

/-- All growth and normalization hypotheses refer to the original prime
sets. The only arithmetic input is the proved bound for divisors. -/
theorem harmonic_history_support_rate (n : ℕ) (K C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ m : ℝ in atTop, ∀ N V : ℕ, ∀ Δ : ℝ, ∀ P : Finset ℕ, ∀ S : Finset ℤ,
      (N : ℝ) ≤ Real.exp (C * m) →
      (V : ℝ) ≤ Real.exp (Δ + Real.sqrt m) →
      (∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N) →
      ∀ Q : FrequencyTree S n → ℕ, ∀ [_hQ : ∀ t, NeZero (Q t)],
      ∀ T : TreeLeafIndex n → Finset ℕ, ∀ h J : TreeLeafIndex n → ℕ,
      ∀ hunit : ∀ t, ∀ p : P, (p : ℕ).Coprime (Q t),
      (∀ t i, Q t ≤ 2 ^ h i) →
      (∀ i p, p ∈ T i → 2 ^ h i ≤ p ∧ p < 2 ^ (h i + J i)) →
      ∀ a C₁ L : ℝ, 0 < a → 1 ≤ L →
      (∀ i, a ≤ ∑ p ∈ T i, (p : ℝ)⁻¹) →
      (∀ i, (J i : ℝ) ≤ Real.exp (C₁ * L)) →
      ∀ data : (t : FrequencyTree S n) → (ZMod (Q t))ˣ →
        List (ZMod (Q t))ˣ → Option (ArithmeticSplitData (Q t)),
      (∀ t R past d, data t R past = some d →
        d.hasFrequencies (singleTreeNodeFrequencies S n t past.length)) →
      Real.exp (-(2 ^ n : ℕ) * Δ + K) * harmonicHistorySupportSum P S V n Q T hunit data ≤
        Real.exp ((C₁ + max (Real.log (3 / a)) 0) * (2 ^ n : ℕ) * L + ε * m) := by
  filter_upwards [single_history_budget_parameters n K C ε hC hε] with m hm
  obtain ⟨D, hD, hdiv, hbudget⟩ := hm
  intro N V Δ P S hN hV hS Q _hQ T h J hunit hsmall hrange a C₁ L ha hL hmass hJ data hmatch
  have hdivN (q : ℕ) (hq : q ≠ 0) (hqN : q ≤ N ^ 2) : (q.divisors.card : ℝ) ≤ D := by
    apply hdiv q hq
    calc
      (q : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hqN
      _ ≤ Real.exp (C * m) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hN 2
      _ = Real.exp (2 * C * m) := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hs := harmonic_history_support_le P S N V n D hD hS hdivN Q T h J hunit hsmall hrange data hmatch
  have hc := harmonic_prior_product_cost_linear n T J a C₁ L ha hL hmass hJ
  have hb := hbudget N V Δ hN hV
  unfold harmonicHistorySupportSum
  calc
    _ ≤ Real.exp (-(2 ^ n : ℕ) * Δ + K) *
        ((∏ i, (∑ p ∈ T i, (p : ℝ)⁻¹)⁻¹ * (3 * J i)) *
          ((4 * D ^ 3 * (1 + Real.log N)) ^ (2 ^ n - 1) * (2 * (V : ℝ)) ^ (2 ^ n))) :=
      mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le
    _ = (∏ i, (∑ p ∈ T i, (p : ℝ)⁻¹)⁻¹ * (3 * J i)) *
        (Real.exp (-(2 ^ n : ℕ) * Δ + K) *
          ((4 * D ^ 3 * (1 + Real.log N)) ^ (2 ^ n - 1) * (2 * (V : ℝ)) ^ (2 ^ n))) := by ring
    _ ≤ Real.exp ((C₁ + max (Real.log (3 / a)) 0) * (2 ^ n : ℕ) * L) * Real.exp (ε * m) :=
      mul_le_mul hc hb (by
        have := Real.log_natCast_nonneg N
        positivity) (Real.exp_pos _).le
    _ = _ := (Real.exp_add _ _).symm

end Ostmann

end OAI
