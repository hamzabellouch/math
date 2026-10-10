import OAI.NumberTheory.Ostmann.Arithmetic.RangedPairParameterDecay

namespace OAI

/-! # One-sided numerical decay uniform over the growing prime-coordinate space -/
namespace Ostmann
universe u
open Filter
open scoped BigOperators

theorem eventual_ranged_word_pair_decay_uniform {n : ℕ}
    (K z α β γ c : ℝ) (d : ℕ)
    (hK : 0 ≤ K) (hz : 0 ≤ z) (hα : 0 < α) (hαβ : α < β)
    (hγβ : γ < β) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ (σ : Type u),
      ∀ (template template' : WordTransferTemplate σ n)
      (D D' : WordRangeDecoration σ n) (t t' : FrequencyTree ℤ n)
      (ht : NonzeroInternalFrequencies n t) (ht' : NonzeroInternalFrequencies n t')
      (B A E : ℕ) (f f' : WordFourierParameters n) (P Q : Finset ℕ)
      (lower : ℝ) (Bq : ℕ) (m : ℝ),
      0 ≤ m → m ≤ z * L →
      Real.exp (c * Real.exp (α * L)) ≤ lower →
      Real.exp (Real.exp (β * L)) ≤ (A : ℝ) →
      (Bq : ℝ) ≤ Real.exp (Real.exp (γ * L)) →
      2 * ((Nat.log 2 E + 1 : ℕ) : ℝ) * (∑ p ∈ P, (p : ℝ)⁻¹)⁻¹ *
        (∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ *
        (f.budget template t ht * f'.budget template' t' ht') ^ 2 ≤
          Real.exp (K * (1 + m) ^ d) →
      2 * ((Nat.log 2 E + 1 : ℕ) : ℝ) * (∑ p ∈ P, (p : ℝ)⁻¹)⁻¹ *
        (wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B : ℕ) *
        (3 ^ (2 * (((3 * 2 ^ n + 3 * (2 ^ n - 1) + 2 * (D.count + D'.count)) * B ^ (n + 1)) +
          ((3 * 2 ^ n + 3 * (2 ^ n - 1) + 2 * (D.count + D'.count)) * B ^ (n + 1)))) : ℕ) *
        (f.budget template t ht * f'.budget template' t' ht') ^ 2 ≤
          Real.exp (K * (1 + m) ^ d) →
      rangedWordTransferPairBound template template' D D' t t' ht ht' B f f'
        A E P Q lower Bq ≤ (Real.exp (-(c / 4) * Real.exp (α * L))) ^ 2 := by
  filter_upwards [eventual_one_sided_squared_budget K z α β γ c d hK hz hα hαβ hγβ hc]
    with L hL σ template template' D D' t t' ht ht' B A E f f' P Q lower Bq m
      hm hmL hlower hA hBq hcost₁ hcost₂
  have hh := dyadic_character_numeric_bound
    ((Nat.log 2 E + 1 : ℕ) : ℝ) (∑ p ∈ P, (p : ℝ)⁻¹)⁻¹ (∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹
    (wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B : ℕ)
    (3 ^ (2 * (((3 * 2 ^ n + 3 * (2 ^ n - 1) + 2 * (D.count + D'.count)) * B ^ (n + 1)) +
      ((3 * 2 ^ n + 3 * (2 ^ n - 1) + 2 * (D.count + D'.count)) * B ^ (n + 1)))) : ℕ)
    (f.budget template t ht * f'.budget template' t' ht') A lower Bq
    (Real.exp (K * (1 + m) ^ d)) α β γ c L
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    hlower hA (Nat.cast_nonneg _) hBq hcost₁ hcost₂
  apply hh.trans
  apply (hL m hm hmL).trans_eq
  rw [← Real.exp_nat_mul]
  congr 1
  ring

theorem eventual_ranged_pair_decay_from_data_uniform (n : ℕ)
    (b d C S H z α β γ c : ℝ)
    (hb : 0 ≤ b) (hd : 0 ≤ d) (hC : 0 ≤ C) (hS : 1 ≤ S) (hH : 0 ≤ H)
    (hz : 0 ≤ z) (hα : 0 < α) (hαβ : α < β) (hγβ : γ < β) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ (σ : Type u), ∀
      (T T' : WordTransferTemplate σ n) (D D' : WordRangeDecoration σ n)
      (t t' : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t)
      (ht' : NonzeroInternalFrequencies n t')
      (B V A E : ℕ) (f f' : WordFourierParameters n) (P Q : Finset ℕ)
      (lower : ℝ) (Bq : ℕ) (m : ℝ),
      0 ≤ m → m ≤ z * L →
      (B : ℝ) ≤ b * (1 + m) →
      (D.count : ℝ) ≤ d * (1 + m) → (D'.count : ℝ) ≤ d * (1 + m) →
      (V : ℝ) ≤ Real.exp (C * (1 + m)) →
      (∀ s ∈ allFrequencyList n t, s.natAbs ≤ V) →
      (∀ s ∈ allFrequencyList n t', s.natAbs ≤ V) →
      SchwartzMap.seminorm ℝ 0 0 f.profile ≤ S →
      SchwartzMap.seminorm ℝ 0 1 f.profile ≤ S →
      SchwartzMap.seminorm ℝ 0 0 f'.profile ≤ S →
      SchwartzMap.seminorm ℝ 0 1 f'.profile ≤ S →
      (∀ i, f.upper i - f.lower i ≤ Real.exp (C * (1 + m))) →
      (∀ i, f'.upper i - f'.lower i ≤ Real.exp (C * (1 + m))) →
      ((Nat.log 2 E + 1 : ℕ) : ℝ) ≤ Real.exp (H * (1 + m)) →
      (∑ p ∈ P, (p : ℝ)⁻¹)⁻¹ ≤ Real.exp (H * (1 + m)) →
      (∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ ≤ Real.exp (H * (1 + m)) →
      Real.exp (c * Real.exp (α * L)) ≤ lower →
      Real.exp (Real.exp (β * L)) ≤ (A : ℝ) →
      (Bq : ℝ) ≤ Real.exp (Real.exp (γ * L)) →
      rangedWordTransferPairBound T T' D D' t t' ht ht' B f f'
        A E P Q lower Bq ≤ (Real.exp (-(c / 4) * Real.exp (α * L))) ^ 2 := by
  let K := Real.log 2 + 6 * rangedPairExponent n b d C S H
  have hK : 0 ≤ K := by
    have hh := rangedPairExponent_nonneg n b d C S H hb hd hC (by linarith) hH
    dsimp [K]
    positivity
  filter_upwards [eventual_ranged_word_pair_decay_uniform (n := n) K z α β γ c (n + 2)
    hK hz hα hαβ hγβ hc] with L hL
  intro σ T T' D D' t t' ht ht' B V A E f f' P Q lower Bq m
    hm hmL hB hD hD' hV hf hf' hs₀ hs₁ hs₀' hs₁' hr hr' hE hP hQ hlower hA hBq
  have hcost := ranged_pair_numeric_costs T T' D D' t t' ht ht' B V E f f' P Q
    b d C S H m hb hd hC hS hH hm hB hD hD' hV hf hf' hs₀ hs₁ hs₀' hs₁' hr hr'
    hE hP hQ
  exact hL σ T T' D D' t t' ht ht' B A E f f' P Q lower Bq m hm hmL hlower hA hBq
    hcost.1 hcost.2

end Ostmann

end OAI
