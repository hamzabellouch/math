import OAI.NumberTheory.Ostmann.Construction.PrimeOriginalPair
import OAI.NumberTheory.Ostmann.Characters.DyadicCharacterBudget

namespace OAI

/-! # Numerical decay with all range, unit and large-prime support costs -/

namespace Ostmann

open scoped BigOperators
open Filter

theorem eventual_ranged_word_pair_decay {σ : Type*} {n : ℕ}
    (K z α β γ c : ℝ) (d : ℕ)
    (hK : 0 ≤ K) (hz : 0 ≤ z) (hα : 0 < α) (hαβ : α < β)
    (hγβ : γ < β) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,
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
    with L hL template template' D D' t t' ht ht' B A E f f' P Q lower Bq m
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

/-- Point-mass and polynomial history losses remain negligible alongside the
already proved one-sided character error. -/
theorem eventual_prime_support_decay (K z α c : ℝ) (d : ℕ)
    (hK : 0 ≤ K) (hz : 0 ≤ z) (hα : 0 < α) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ (m δ loss atom value : ℝ),
      0 ≤ m → m ≤ z * L → 0 ≤ loss →
      loss ≤ Real.exp (K * (1 + m) ^ d) →
      atom ≤ Real.exp (-c * Real.exp (α * L)) →
      δ ≤ Real.exp (-(c / 4) * Real.exp (α * L)) →
      value ≤ δ + loss * atom → value ≤ Real.exp (-(c / 8) * Real.exp (α * L)) := by
  have hpoly := eventual_polynomial_log_budget K z α (c / 2) d hK hz hα (by positivity)
  have htwo := eventual_diagonal_atom_error 0 z α (c / 4) d (by norm_num) hz hα (by positivity)
  filter_upwards [hpoly, htwo] with L hpoly htwo m δ loss atom value hm hmL hloss hcost hatom hδ hv
  have he : loss * atom ≤ Real.exp (-(c / 2) * Real.exp (α * L)) := by
    calc
      _ ≤ loss * Real.exp (-c * Real.exp (α * L)) := mul_le_mul_of_nonneg_left hatom hloss
      _ ≤ Real.exp (K * (1 + m) ^ d) * Real.exp (-c * Real.exp (α * L)) :=
        mul_le_mul_of_nonneg_right hcost (Real.exp_nonneg _)
      _ = Real.exp (K * (1 + m) ^ d - c * Real.exp (α * L)) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith [hpoly m hm hmL])
  have he' : Real.exp (-(c / 2) * Real.exp (α * L)) ≤
      Real.exp (-(c / 4) * Real.exp (α * L)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.exp_pos (α * L)]
  have hh := htwo m hm hmL
  simp only [zero_mul, zero_sub] at hh
  calc
    value ≤ δ + loss * atom := hv
    _ ≤ Real.exp (-(c / 4) * Real.exp (α * L)) + Real.exp (-(c / 4) * Real.exp (α * L)) :=
      add_le_add hδ (he.trans he')
    _ = 2 * Real.exp (-(c / 4) * Real.exp (α * L)) := by ring
    _ ≤ _ := by convert hh using 1 <;> congr 2 <;> ring

end Ostmann

end OAI
