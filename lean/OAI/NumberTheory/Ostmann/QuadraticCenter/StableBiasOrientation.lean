import OAI.NumberTheory.Ostmann.Construction.StablePrimeSelection

namespace OAI

/-! # The retained stable primes have compatible opposite orientations -/

namespace Ostmann

open scoped BigOperators Classical

theorem stable_prime_bias_orientations (P : Finset ℕ) (S T : ℕ → Finset ℕ)
    (μ ν f : ℕ → ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ) (hδU : δ ≤ 1)
    (hS : ∀ p ∈ P, (S p).Nonempty) (hT : ∀ p ∈ P, (T p).Nonempty)
    (hcard : ∀ p ∈ P, (S p).card + (T p).card = p)
    (hfS : ∀ p ∈ P, ∀ r ∈ S p, |f p r| ≤ 1)
    (hfT : ∀ p ∈ P, ∀ r ∈ T p, |f p r| ≤ 1)
    (hsum : ∀ p ∈ P, (∑ r ∈ S p, f p r) + (∑ r ∈ T p, f p r) = 0)
    (hbias : ∀ p ∈ P, δ ≤ |residueTestMean (S p) (f p)|) :
    ∃ ε : ℕ → ℝ, ∀ p ∈ stableBiasPrimes P S T μ ν δ,
      (ε p = 1 ∨ ε p = -1) ∧
      δ / 4 ≤ ε p * (∑ r ∈ S p, μ p r * f p r) ∧
      δ / 4 ≤ -(ε p) * (∑ r ∈ T p, ν p r * f p r) := by
  let R := stableBiasPrimes P S T μ ν δ
  have hpoint (p : ℕ) (hp : p ∈ R) : ∃ e : ℝ, (e = 1 ∨ e = -1) ∧
      δ / 4 ≤ e * (∑ r ∈ S p, μ p r * f p r) ∧
      δ / 4 ≤ -e * (∑ r ∈ T p, ν p r * f p r) := by
    have hpP := (Finset.mem_filter.mp hp).1
    have hstable := stableBiasPrimes_pointwise P S T μ ν f f δ hδ.le hδU hS hT hcard hfS hfT p hp
    have hc : (0 : ℝ) < (T p).card := by exact_mod_cast (hT p hpP).card_pos
    have hsplit : ((S p).card : ℝ) + (T p).card = p := by exact_mod_cast hcard p hpP
    have hratio : (1 / 2 : ℝ) ≤ ((S p).card : ℝ) / (T p).card := by
      apply (le_div_iff₀ hc).mpr
      linarith [hstable.1]
    apply exists_opposite_bias_orientation (residueTestMean (S p) (f p))
      (residueTestMean (T p) (f p)) _ _ (((S p).card : ℝ) / (T p).card) δ
      hδ hratio (hbias p hpP) (paired_test_means (S p) (T p) (f p) (hS p hpP) (hT p hpP) (hsum p hpP))
      hstable.2.2.1 hstable.2.2.2
  let ε : ℕ → ℝ := fun p => if hp : p ∈ R then Classical.choose (hpoint p hp) else 1
  refine ⟨ε, ?_⟩
  intro p hp
  have hpR : p ∈ R := hp
  simpa [ε, hpR] using Classical.choose_spec (hpoint p hpR)

end Ostmann

end OAI
