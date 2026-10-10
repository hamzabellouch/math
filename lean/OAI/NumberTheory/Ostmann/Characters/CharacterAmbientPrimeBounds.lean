import OAI.NumberTheory.Ostmann.Characters.CharacterConstructedRanges
import OAI.NumberTheory.Ostmann.Construction.PrimeLogLogIntervalMass

namespace OAI

/-! # The original prime band supplies its total mass and ambient ranges -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem eventual_character_prime_total {C : ℝ} (hM : MertensEstimate C)
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) :
    ∀ᶠ L : ℝ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, α * L < Real.log (Real.log (p : ℝ)) ∧
        Real.log (Real.log (p : ℝ)) ≤ β * L) →
      (∑ p : P, (p : ℝ)⁻¹) ≤ (Real.exp 1 + 1) * (β - α + 1) * L := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_id.const_mul_atTop hα).eventually (eventually_ge_atTop (max C 0))]
    with L hL hbase P hP hrange
  have he : weightedIntervalMass P (fun p => Real.log (Real.log p))
      (fun p => (p : ℝ)⁻¹) (α * L) (β * L) = ∑ p : P, (p : ℝ)⁻¹ := by
    simp only [weightedIntervalMass]
    rw [Finset.filter_eq_self.mpr hrange]
    exact (Finset.sum_coe_sort P (fun p : ℕ => (p : ℝ)⁻¹)).symm
  have hh := prime_loglog_interval_mass_upper hM P hP (α * L) (β * L) hbase
    (mul_le_mul_of_nonneg_right hαβ.le (by linarith))
  rw [he] at hh
  have hp : 0 < Real.exp 1 + 1 := by positivity
  have hscale := mul_le_mul_of_nonneg_left hL hp.le
  nlinarith only [hh, hscale]

theorem character_ambient_prime_ranges (α β L : ℝ) (hα : 0 < α) (hL : 0 ≤ L)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hrange : ∀ p ∈ P, α * L < Real.log (Real.log (p : ℝ)) ∧
      Real.log (Real.log (p : ℝ)) ≤ β * L) :
    ∀ p ∈ P, Real.exp (Real.exp ((α / 2) * L)) ≤ p ∧
      (p : ℝ) ≤ Real.exp (Real.exp ((β + 1) * L)) := by
  intro p hp
  constructor
  · apply prime_of_loglog_lower p (hP p hp)
    exact (show (α / 2) * L ≤ α * L by nlinarith only [mul_nonneg hα.le hL]).trans
      (hrange p hp).1.le
  · apply prime_of_loglog_upper p (hP p hp)
    exact (hrange p hp).2.trans (by nlinarith only [hL])

end Ostmann

end OAI
