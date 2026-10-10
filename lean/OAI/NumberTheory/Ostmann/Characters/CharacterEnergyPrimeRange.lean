import OAI.NumberTheory.Ostmann.Characters.CharacterPrimeFrequency
import OAI.NumberTheory.Ostmann.Construction.DyadicPrimeRange

namespace OAI

/-! # Dyadic data for the actual prime-cell energy theorem -/
namespace Ostmann
open Filter

 theorem naturalTransferCutoff_pos (d m : ℝ) (hd : 0 ≤ d) (hm : 0 ≤ m) (j : ℕ) :
    0 < naturalTransferCutoff (d * m) m j := by
  apply Nat.floor_pos.mpr
  apply Real.one_le_exp_iff.mpr
  unfold transferErrorScale
  positivity

theorem eventual_twice_natural_cutoff_power_le (k r : ℕ) (d z α : ℝ)
    (hd : 0 ≤ d) (hz : 0 ≤ z) (hα : 0 < α) :
    ∀ᶠ L : ℝ in atTop, ∀ m : ℝ, 1 ≤ m → m ≤ z * L →
      ∀ A : ℕ, Real.exp (Real.exp (α * L)) ≤ A → ∀ j ≤ k,
        2 * naturalTransferCutoff (d * m) m j ^ r ≤ A := by
  have hg : ∀ᶠ L : ℝ in atTop, 2 * Real.log 2 ≤ Real.exp (α * L) :=
    (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hα)).eventually
      (eventually_ge_atTop _)
  filter_upwards [hg, eventual_natural_cutoff_power_lt k r d z α (1 / 2)
    hd hz hα (by norm_num)] with L hg hcut
  intro m hm hmL A hA j hj
  have he : 2 * Real.exp ((1 / 2 : ℝ) * Real.exp (α * L)) ≤
      Real.exp (Real.exp (α * L)) := by
    calc
      _ = Real.exp (Real.log 2 + (1 / 2 : ℝ) * Real.exp (α * L)) := by
        rw [Real.exp_add, Real.exp_log (by norm_num)]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hc := mul_le_mul_of_nonneg_left (hcut m hm hmL j hj).le (by norm_num : (0 : ℝ) ≤ 2)
  have hf := hc.trans (he.trans hA)
  exact_mod_cast hf

/-- Both dyadic endpoints are explicit ceilings/floors of the physical prime
range. The finite denominator power is below the first dyadic point. -/
theorem eventual_character_energy_prime_range (k r : ℕ) (d z α β : ℝ)
    (hd : 0 ≤ d) (hz : 0 ≤ z) (hα : 0 < α) (hβ : 0 ≤ β) :
    ∀ᶠ L : ℝ in atTop, ∀ m : ℝ, 1 ≤ m → m ≤ z * L →
      ∀ S : Finset ℕ,
      (∀ p ∈ S, Real.exp (Real.exp (α * L)) ≤ p ∧
        (p : ℝ) ≤ Real.exp (Real.exp (β * L))) →
      ∃ h J : ℕ,
        (∀ j ≤ k, naturalTransferCutoff (d * m) m j ^ r ≤ 2 ^ h) ∧
        (∀ p ∈ S, 2 ^ h ≤ p ∧ p < 2 ^ (h + J)) ∧
        (J : ℝ) ≤ Real.exp ((β + Real.log ((Real.log 2)⁻¹ + 1)) * L) := by
  filter_upwards [eventual_twice_natural_cutoff_power_le k r d z α hd hz hα,
    eventually_ge_atTop (1 : ℝ)] with L hcut hL
  intro m hm hmL S hS
  let A : ℕ := ⌈Real.exp (Real.exp (α * L))⌉₊
  let B : ℕ := ⌊Real.exp (Real.exp (β * L))⌋₊
  have hbounds : ∀ p ∈ S, A ≤ p ∧ p ≤ B := by
    intro p hp
    exact ⟨Nat.ceil_le.mpr (hS p hp).1, Nat.le_floor (hS p hp).2⟩
  have hA : Real.exp (Real.exp (α * L)) ≤ (A : ℝ) := Nat.le_ceil _
  have hq (j : ℕ) : 0 < naturalTransferCutoff (d * m) m j ^ r :=
    pow_pos (naturalTransferCutoff_pos d m hd (by linarith) j) r
  have hranges (j : ℕ) (hj : j ≤ k) := dyadic_prime_range_cover A B
    (naturalTransferCutoff (d * m) m j ^ r) (hq j) (hcut m hm hmL A hA j hj) S hbounds
  refine ⟨Nat.log 2 A, Nat.log 2 B + 1, fun j hj => (hranges j hj).1,
    (hranges 0 (Nat.zero_le _)).2, ?_⟩
  exact dyadic_prime_range_count B β L hβ hL (Nat.floor_le (Real.exp_nonneg _))

end Ostmann

end OAI
