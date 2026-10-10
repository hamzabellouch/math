import OAI.NumberTheory.Ostmann.Characters.CharacterPrimeFrequency
import OAI.NumberTheory.Ostmann.Construction.InitialGapRate

namespace OAI

/-! # The actual rounded initial cutoff covers the Poisson window -/
namespace Ostmann
open Filter

/-- The original two-sqrt reserve absorbs the fixed Fourier support and the
covering error of the selected cells, including the floor in the cutoff. -/
theorem eventual_character_poisson_cutoff (C H : ℝ) (hH : 0 ≤ H) :
    ∀ᶠ m : ℝ in atTop, ∀ Δ : ℝ, 0 ≤ Δ →
      H * Real.exp (Δ + C) ≤ naturalTransferCutoff Δ m 0 := by
  filter_upwards [Real.tendsto_sqrt_atTop.eventually
      (eventually_ge_atTop ((C + Real.log (2 * (H + 1))) / 2)),
    Real.tendsto_sqrt_atTop.eventually (eventually_ge_atTop (Real.log 2 / 2))]
      with m hm hlog Δ hΔ
  have hE : Real.log 2 ≤ Δ + 2 * Real.sqrt m := by linarith
  have he := (natural_exp_cutoff_bounds (Δ + 2 * Real.sqrt m) hE).2.2
  have hg : C + Real.log (2 * (H + 1)) ≤ 2 * Real.sqrt m := by linarith
  have hh := Real.exp_le_exp.mpr hg
  rw [Real.exp_add, Real.exp_log (by positivity : 0 < 2 * (H + 1))] at hh
  have hscale := mul_le_mul_of_nonneg_left hh (Real.exp_nonneg Δ)
  have hnonneg : 0 ≤ Real.exp Δ * Real.exp C := by positivity
  have he' : Real.exp (Δ + 2 * Real.sqrt m) ≤
      2 * (naturalTransferCutoff Δ m 0 : ℝ) := by
    simpa only [naturalTransferCutoff, transferErrorScale, pow_zero, one_mul, mul_one] using he
  rw [Real.exp_add] at he' ⊢
  nlinarith only [hscale, he', hnonneg]

theorem eventual_character_poisson_window (z d C H α : ℝ)
    (hz : 1 ≤ z) (hd : 0 ≤ d) (hH : 0 ≤ H) (hα : 0 < α) :
    ∀ᶠ L : ℝ in atTop,
      let m := ⌊z * L⌋₊
      let Δ := d * (m : ℝ)
      let N := naturalTransferCutoff Δ m 0
      H * Real.exp (Δ + C) ≤ N ∧
        ∀ p : ℕ, Real.exp (Real.exp (α * L)) ≤ p → H * Real.exp (Δ + C) < p := by
  have hz0 : 0 < z := by linarith
  filter_upwards [eventually_bulkCount_bounds z hz0,
    eventually_bulkCount z hz0 _
      ((tendsto_natCast_atTop_atTop (R := ℝ)).eventually
        (eventual_character_poisson_cutoff C H hH)),
    eventual_natural_cutoff_below_primes 0 d z α 1 hd hz0.le hα (by norm_num)]
      with L hm hN hp
  dsimp only
  have hbound := hN (d * (⌊z * L⌋₊ : ℝ)) (mul_nonneg hd (Nat.cast_nonneg _))
  refine ⟨hbound, ?_⟩
  intro p hmin
  have hm1 : (1 : ℝ) ≤ ⌊z * L⌋₊ := by exact_mod_cast hm.2.1
  have hmin' : Real.exp (1 * Real.exp (α * L)) ≤ (p : ℝ) := by
    simpa only [one_mul] using hmin
  exact hbound.trans_lt (by exact_mod_cast hp _ hm1 hm.2.2.1 p hmin' 0 (Nat.zero_le _))

end Ostmann

end OAI
