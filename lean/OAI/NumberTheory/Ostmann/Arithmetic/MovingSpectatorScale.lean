import OAI.NumberTheory.Ostmann.Arithmetic.MovingSpectatorModulus

namespace OAI

/-! # Spectator periods fit the same published progression range -/

namespace Ostmann
open Filter Asymptotics

theorem movingSpectator_exponent_budget (n : ℕ) (C : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      ((4 * (4 ^ n - 1) + 2 * (2 ^ n - 1) : ℕ) : ℝ) *
          (C * L + C * Real.exp ((1 / 100 : ℝ) * L)) +
        ((1 / 1000 : ℝ) * L) * Real.exp ((1 / 1000 : ℝ) * L) ≤
          Real.exp ((12 / 1000 : ℝ) * L) := by
  let E : ℝ := (4 * (4 ^ n - 1) + 2 * (2 ^ n - 1) : ℕ)
  have hlin : (fun L : ℝ => (E * C) * L) =o[atTop]
      (fun L => Real.exp ((12 / 1000 : ℝ) * L)) := by
    simpa only [pow_one] using
      (isLittleO_pow_exp_pos_mul_atTop 1 (by norm_num : (0 : ℝ) < 12 / 1000)).const_mul_left (E * C)
  have hexp : (fun L : ℝ => (E * C) * Real.exp ((1 / 100 : ℝ) * L)) =o[atTop]
      (fun L => Real.exp ((12 / 1000 : ℝ) * L)) := by
    simpa only [Real.rpow_zero, mul_one] using
      (isLittleO_exp_mul_rpow_of_lt 0 (by norm_num : (1 / 100 : ℝ) < 12 / 1000)).const_mul_left (E * C)
  have hspec : (fun L : ℝ => (1 / 1000 : ℝ) *
      (Real.exp ((1 / 1000 : ℝ) * L) * L)) =o[atTop]
      (fun L => Real.exp ((12 / 1000 : ℝ) * L)) := by
    simpa only [Real.rpow_one] using
      (isLittleO_exp_mul_rpow_of_lt 1 (by norm_num : (1 / 1000 : ℝ) < 12 / 1000)).const_mul_left (1 / 1000)
  filter_upwards [((hlin.add hexp).add hspec).bound (by norm_num : (0 : ℝ) < 1)] with L hL
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul] at hL
  have h := (le_abs_self _).trans hL
  change E * (C * L + C * Real.exp ((1 / 100 : ℝ) * L)) +
    ((1 / 1000 : ℝ) * L) * Real.exp ((1 / 1000 : ℝ) * L) ≤ _
  nlinarith only [h]

/-- The cutoff is uniform in the actual tree and the spectator prime set.
The period includes both integer division denominators and all spectators. -/
theorem movingSpectator_progression_range {σ : Type*} (n : ℕ) (C : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
      (childBound pivotBound : ℕ → ℕ) (T : MovingSlotData σ n)
      (hf : T.Frequencies (· ≠ 0)) (B : ℕ), 1 ≤ B →
      T.Frequencies (fun s => s.natAbs ≤ B) → T.CompensationBound value B →
      (B : ℝ) ≤ Real.exp (C * L + C * Real.exp ((1 / 100 : ℝ) * L)) →
      ∀ (S : Finset ℕ) (R : ℕ), (∀ q ∈ S, 0 < q ∧ q ≤ R) →
      (R : ℝ) ≤ Real.exp ((1 / 1000 : ℝ) * L) →
      movingSpectatorModulus value hvalue childBound pivotBound T hf id S ≤
        ⌊Real.exp (Real.exp ((12 / 1000 : ℝ) * L))⌋₊ := by
  filter_upwards [movingSpectator_exponent_budget n C, eventually_ge_atTop (0 : ℝ)] with L hL hL0
  intro value hvalue childBound pivotBound T hf B hB hfreq hcomp hb S R hS hR
  apply Nat.le_floor
  apply (movingSpectatorModulus_exp value hvalue childBound pivotBound T hf S B hB hfreq hcomp
    _ _ hb (small_spectator_product_exp S R hS _ (by positivity) hR)).trans
  exact Real.exp_le_exp.mpr hL

end Ostmann

end OAI
