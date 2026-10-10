import OAI.NumberTheory.Ostmann.Arithmetic.MovingProductFrequency
import OAI.NumberTheory.Ostmann.Construction.SpectatorBulkScale
import OAI.NumberTheory.Ostmann.Construction.SmoothGiantActiveSupport
import OAI.NumberTheory.Ostmann.Construction.OneSidedDecayBudget

namespace OAI

/-! # Live giant primes exceed the initial product-centered Fourier cutoff -/
namespace Ostmann
open Filter
open scoped Classical

theorem eventual_initial_giant_frequency (k : ℕ) (A : ℝ) (hA : 0 ≤ A) :
    ∀ᶠ L : ℝ in atTop, ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime) →
      ∀ (T : ℕ → ℝ) (W Y G : ℝ),
      W - Y ≤ A * spectatorBulkCount k L →
      Real.exp ((1 / 20 : ℝ) * L) - 2 ≤ G →
      ∀ p : P, smoothGiantPrior P logCellProfile G p ≠ 0 →
        movingProductNaturalCutoff T W Y ((spectatorBulkCount k L : ℝ) / 4) 0 < (p : ℕ) := by
  have hlarge := (Real.tendsto_exp_atTop.comp
    (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 20))).eventually
      (eventually_ge_atTop (8 : ℝ))
  filter_upwards [eventual_polynomial_log_budget (A + 2) ((k : ℝ) ^ 4) (1 / 20) (1 / 2) 1
      (by linarith) (by positivity) (by norm_num) (by norm_num),
    hlarge, eventually_ge_atTop (0 : ℝ)] with L hbudget hlarge hL
  intro P hP T W Y G hW hG p hp
  let m : ℝ := spectatorBulkCount k L
  change W - Y ≤ A * m at hW
  change 8 ≤ Real.exp ((1 / 20 : ℝ) * L) at hlarge
  have hm : 0 ≤ m := Nat.cast_nonneg _
  have hroot : Real.sqrt m ≤ m + 1 := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · linarith
    · nlinarith [sq_nonneg m]
  have hb := hbudget m hm (spectatorBulkCount_upper k L hL)
  simp only [pow_one] at hb
  have he : movingProductFrequencyExponent T W Y (m / 4) 0 < G - 1 := by
    simp only [movingProductFrequencyExponent, movingProductExponent, pow_zero, one_mul]
    rw [show 4 * (m / 4) = m by ring]
    have ha := mul_nonneg hA hm
    nlinarith only [hW, hG, hlarge, hroot, hb, hm, hA]
  have hbound : (movingProductNaturalCutoff T W Y (m / 4) 0 : ℝ) < (p : ℝ) := by
    apply (Nat.floor_le (Real.exp_pos _).le).trans_lt
    apply (Real.exp_lt_exp.mpr he).trans
    exact (smoothGiantPrior_active_bounds P hP logCellProfile G logCellProfile_zero_outside p hp).1
  exact_mod_cast hbound

end Ostmann

end OAI
