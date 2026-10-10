import OAI.NumberTheory.Ostmann.Arithmetic.MovingProductFrequency
import OAI.NumberTheory.Ostmann.Arithmetic.MovingFrequencyBudget

namespace OAI

/-! # Centered initial windows and the original energy cutoff -/
namespace Ostmann
open Filter

/-- The initial cutoff depends on the quotient of the two product scales. -/
theorem movingProductNaturalCutoff_zero_translate (T : ℕ → ℝ) (W Y m D : ℝ) :
    movingProductNaturalCutoff T (W - D) (Y - D) m 0 =
      movingProductNaturalCutoff T W Y m 0 := by
  unfold movingProductNaturalCutoff movingProductFrequencyExponent
  simp only [movingProductExponent]
  congr 2
  ring

theorem movingProductFrequency_mono_mass (T : ℕ → ℝ) (W Y a b : ℝ) (n : ℕ)
    (hab : a ≤ b) :
    movingProductFrequencyExponent T W Y a n ≤ movingProductFrequencyExponent T W Y b n := by
  have hh := Real.sqrt_le_sqrt (show 4 * a ≤ 4 * b by linarith)
  have hmul := mul_le_mul_of_nonneg_left hh (show 0 ≤ (2 : ℝ) ^ n by positivity)
  unfold movingProductFrequencyExponent
  linarith

/-- Using one quarter of the bulk mass in the frequency reserve leaves room
for the fixed width of the actual initial product window. The diagonal energy
estimate retains its original `sqrt (4m)` cutoff. -/
theorem movingProductNaturalCutoff_zero_window (T : ℕ → ℝ)
    (W Y Δ m H : ℝ) (hW : W - Y ≤ Δ + H)
    (hwidth : H ≤ Real.sqrt m) :
    (movingProductNaturalCutoff T W Y (m / 4) 0 : ℝ) ≤
      Real.exp (Δ + Real.sqrt (4 * m)) := by
  have hs : Real.sqrt (4 * m) = 2 * Real.sqrt m := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have hq : 4 * (m / 4) = m := by ring
  have he : movingProductFrequencyExponent T W Y (m / 4) 0 ≤
      Δ + Real.sqrt (4 * m) := by
    simp only [movingProductFrequencyExponent, movingProductExponent, pow_zero, one_mul, hq]
    rw [hs]
    linarith
  exact (Nat.floor_le (Real.exp_pos _).le).trans (Real.exp_le_exp.mpr he)

theorem eventually_initial_product_reserve (H : ℝ) :
    ∀ᶠ m : ℝ in atTop, 64 ≤ m / 4 ∧ H ≤ Real.sqrt m := by
  filter_upwards [eventually_ge_atTop (256 : ℝ),
    Real.tendsto_sqrt_atTop.eventually (eventually_ge_atTop H)] with m hm hH
  exact ⟨by linarith, hH⟩

theorem movingProductNaturalCutoff_card_bound (T : ℕ → ℝ)
    (W Y m A : ℝ) (n : ℕ)
    (hF : 0 ≤ movingProductFrequencyExponent T W Y m n)
    (hA : movingProductFrequencyExponent T W Y m n + Real.log 3 ≤ A) :
    ((transferFrequencyRange (movingProductNaturalCutoff T W Y m n)).card : ℝ) ≤
      Real.exp A := by
  have hv : (movingProductNaturalCutoff T W Y m n : ℝ) ≤
      Real.exp (movingProductFrequencyExponent T W Y m n) :=
    Nat.floor_le (Real.exp_pos _).le
  have he := Real.one_le_exp hF
  rw [card_transferFrequencyRange]
  push_cast
  calc
    _ ≤ 3 * Real.exp (movingProductFrequencyExponent T W Y m n) := by linarith
    _ = Real.exp (movingProductFrequencyExponent T W Y m n + Real.log 3) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
      ring
    _ ≤ _ := Real.exp_le_exp.mpr hA

end Ostmann

end OAI
