import OAI.NumberTheory.Ostmann.Characters.CharacterPrimeFrequency

namespace OAI

/-! # Every live initial prime exceeds the Poisson product ratio -/
namespace Ostmann
open Filter

theorem eventual_linear_product_prime_window (H C z α : ℝ) (hC : 0 ≤ C) (hα : 0 < α) :
    ∀ᶠ L : ℝ in atTop, ∀ m : ℕ, (m : ℝ) ≤ z * L →
      ∀ D : ℝ, D ≤ C * m → ∀ p : ℕ,
        Real.exp (Real.exp (α * L)) ≤ (p : ℝ) → H * Real.exp D < (p : ℝ) := by
  have hlinear := ((isLittleO_pow_exp_pos_mul_atTop 1 hα).const_mul_left (C * z)).bound
    (show (0 : ℝ) < 1 / 4 by norm_num)
  have hconstant := (Real.tendsto_exp_atTop.comp
    (tendsto_id.const_mul_atTop hα)).eventually (eventually_ge_atTop (4 * H))
  filter_upwards [hlinear, hconstant] with L hlinear hconstant m hm D hD p hp
  simp only [Function.comp_apply, id_eq] at hconstant
  have hl : C * z * L ≤ (1 / 4 : ℝ) * Real.exp (α * L) := by
    apply (le_abs_self _).trans
    simpa only [Real.norm_eq_abs, pow_one, abs_of_pos (Real.exp_pos _)] using hlinear
  have hd : D ≤ C * z * L := by
    have hh := mul_le_mul_of_nonneg_left hm hC
    linarith
  calc
    H * Real.exp D ≤ Real.exp H * Real.exp D :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp H]) (Real.exp_nonneg _)
    _ = Real.exp (H + D) := (Real.exp_add _ _).symm
    _ < Real.exp (Real.exp (α * L)) := Real.exp_lt_exp.mpr (by
      nlinarith only [hl, hd, hconstant, Real.exp_pos (α * L)])
    _ ≤ _ := hp

end Ostmann

end OAI
