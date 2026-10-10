import OAI.NumberTheory.Ostmann.Characters.CharacterTargetGaps

namespace OAI

/-! # The separated long/short scales absorb the one-sided losses -/

namespace Ostmann

open Filter

theorem eventual_polynomial_log_budget (C z α ε : ℝ) (d : ℕ)
    (hC : 0 ≤ C) (hz : 0 ≤ z) (hα : 0 < α) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ m : ℝ, 0 ≤ m → m ≤ z * L →
      C * (1 + m) ^ d ≤ ε * Real.exp (α * L) := by
  have hb := ((isLittleO_pow_exp_pos_mul_atTop d hα).const_mul_left
    (C * (z + 1) ^ d)).bound hε
  filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with L hlarge hL m hm hmL
  have hx : 1 + m ≤ (z + 1) * L := by nlinarith
  have hp : (1 + m) ^ d ≤ ((z + 1) * L) ^ d := pow_le_pow_left₀ (by linarith) hx d
  have hlarge' : C * (z + 1) ^ d * L ^ d ≤ ε * Real.exp (α * L) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ C * (z + 1) ^ d * L ^ d),
      abs_of_pos (Real.exp_pos _)] using hlarge
  calc
    _ ≤ C * (((z + 1) * L) ^ d) := mul_le_mul_of_nonneg_left hp hC
    _ = C * (z + 1) ^ d * L ^ d := by rw [mul_pow]; ring
    _ ≤ _ := hlarge'

/-- The square-mean off-diagonal error after all polynomial history costs.
The long logarithmic scale β exceeds both the short scale γ and the desired
error scale α. -/
theorem eventual_separated_character_error (C z α β γ c : ℝ) (d : ℕ)
    (hC : 0 ≤ C) (hz : 0 ≤ z) (hα : 0 < α) (hαβ : α < β)
    (hγβ : γ < β) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ m : ℝ, 0 ≤ m → m ≤ z * L →
      Real.exp (C * (1 + m) ^ d + 2 * Real.exp (γ * L) - Real.exp (β * L)) ≤
        Real.exp (-c * Real.exp (α * L)) := by
  have hpoly := eventual_polynomial_log_budget C z β (1 / 4) d hC hz (hα.trans hαβ) (by norm_num)
  have hshort := ((isLittleO_exp_mul_rpow_of_lt 0 hγβ).const_mul_left (2 : ℝ)).bound
    (by norm_num : (0 : ℝ) < 1 / 4)
  have herr := ((isLittleO_exp_mul_rpow_of_lt 0 hαβ).const_mul_left c).bound
    (by norm_num : (0 : ℝ) < 1 / 4)
  filter_upwards [hpoly, hshort, herr] with L hpoly hshort herr m hm hmL
  have hs : 2 * Real.exp (γ * L) ≤ Real.exp (β * L) / 4 := by
    simpa only [Real.rpow_zero, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ 2 * Real.exp (γ * L)),
      abs_of_pos (Real.exp_pos _), one_div_mul_eq_div] using hshort
  have he : c * Real.exp (α * L) ≤ Real.exp (β * L) / 4 := by
    simpa only [Real.rpow_zero, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ c * Real.exp (α * L)),
      abs_of_pos (Real.exp_pos _), one_div_mul_eq_div] using herr
  have hp := hpoly m hm hmL
  apply Real.exp_le_exp.mpr
  nlinarith [Real.exp_pos (β * L)]

/-- The small diagonal atom remains exponentially small after multiplication
by every fixed polynomial-in-m exponential loss. -/
theorem eventual_diagonal_atom_error (C z α c : ℝ) (d : ℕ)
    (hC : 0 ≤ C) (hz : 0 ≤ z) (hα : 0 < α) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ m : ℝ, 0 ≤ m → m ≤ z * L →
      2 * Real.exp (C * (1 + m) ^ d - c * Real.exp (α * L)) ≤
        Real.exp (-(c / 2) * Real.exp (α * L)) := by
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hb := eventual_polynomial_log_budget (C + Real.log 2) z α (c / 2) d
    (by positivity) hz hα (by positivity)
  filter_upwards [hb] with L hb m hm hmL
  have hpow : 1 ≤ (1 + m) ^ d := one_le_pow₀ (by linarith)
  have hlog : Real.log 2 ≤ Real.log 2 * (1 + m) ^ d := by nlinarith
  have hh := hb m hm hmL
  calc
    _ = Real.exp (Real.log 2 + C * (1 + m) ^ d - c * Real.exp (α * L)) := by
      rw [show Real.log 2 + C * (1 + m) ^ d - c * Real.exp (α * L) =
        Real.log 2 + (C * (1 + m) ^ d - c * Real.exp (α * L)) by ring,
        Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

theorem norm_le_exp_half_of_sq_le (w : ℂ) (E : ℝ) (h : ‖w‖ ^ 2 ≤ Real.exp E) :
    ‖w‖ ≤ Real.exp (E / 2) := by
  have he : (Real.exp (E / 2)) ^ 2 = Real.exp E := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  nlinarith [Real.exp_pos (E / 2), norm_nonneg w]

/-- Both parts of the expanded square, including all fixed polynomial losses,
obey one common smallness bound. -/
theorem eventual_one_sided_squared_budget (C z α β γ c : ℝ) (d : ℕ)
    (hC : 0 ≤ C) (hz : 0 ≤ z) (hα : 0 < α) (hαβ : α < β)
    (hγβ : γ < β) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ m : ℝ, 0 ≤ m → m ≤ z * L →
      Real.exp (C * (1 + m) ^ d) *
        (Real.exp (-c * Real.exp (α * L)) +
          Real.exp (2 * Real.exp (γ * L) - Real.exp (β * L))) ≤
        Real.exp (-(c / 2) * Real.exp (α * L)) := by
  have hdiag := eventual_diagonal_atom_error C z α c d hC hz hα hc
  have hoff := eventual_separated_character_error 0 z α β γ c d (by norm_num) hz hα hαβ hγβ hc
  filter_upwards [hdiag, hoff] with L hdiag hoff m hm hmL
  have ho := hoff m hm hmL
  simp only [zero_mul, zero_add] at ho
  calc
    _ ≤ Real.exp (C * (1 + m) ^ d) *
        (Real.exp (-c * Real.exp (α * L)) + Real.exp (-c * Real.exp (α * L))) := by
      exact mul_le_mul_of_nonneg_left (add_le_add le_rfl ho) (Real.exp_pos _).le
    _ = 2 * Real.exp (C * (1 + m) ^ d - c * Real.exp (α * L)) := by
      rw [show C * (1 + m) ^ d - c * Real.exp (α * L) =
        C * (1 + m) ^ d + (-c * Real.exp (α * L)) by ring, Real.exp_add]
      ring
    _ ≤ _ := hdiag m hm hmL

theorem eventual_one_sided_amplitude_budget (C z α β γ c : ℝ) (d : ℕ)
    (hC : 0 ≤ C) (hz : 0 ≤ z) (hα : 0 < α) (hαβ : α < β)
    (hγβ : γ < β) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ (m : ℝ) (w : ℂ), 0 ≤ m → m ≤ z * L →
      ‖w‖ ^ 2 ≤ Real.exp (C * (1 + m) ^ d) *
        (Real.exp (-c * Real.exp (α * L)) +
          Real.exp (2 * Real.exp (γ * L) - Real.exp (β * L))) →
      ‖w‖ ≤ Real.exp (-(c / 4) * Real.exp (α * L)) := by
  filter_upwards [eventual_one_sided_squared_budget C z α β γ c d hC hz hα hαβ hγβ hc]
    with L hL m w hm hmL hw
  have h := norm_le_exp_half_of_sq_le w _ (hw.trans (hL m hm hmL))
  convert h using 1
  congr 1
  ring

end Ostmann

end OAI
