import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterGlobalBound
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterLogDerivative

namespace OAI

/-! A uniform prime-tail consequence of the effective all-height character
strip, retaining its polynomial modulus cost explicitly. -/

namespace TwoPointCorrelations

open Set
open scoped Classical LSeries.notation

theorem mrt_character_global_prime_tail : ∃ C : ℝ, 0 < C ∧
    ∀ (q : ℕ) [NeZero q], ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 →
    ∀ (t : ℝ) (Y X : ℕ), 1 ≤ Real.log (Y : ℝ) → Y ≤ X →
      (q : ℝ) ^ 2 * mrtCharacterHeight q t ^ 2 ≤ Real.log (Y : ℝ) →
      |(∑ p ∈ primesUpTo X \ primesUpTo Y, characterTwist χ t p / (p : ℂ)).re| ≤ C := by
  obtain ⟨c, C, hc, hC, hstrip⟩ := mrt_character_logderiv_global_bound
  refine ⟨24 + 20 * halaszMertensConstant + C,
    by linarith [halaszMertensConstant_nonneg], ?_⟩
  intro q _ χ hχ t Y X hY hYX hheight
  have hYpos : (0 : ℝ) < Y :=
    zero_lt_one.trans ((Real.log_pos_iff (Nat.cast_nonneg Y)).mp (by linarith))
  have hlog : Real.log (Y : ℝ) ≤ Real.log (X : ℝ) :=
    Real.log_le_log hYpos (by exact_mod_cast hYX)
  have hX : 1 ≤ Real.log (X : ℝ) := hY.trans hlog
  have hLX : 0 < Real.log (X : ℝ) := by linarith
  have hLY : 0 < Real.log (Y : ℝ) := by linarith
  have hh : mrtCharacterHeight q (-t) = mrtCharacterHeight q t := by
    simp [mrtCharacterHeight]
  have hbound : ∀ sigma ∈ Ico (1 + 1 / Real.log (X : ℝ)) (1 + 1 / Real.log (Y : ℝ)),
      ‖logDeriv (L ↗χ) ((sigma : ℂ) - (t : ℂ) * Complex.I)‖ ≤ C * Real.log (Y : ℝ) := by
    intro sigma hsigma
    have hsigma1 : 1 < sigma := by linarith [one_div_pos.mpr hLX, hsigma.1]
    have hsigma2 : sigma ≤ 2 := by
      have hi : 1 / Real.log (Y : ℝ) ≤ 1 := (div_le_iff₀ hLY).mpr (by linarith)
      linarith [hsigma.2]
    have hleft : 1 - c / ((q : ℝ) ^ 2 * mrtCharacterHeight q (-t)) ≤ sigma := by
      have hd : 0 ≤ c / ((q : ℝ) ^ 2 * mrtCharacterHeight q (-t)) :=
        div_nonneg hc.le (mul_nonneg (sq_nonneg (q : ℝ))
          (mrt_character_height_pos q (-t)).le)
      linarith
    have hnorm := (hstrip q χ hχ (-t) sigma hleft hsigma2).2
    rw [hh] at hnorm
    have hpoint : (sigma : ℂ) + Complex.I * ((-t : ℝ) : ℂ) =
        (sigma : ℂ) - (t : ℂ) * Complex.I := by push_cast; ring
    rw [hpoint] at hnorm
    have hs : 1 < ((sigma : ℂ) - (t : ℂ) * Complex.I).re := by simpa using hsigma1
    rw [DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
      DirichletCharacter.LFunction_eq_LSeries χ hs] at hnorm
    have hscale : C * (q : ℝ) ^ 2 * mrtCharacterHeight q t ^ 2 ≤ C * Real.log (Y : ℝ) := by
      calc
        _ = C * ((q : ℝ) ^ 2 * mrtCharacterHeight q t ^ 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hheight hC.le
    exact hnorm.trans hscale
  have hr := mrt_character_LSeries_sigma_ratio χ (NeZero.pos q) t hY hYX hC.le hbound
  have he := mrt_character_prime_tail_LSeries_ratio χ t hY hX hYX
  have ht := abs_add_le
    ((∑ p ∈ primesUpTo X \ primesUpTo Y, characterTwist χ t p / (p : ℂ)).re -
      (Real.log ‖L ↗χ (1 + (1 / Real.log (X : ℝ) : ℝ) - (t : ℂ) * Complex.I)‖ -
        Real.log ‖L ↗χ (1 + (1 / Real.log (Y : ℝ) : ℝ) - (t : ℂ) * Complex.I)‖))
    (Real.log ‖L ↗χ (1 + (1 / Real.log (X : ℝ) : ℝ) - (t : ℂ) * Complex.I)‖ -
      Real.log ‖L ↗χ (1 + (1 / Real.log (Y : ℝ) : ℝ) - (t : ℂ) * Complex.I)‖)
  rw [sub_add_cancel] at ht
  linarith

end TwoPointCorrelations

end OAI
