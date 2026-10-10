import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWeakVKDerivative
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterLogDerivative

namespace OAI

/-! The weak VK derivative estimate implies a uniform finite prime-tail
bound. Both the sigma-segment width and height budget are retained. -/

namespace TwoPointCorrelations

open Set
open scoped Classical LSeries.notation

theorem MRTWeakHurwitzGrowthInput.prime_tail (h : MRTWeakHurwitzGrowthInput) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧
    ∀ (q : ℕ) [NeZero q], ∀ (χ : DirichletCharacter ℂ q),
    ∀ (t : ℝ) (Y X : ℕ), 1 ≤ Real.log (Y : ℝ) → Y ≤ X → T ≤ |t| →
      1 / Real.log (Y : ℝ) ≤ mrtVKRadius (2 * t) / 16 →
      (mrtVKWeight q (2 * t)) ^ 2 * (mrtVKLog (2 * t)) ^ (2 / 3 : ℝ) ≤ Real.log (Y : ℝ) →
      |(∑ p ∈ primesUpTo X \ primesUpTo Y, characterTwist χ t p / (p : ℂ)).re| ≤ C := by
  obtain ⟨C, T, hC, hT, hbound⟩ := h.logderiv
  refine ⟨24 + 20 * halaszMertensConstant + C, T,
    by linarith [halaszMertensConstant_nonneg], hT, ?_⟩
  intro q _ χ t Y X hY hYX ht hwidth hcost
  have hYpos : (0 : ℝ) < Y :=
    zero_lt_one.trans ((Real.log_pos_iff (Nat.cast_nonneg Y)).mp (by linarith))
  have hlog : Real.log (Y : ℝ) ≤ Real.log (X : ℝ) :=
    Real.log_le_log hYpos (by exact_mod_cast hYX)
  have hX : 1 ≤ Real.log (X : ℝ) := hY.trans hlog
  have hLX : 0 < Real.log (X : ℝ) := by linarith
  have hHneg : mrtVKLog (2 * -t) = mrtVKLog (2 * t) := by
    unfold mrtVKLog
    rw [mul_neg, abs_neg]
  have hRneg : mrtVKRadius (2 * -t) = mrtVKRadius (2 * t) := by
    unfold mrtVKRadius
    rw [hHneg]
  have hWneg : mrtVKWeight q (2 * -t) = mrtVKWeight q (2 * t) := by
    unfold mrtVKWeight
    rw [hHneg]
  have hb : ∀ sigma ∈ Ico (1 + 1 / Real.log (X : ℝ)) (1 + 1 / Real.log (Y : ℝ)),
      ‖logDeriv (L ↗χ) ((sigma : ℂ) - (t : ℂ) * Complex.I)‖ ≤ C * Real.log (Y : ℝ) := by
    intro sigma hsigma
    have hσ : 1 < sigma := by linarith [one_div_pos.mpr hLX, hsigma.1]
    have hσr : sigma ≤ 1 + mrtVKRadius (2 * -t) / 16 := by
      rw [hRneg]
      linarith [hsigma.2]
    have hh := hbound q χ (-t) sigma (by simpa using ht) hσ hσr
    rw [hHneg, hWneg] at hh
    have hpoint : (sigma : ℂ) + Complex.I * ((-t : ℝ) : ℂ) =
        (sigma : ℂ) - (t : ℂ) * Complex.I := by push_cast; ring
    rw [hpoint] at hh
    have hs : 1 < ((sigma : ℂ) - (t : ℂ) * Complex.I).re := by simpa using hσ
    rw [DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
      DirichletCharacter.LFunction_eq_LSeries χ hs] at hh
    apply hh.trans
    calc
      _ = C * ((mrtVKWeight q (2 * t)) ^ 2 * (mrtVKLog (2 * t)) ^ (2 / 3 : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcost hC.le
  have hr := mrt_character_LSeries_sigma_ratio χ (NeZero.pos q) t hY hYX hC.le hb
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
