import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingPhysicalTermDerivative

namespace OAI

/-! # A physical-space bound for the transport and Schrödinger mode rate -/

open scoped RealInnerProductSpace

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def physicalModeRate (a b R : ℝ) (n : frequencyLattice) (y : E) : ℂ :=
  (-(a : ℂ) + Complex.I * b) - Complex.I * (((‖n‖ / R) ^ 2 : ℝ) : ℂ) +
    ((-R⁻¹ / 2 * ⟪y, (n : E)⟫ : ℝ) : ℂ) * Complex.I

theorem physicalModeRate_norm_le (a b R : ℝ) (hR : 0 < R) (n : frequencyLattice) (y : E) :
    ‖physicalModeRate a b R n y‖ ≤
      (|a| + |b| + 1 + ‖y‖ / 2) * (1 + (‖n‖ / R) ^ 2) := by
  let r := ‖n‖ / R
  have hr : 0 ≤ r := div_nonneg (norm_nonneg _) hR.le
  have hinner : |⟪y, (n : E)⟫| ≤ ‖y‖ * ‖n‖ := abs_real_inner_le_norm _ _
  have hdrift : ‖((-R⁻¹ / 2 * ⟪y, (n : E)⟫ : ℝ) : ℂ) * Complex.I‖ ≤ (‖y‖ / 2) * r := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_mul, abs_div, abs_neg, abs_inv, abs_of_pos hR]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hm := mul_le_mul_of_nonneg_left hinner (show 0 ≤ R⁻¹ / 2 by positivity)
    calc
      _ ≤ (R⁻¹ / 2) * (‖y‖ * ‖n‖) := hm
      _ = _ := by dsimp [r]; ring
  have hbase : ‖(-(a : ℂ) + Complex.I * b) - Complex.I * (((‖n‖ / R) ^ 2 : ℝ) : ℂ)‖ ≤
      |a| + |b| + r ^ 2 := by
    calc
      _ ≤ ‖-(a : ℂ) + Complex.I * b‖ + ‖Complex.I * (((‖n‖ / R) ^ 2 : ℝ) : ℂ)‖ := norm_sub_le _ _
      _ ≤ (‖-(a : ℂ)‖ + ‖Complex.I * b‖) + ‖Complex.I * (((‖n‖ / R) ^ 2 : ℝ) : ℂ)‖ := by gcongr; exact norm_add_le _ _
      _ = _ := by simp only [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_I, one_mul, abs_of_nonneg (sq_nonneg (‖n‖ / R))]; rfl
  have htotal := (norm_add_le
    ((-(a : ℂ) + Complex.I * b) - Complex.I * (((‖n‖ / R) ^ 2 : ℝ) : ℂ))
    (((-R⁻¹ / 2 * ⟪y, (n : E)⟫ : ℝ) : ℂ) * Complex.I)).trans (add_le_add hbase hdrift)
  have hr1 : r ≤ 1 + r ^ 2 := by nlinarith [sq_nonneg (r - 1)]
  have hm := mul_le_mul_of_nonneg_left hr1 (show 0 ≤ ‖y‖ / 2 by positivity)
  have hp := mul_nonneg (show 0 ≤ |a| + |b| by positivity) (sq_nonneg r)
  change ‖physicalModeRate a b R n y‖ ≤ _ at htotal
  change ‖physicalModeRate a b R n y‖ ≤ (|a| + |b| + 1 + ‖y‖ / 2) * (1 + r ^ 2)
  nlinarith

end DefocusingNLS

end OAI
