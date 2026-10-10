import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalParameter
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCanonicalParameterExpansion

namespace OAI

/-! Explicit logarithmic value and slope bounds for the differentiated
physical outgoing columns. -/

namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem circularParameterShear_norm (t : ℝ) (ht : 0 ≤ t) (Y D : E₄)
    (A B : ℝ) (hY : ‖Y‖ ≤ A) (hD : ‖D‖ ≤ B) :
    ‖circularParameterShear t Y D‖ ≤ B + (2 * t + 2) * A := by
  let V : E₄ := ((0, Y.1.1), (0, Y.2.1))
  have hV : ‖V‖ ≤ ‖Y‖ := by
    change max (max ‖(0 : ℂ)‖ ‖Y.1.1‖) (max ‖(0 : ℂ)‖ ‖Y.2.1‖) ≤ ‖Y‖
    rw [norm_zero, max_eq_right (norm_nonneg _), max_eq_right (norm_nonneg _)]
    exact max_le ((norm_fst_le Y.1).trans (norm_fst_le Y))
      ((norm_fst_le Y.2).trans (norm_snd_le Y))
  have he : (((0 : ℂ), 2 * Y.1.1), ((0 : ℂ), 2 * Y.2.1)) = (2 : ℂ) • V := by
    apply Prod.ext <;> apply Prod.ext <;> simp [V, smul_eq_mul]
  have hE : ‖(((0 : ℂ), 2 * Y.1.1), ((0 : ℂ), 2 * Y.2.1))‖ ≤ 2 * A := by
    calc
      _ = 2 * ‖V‖ := by rw [he, norm_smul]; norm_num
      _ ≤ 2 * A := mul_le_mul_of_nonneg_left (hV.trans hY) (by norm_num)
  have hα : ‖2 * (t : ℂ)‖ = 2 * t := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
    norm_num
  calc
    ‖circularParameterShear t Y D‖ ≤ ‖D‖ + ‖(2 * (t : ℂ)) • Y‖ +
        ‖(((0 : ℂ), 2 * Y.1.1), ((0 : ℂ), 2 * Y.2.1))‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ = ‖D‖ + 2 * t * ‖Y‖ + ‖(((0 : ℂ), 2 * Y.1.1), ((0 : ℂ), 2 * Y.2.1))‖ := by
      rw [norm_smul, hα]
    _ ≤ B + 2 * t * A + 2 * A :=
      add_le_add (add_le_add hD (mul_le_mul_of_nonneg_left hY (by positivity))) hE
    _ = B + (2 * t + 2) * A := by ring

theorem spectralPhysicalParameter_value_slope_bound (νp νm : ℂ)
    (Y D : ℝ → E₄) (r A B : ℝ) (hr : 1 ≤ r)
    (hY : ‖Y (Real.log r)‖ ≤ A) (hD : ‖D (Real.log r)‖ ≤ B) :
    let V := spectralPhysicalPair νp νm (fun t => circularParameterShear t (Y t) (D t)) r
    let C := B + (2 * Real.log r + 2) * A
    (‖V.1.1‖ ≤ r ^ νp.re * C ∧ ‖V.1.2‖ ≤ r ^ (νp.re - 1) * (‖νp‖ + 1) * C) ∧
      (‖V.2.1‖ ≤ r ^ νm.re * C ∧ ‖V.2.2‖ ≤ r ^ (νm.re - 1) * (‖νm‖ + 1) * C) := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hs := circularParameterShear_norm (Real.log r) (Real.log_nonneg hr)
    (Y (Real.log r)) (D (Real.log r)) A B hY hD
  exact ⟨spectralPhysicalJet_bounds νp _ _ r hr0 ((norm_fst_le _).trans hs),
    spectralPhysicalJet_bounds νm _ _ r hr0 ((norm_snd_le _).trans hs)⟩

end DefocusingNLS

end OAI
