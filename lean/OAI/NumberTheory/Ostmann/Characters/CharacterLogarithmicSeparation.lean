import OAI.NumberTheory.Ostmann.ZeroDensity.CompletedLogDerivativeSeparated
import OAI.NumberTheory.Ostmann.ZeroDensity.GammaHalfStripBound

namespace OAI

/-! # A conductor-uniform logarithmic derivative estimate

The actual Hadamard difference and the positive reference zero sum control
L'/L throughout the positive half-strip, with the explicit cost of the
separation from all actual zeros.
-/

namespace Ostmann

open Complex

theorem character_logDeriv_logarithmic_separation : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : PrimitiveComplexCharacter) (s : ℂ) (δ : ℝ),
      1 / 2 ≤ s.re → s.re ≤ 2 → 0 < δ →
      (∀ i : ℕ, δ ≤ ‖s - (actualCharacterZeros χ).zeros i‖) →
      ‖logDeriv χ.L s‖ ≤
        C * (Real.log χ.modulus + Real.log (|s.im| + 2) + 1) * (1 + δ⁻¹) := by
  obtain ⟨C0, hC0, hright⟩ := character_logDeriv_right_uniform_bound
  obtain ⟨B0, hB0, hzeros⟩ := exists_character_zero_sum_log_bound
  obtain ⟨B1, hB1, hgamma⟩ := characterGamma_logarithmic_half_strip
  obtain ⟨B2, hB2, hinv⟩ := characterGammaInverse_logarithmic_half_strip
  let D := C0 + B0 + B1 + B2 + 1
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨5 * D, by positivity, ?_⟩
  intro χ s δ hs hs2 hδ hsep
  let w : ℂ := 2 + (s.im : ℂ) * I
  have hw : w.re = 2 := by simp [w]
  have hwi : w.im = s.im := by simp [w]
  have hshift : ‖w - s‖ ≤ 2 := by
    have he : w - s = ((2 - s.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [w]
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  have hdiff := completed_logDeriv_difference_bound χ s w 2 δ
    (by norm_num) hδ hw hshift hsep
  have hcne : χ.completed s ≠ 0 := by
    intro hz
    obtain ⟨i, hi⟩ := actualCharacterZeros_complete χ s ((χ.completed_zero_iff s).mp hz)
    have hh := hsep i
    rw [hi, sub_self, norm_zero] at hh
    linarith
  have hL : χ.L s ≠ 0 := by
    rw [χ.L_eq_completed_mul_all]
    exact mul_ne_zero hcne (χ.gammaInverse_ne_zero s (by linarith))
  have hcw := χ.completed_logDeriv_eq_add w (by linarith)
  have hls := χ.logDeriv_L_eq_completed_add s hL
  have hzsum := hzeros χ w (by linarith) (by linarith)
  have hr := hright χ w hw.ge
  have hgw := hgamma χ w (by linarith) (by linarith)
  have hgs := hinv χ s hs hs2
  rw [hwi] at hzsum hgw
  have hz : characterRealZeroSum χ w ≤
      C0 + (1 / 2) * Real.log χ.modulus + B0 * Real.log (|s.im| + 2) := by
    have hh := (Complex.re_le_norm (logDeriv χ.L w)).trans hr
    linarith
  have hbound : ‖logDeriv χ.L s‖ ≤
      (2 * (1 + 2 / δ)) *
        (C0 + (1 / 2) * Real.log χ.modulus + B0 * Real.log (|s.im| + 2)) +
          C0 + (B1 + B2) * Real.log (|s.im| + 2) := by
    have hc := norm_le_norm_sub_add (logDeriv χ.completed s) (logDeriv χ.completed w)
    have hwbound : ‖logDeriv χ.completed w‖ ≤ C0 + B1 * Real.log (|s.im| + 2) := by
      rw [hcw]
      exact (norm_add_le _ _).trans (add_le_add hr hgw)
    have hsbound : ‖logDeriv χ.L s‖ ≤ ‖logDeriv χ.completed s‖ +
        ‖logDeriv χ.gammaInverse s‖ := by rw [hls]; exact norm_add_le _ _
    have hdiff' := hdiff.trans (mul_le_mul_of_nonneg_left hz (by positivity))
    linarith
  let H := Real.log (|s.im| + 2)
  let L := Real.log χ.modulus + H + 1
  have hq : 0 ≤ Real.log χ.modulus := Real.log_nonneg (by exact_mod_cast χ.positive)
  have hH : 0 ≤ H := Real.log_nonneg (by linarith [abs_nonneg s.im])
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hD0 : C0 ≤ D := by dsimp [D]; linarith
  have hDhalf : 1 / 2 ≤ D := by dsimp [D]; linarith
  have hDB0 : B0 ≤ D := by dsimp [D]; linarith
  have hDB12 : B1 + B2 ≤ D := by dsimp [D]; linarith
  have hbase : C0 + (1 / 2) * Real.log χ.modulus + B0 * H ≤ D * L := by
    have h1 := mul_le_mul_of_nonneg_right hDhalf hq
    have h2 := mul_le_mul_of_nonneg_right hDB0 hH
    dsimp [L]
    nlinarith
  have hrest : C0 + (B1 + B2) * H ≤ D * L := by
    have hh := mul_le_mul_of_nonneg_right hDB12 hH
    have hnon := mul_nonneg hD.le hq
    dsimp [L]
    nlinarith
  have hcost : 2 * (1 + 2 / δ) ≤ 4 * (1 + δ⁻¹) := by
    simp only [div_eq_mul_inv]
    linarith
  have hrest' : D * L ≤ D * L * (1 + δ⁻¹) := by
    have hh := mul_nonneg (mul_nonneg hD.le hLpos.le) (inv_nonneg.mpr hδ.le)
    nlinarith
  calc
    _ ≤ (2 * (1 + 2 / δ)) * (C0 + (1 / 2) * Real.log χ.modulus + B0 * H) +
        (C0 + (B1 + B2) * H) := by simpa only [H, add_assoc] using hbound
    _ ≤ (2 * (1 + 2 / δ)) * (D * L) + D * L :=
      add_le_add (mul_le_mul_of_nonneg_left hbase (by positivity)) hrest
    _ ≤ (4 * (1 + δ⁻¹)) * (D * L) + D * L * (1 + δ⁻¹) :=
      add_le_add (mul_le_mul_of_nonneg_right hcost (by positivity)) hrest'
    _ = _ := by dsimp [L, H]; ring

end Ostmann

end OAI
