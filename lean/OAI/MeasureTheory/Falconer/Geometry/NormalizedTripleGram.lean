import OAI.MeasureTheory.Falconer.Estimates.TripleGram

namespace OAI

/-! # Quantitative triple transversality in the bounded unit-direction chart -/

namespace Falconer
variable {n : ℕ}

theorem northLift_norm_le_two {p : Space n} (hp : ‖p‖ ≤ 1) : ‖northLift p‖ ≤ 2 := by
  have he := northLift_norm_sq p
  nlinarith [norm_nonneg p,norm_nonneg (northLift p)]

theorem gnomonic_tripleGram_lower {p q r : Space n}
    (hp : ‖p‖ ≤ 1) (hq : ‖q‖ ≤ 1) (hr : ‖r‖ ≤ 1) :
    (1/64:ℝ)*(‖q-p‖^2*‖r-p‖^2-(inner ℝ (q-p) (r-p))^2) ≤
      tripleGram (gnomonicChart p : Space (n+1)) (gnomonicChart q : Space (n+1))
        (gnomonicChart r : Space (n+1)) := by
  have hinv (x : Space n) (hx : ‖x‖ ≤ 1) : (1/2:ℝ) ≤ ‖northLift x‖⁻¹ := by
    rw [← one_div (‖northLift x‖)]
    apply (div_le_div_iff₀ (by norm_num) (norm_pos_iff.mpr (northLift_ne_zero x))).mpr
    simpa only [one_mul] using northLift_norm_le_two hx
  have hp' := hinv p hp
  have hq' := hinv q hq
  have hr' := hinv r hr
  have hprod : (1/8:ℝ) ≤ ‖northLift p‖⁻¹*‖northLift q‖⁻¹*‖northLift r‖⁻¹ := by
    calc
      _ = (1/2:ℝ)*(1/2)*(1/2) := by norm_num
      _ ≤ _ := by gcongr
  have hsq : (1/64:ℝ) ≤ (‖northLift p‖⁻¹*‖northLift q‖⁻¹*‖northLift r‖⁻¹)^2 := by
    calc
      _ = (1/8:ℝ)^2 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hprod 2
  have hw : 0 ≤ ‖q-p‖^2*‖r-p‖^2-(inner ℝ (q-p) (r-p))^2 := by
    have hc := pow_le_pow_left₀ (abs_nonneg (inner ℝ (q-p) (r-p)))
      (abs_real_inner_le_norm (q-p) (r-p)) 2
    rw [sq_abs,mul_pow] at hc
    exact sub_nonneg.mpr hc
  rw [gnomonic_tripleGram]
  exact mul_le_mul hsq (northLift_tripleGram_lower p q r) hw (sq_nonneg _)

end Falconer

end OAI
