import OAI.Geometry.SurfaceImmersion.Correction.CorrectionErrorEnvelope

namespace OAI

/-! The actual normalized one-step error has the six powers in the
correction table, with linear dependence on both input bounds. -/
noncomputable section

namespace ClosedSurfaceR4.ExactCorrection

theorem normalized_step_envelope {t k B C D E U T : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hk : 10 ≤ k)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hE : 0 ≤ E) (hU : 0 ≤ U) (hT : 0 ≤ T) :
    ((t ^ ((6/5 : ℝ)*(k+1))) ^ (2 : ℕ))⁻¹ *
      (((t^k)^(2 : ℕ) + E*U*t^k) * D *
        (B*(t^(11/10 : ℝ)/t)^(40*(k+1)) + C*(t^(6/5 : ℝ)/t)^(40*(k+1))) +
        T*(t^k*(t^(6/5 : ℝ)/t^(11/10 : ℝ))^(40*(k+1)) + (t^k)^(3 : ℕ)/t^(6/5 : ℝ))) ≤
      (D+E*U*D+2*T)*(1+B+C)*t^(1/5 : ℝ) := by
  have he : ((t ^ ((6/5 : ℝ)*(k+1))) ^ (2 : ℕ))⁻¹ *
      (((t^k)^(2 : ℕ) + E*U*t^k) * D *
        (B*(t^(11/10 : ℝ)/t)^(40*(k+1)) + C*(t^(6/5 : ℝ)/t)^(40*(k+1))) +
        T*(t^k*(t^(6/5 : ℝ)/t^(11/10 : ℝ))^(40*(k+1)) + (t^k)^(3 : ℕ)/t^(6/5 : ℝ))) =
      D * (B * (((t^k)^(2 : ℕ)*(t^(11/10 : ℝ)/t)^(40*(k+1))) /
          (t^((6/5 : ℝ)*(k+1)))^(2 : ℕ)) +
        C * (((t^k)^(2 : ℕ)*(t^(6/5 : ℝ)/t)^(40*(k+1))) /
          (t^((6/5 : ℝ)*(k+1)))^(2 : ℕ))) +
      T * ((t^k*(t^(6/5 : ℝ)/t^(11/10 : ℝ))^(40*(k+1))) /
          (t^((6/5 : ℝ)*(k+1)))^(2 : ℕ) +
        ((t^k)^(3 : ℕ)/t^(6/5 : ℝ)) /(t^((6/5 : ℝ)*(k+1)))^(2 : ℕ)) +
      (E*U*D) * (B * ((t^k*(t^(11/10 : ℝ)/t)^(40*(k+1))) /
          (t^((6/5 : ℝ)*(k+1)))^(2 : ℕ)) +
        C * ((t^k*(t^(6/5 : ℝ)/t)^(40*(k+1))) /
          (t^((6/5 : ℝ)*(k+1)))^(2 : ℕ))) := by ring
  rw [he,(normalized_defect_tail_scales ht k).1,(normalized_defect_tail_scales ht k).2,
    normalized_mode_scale ht k,normalized_cubic_scale ht k,
    (normalized_cross_tail_scales ht k).1,(normalized_cross_tail_scales ht k).2]
  calc
    _ ≤ (D+2*T+E*U*D)*(1+B+C)*t^(1/5 : ℝ) :=
      normalized_error_envelope ht ht1 hk hB hC hD hT (mul_nonneg (mul_nonneg hE hU) hD)
    _ = _ := by ring

/-- The same estimate with the integer smoothing order used by the
scheduled correction sequence. -/
theorem normalized_step_envelope_nat {t B C D E U T : ℝ} {k : ℕ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hk : 10 ≤ k)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hE : 0 ≤ E) (hU : 0 ≤ U) (hT : 0 ≤ T) :
    ((t ^ ((6/5 : ℝ)*((k : ℝ)+1))) ^ (2 : ℕ))⁻¹ *
      (((t^(k : ℝ))^(2 : ℕ) + E*U*t^(k : ℝ)) * D *
        (B*(t^(11/10 : ℝ)/t)^(40*(k+1)) + C*(t^(6/5 : ℝ)/t)^(40*(k+1))) +
        T*(t^(k : ℝ)*(t^(6/5 : ℝ)/t^(11/10 : ℝ))^(40*(k+1)) +
          (t^(k : ℝ))^(3 : ℕ)/t^(6/5 : ℝ))) ≤
      (D+E*U*D+2*T)*(1+B+C)*t^(1/5 : ℝ) := by
  have hk' : (10 : ℝ) ≤ k := by exact_mod_cast hk
  have h := normalized_step_envelope ht ht1 hk' hB hC hD hE hU hT
  simpa only [← Real.rpow_natCast, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using h

/-- The actual finite-mode residual has one extra power of the frequency
ratio, which only improves the same normalized envelope. -/
theorem normalized_step_envelope_nat_succ {t B C D E U T : ℝ} {k : ℕ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hk : 10 ≤ k)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hE : 0 ≤ E) (hU : 0 ≤ U) (hT : 0 ≤ T) :
    ((t ^ ((6/5 : ℝ)*((k : ℝ)+1))) ^ (2 : ℕ))⁻¹ *
      (((t^(k : ℝ))^(2 : ℕ) + E*U*t^(k : ℝ)) * D *
        (B*(t^(11/10 : ℝ)/t)^(40*(k+1)) + C*(t^(6/5 : ℝ)/t)^(40*(k+1))) +
        T*(t^(k : ℝ)*(t^(6/5 : ℝ)/t^(11/10 : ℝ))^(40*(k+1)+1) +
          (t^(k : ℝ))^(3 : ℕ)/t^(6/5 : ℝ))) ≤
      (D+E*U*D+2*T)*(1+B+C)*t^(1/5 : ℝ) := by
  have hs : 0 < t^(11/10 : ℝ) := Real.rpow_pos_of_pos ht _
  have hratio : 0 ≤ t^(6/5 : ℝ)/t^(11/10 : ℝ) :=
    div_nonneg (Real.rpow_nonneg ht.le _) hs.le
  have hratio1 : t^(6/5 : ℝ)/t^(11/10 : ℝ) ≤ 1 := by
    apply (div_le_one hs).mpr
    exact Real.rpow_le_rpow_of_exponent_ge ht ht1 (by norm_num)
  have hp := pow_le_pow_of_le_one hratio hratio1 (Nat.le_succ (40*(k+1)))
  calc
    _ ≤ ((t ^ ((6/5 : ℝ)*((k : ℝ)+1))) ^ (2 : ℕ))⁻¹ *
        (((t^(k : ℝ))^(2 : ℕ) + E*U*t^(k : ℝ)) * D *
          (B*(t^(11/10 : ℝ)/t)^(40*(k+1)) + C*(t^(6/5 : ℝ)/t)^(40*(k+1))) +
          T*(t^(k : ℝ)*(t^(6/5 : ℝ)/t^(11/10 : ℝ))^(40*(k+1)) +
            (t^(k : ℝ))^(3 : ℕ)/t^(6/5 : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (sq_nonneg _))
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ hT
      exact add_le_add (mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg ht.le _)) le_rfl
    _ ≤ _ := normalized_step_envelope_nat ht ht1 hk hB hC hD hE hU hT

end ClosedSurfaceR4.ExactCorrection

end

end OAI
