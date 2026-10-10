import OAI.MathematicalPhysics.DefocusingNLS.Profile.ProfileNormalizedBounds

namespace OAI

/-! The zero-tail quotient has the certified linear approximation. -/

namespace DefocusingNLS.ProfileCertificate

private theorem ratio_error (d b l : ℂ) (η χ S : ℝ)
    (hη : 0 ≤ η) (hχ : 0 ≤ χ) (hχ1 : χ < 1) (hS : 0 ≤ S)
    (hd : ‖d-l‖ ≤ η) (hb : ‖b-1‖ ≤ χ) (hl : ‖l‖ ≤ S) :
    ‖d/b-l‖ ≤ (η+S*χ)/(1-χ) := by
  have hnorm : 1-χ ≤ ‖b‖ := by
    have hn := norm_sub_norm_le (1 : ℂ) b
    rw [norm_one, norm_sub_rev] at hn
    linarith
  have hden : 0 < 1-χ := sub_pos.mpr hχ1
  have hb0 : b ≠ 0 := norm_pos_iff.mp (hden.trans_le hnorm)
  have he : d/b-l = (d-l+l*(1-b))/b := by field_simp [hb0]; ring
  rw [he, norm_div]
  have hnum : ‖d-l+l*(1-b)‖ ≤ η+S*χ := by
    apply (norm_add_le _ _).trans
    rw [norm_mul, norm_sub_rev (1 : ℂ) b]
    exact add_le_add hd (mul_le_mul hl hb (norm_nonneg _) hS)
  exact (div_le_div_of_nonneg_right hnum (norm_nonneg _)).trans
    (div_le_div_of_nonneg_left (by positivity) hden hnorm)

theorem normalized_first_denominator_lower (b z : ℝ)
    (hb : |b| ≤ (radius : ℝ)) (hz : |z| ≤ (radius : ℝ)) :
    1-(changeBound : ℝ) ≤ ‖normalizedProfile b z 0 1‖ := by
  have h := normalizedProfile_variation b z hb hz 0 1
  rw [centralNormalized_zero_one] at h
  have hn := norm_sub_norm_le (1 : ℂ) (normalizedProfile b z 0 1)
  rw [norm_one, norm_sub_rev] at hn
  linarith

theorem normalized_first_entry_ne_zero (b z : ℝ)
    (hb : |b| ≤ (radius : ℝ)) (hz : |z| ≤ (radius : ℝ)) :
    normalizedProfile b z 0 1 ≠ 0 := by
  apply norm_pos_iff.mp
  have hχ : (changeBound : ℝ) < 1 := by norm_num [changeBound, radius]
  linarith [normalized_first_denominator_lower b z hb hz]

theorem normalized_zero_tail_error (b z : ℝ)
    (hb : |b| ≤ (radius : ℝ)) (hz : |z| ≤ (radius : ℝ)) :
    ‖normalizedProfile b z 1 1/normalizedProfile b z 0 1-
      ((b : ℂ)*centralX+(z : ℂ)*centralY)‖ ≤ (jetError : ℝ) := by
  have h := ratio_error (normalizedProfile b z 1 1) (normalizedProfile b z 0 1)
    ((b : ℂ)*centralX+(z : ℂ)*centralY)
    ((1/1000000000000 : ℝ)+50000*(radius : ℝ)^2) (changeBound : ℝ)
    ((283/1000 : ℝ)*(radius : ℝ))
    (by positivity) (by norm_num [changeBound, radius]) (by norm_num [changeBound, radius])
    (by norm_num [radius]) (normalizedProfile_last_remainder b z hb hz).le
    (by simpa only [centralNormalized_zero_one] using (normalizedProfile_variation b z hb hz 0 1).le)
    (free_linear_size b z hb hz)
  convert! h using 1
  unfold jetError
  push_cast
  ring

end DefocusingNLS.ProfileCertificate

end OAI
