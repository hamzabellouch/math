import OAI.MathematicalPhysics.DefocusingNLS.Profile.ProfileDeterminantBound
import OAI.MathematicalPhysics.DefocusingNLS.Profile.ProfileJetError
import OAI.MathematicalPhysics.DefocusingNLS.Profile.ProfileMatchingQuotient

namespace OAI

/-! Propagation of the strict tail disk to the actual free-profile quotient. -/

open Matrix
namespace DefocusingNLS.ProfileCertificate

attribute [local irreducible] profileProduct normalizedMatchingB normalizedMatchingC

theorem normalized_profile_determinant_bound (b z : ℝ)
    (hb : |b| ≤ (radius : ℝ)) :
    ‖Matrix.det (normalizedProfile b z)‖ < (62/10000000000000 : ℝ) := by
  have hm : normalizedProfile b z =
      centralM⁻¹ • profileProduct ((centerB : ℝ)+b) ((centerZ : ℝ)+z) 34 := by
    ext i j
    simp only [normalizedProfile, Matrix.smul_apply, smul_eq_mul, div_eq_mul_inv]
    ring
  rw [hm, Matrix.det_smul, Fintype.card_fin, norm_mul, norm_pow, norm_inv]
  have h := actual_profile_determinant_bound b z hb
  change ‖(profileProduct ((centerB : ℝ)+b) ((centerZ : ℝ)+z) 34).det‖ <
    (62/10000000000000 : ℝ)*‖centralM‖^2 at h
  have hn : 0 < ‖centralM‖^2 := pow_pos (norm_pos_iff.mpr centralM_ne_zero) _
  have hd := (div_lt_iff₀ hn).mpr h
  convert! hd using 1
  simp only [div_eq_mul_inv, inv_pow]
  ring

theorem actual_tail_error (b z : ℝ)
    (hb : |b| ≤ (radius : ℝ)) (hz : |z| ≤ (radius : ℝ)) :
    ‖freeProfileJ ((centerB : ℝ)+b) ((centerZ : ℝ)+z)-
      normalizedProfile b z 1 1/normalizedProfile b z 0 1‖ < (tailError : ℝ) := by
  let q : ℂ := -Complex.I*(((centerB : ℝ)+b : ℝ) : ℂ)
  let s : ℂ := Complex.I*(((centerZ : ℝ)+z : ℝ) : ℂ)
  let r := normalizedMatchingB q 6 s 34/normalizedMatchingC q 6 s 34
  have hδ : 0 ≤ (radius : ℝ) := by norm_num [radius]
  have hZ : 0 < (centerZ : ℝ)+z := by
    have hz' := (abs_le.mp hz).1
    norm_num [centerZ, radius] at hz' ⊢
    linarith
  have hsn : ‖s/5‖ = ((centerZ : ℝ)+z)/5 := by
    simp only [s, norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_ofNat, abs_of_pos hZ]
  have hr : ‖r+s/5‖ ≤ ((centerZ : ℝ)+z)/5 := (profile_tail_disk b z hz).2
  have hru : ‖r‖ ≤ 2*((centerZ : ℝ)+(radius : ℝ))/5 := by
    have ht : ‖r‖ ≤ ‖r+s/5‖+‖s/5‖ := by
      calc
        _ = ‖(r+s/5)-s/5‖ := by rw [add_sub_cancel_right]
        _ ≤ _ := norm_sub_le _ _
    rw [hsn] at ht
    linarith [(abs_le.mp hz).2]
  have hgap := normalized_denominator_gap b z hb hz
  simp only [← Complex.ofReal_add] at hgap
  have hden := matched_denominator_lower (normalizedProfile b z) r (s/5)
    (((centerZ : ℝ)+z)/5) hr
  have hd : (6/10 : ℝ) ≤ ‖normalizedProfile b z 0 0*r+normalizedProfile b z 0 1‖ := by
    dsimp only [s] at hden
    linarith
  have hχ : 0 < 1-(changeBound : ℝ) := by norm_num [changeBound, radius]
  have ht := matched_quotient_bound (normalizedProfile b z) r
    (1-(changeBound : ℝ)) (6/10) hχ (by norm_num)
    (normalized_first_denominator_lower b z hb hz) hd
  rw [freeProfileJ_eq_matched b z hz]
  change ‖(normalizedProfile b z 1 0*r+normalizedProfile b z 1 1)/
    (normalizedProfile b z 0 0*r+normalizedProfile b z 0 1)-
      normalizedProfile b z 1 1/normalizedProfile b z 0 1‖ < _
  apply ht.trans_lt
  have hdet := normalized_profile_determinant_bound b z hb
  have hu : 0 < 2*((centerZ : ℝ)+(radius : ℝ))/5 := by norm_num [centerZ, radius]
  have hm : ‖r‖*‖Matrix.det (normalizedProfile b z)‖ <
      (2*((centerZ : ℝ)+(radius : ℝ))/5)*(62/10000000000000) :=
    (mul_le_mul_of_nonneg_right hru (norm_nonneg _)).trans_lt
      (mul_lt_mul_of_pos_left hdet hu)
  have hquot := (div_lt_div_iff_of_pos_right (mul_pos hχ (by norm_num : (0 : ℝ)<6/10))).mpr hm
  convert! hquot using 1
  unfold tailError
  push_cast
  ring

/-- The certified small error applies to the genuine logarithmic derivative. -/
theorem free_profile_linear_error (b z : ℝ)
    (hb : |b| ≤ (radius : ℝ)) (hz : |z| ≤ (radius : ℝ)) :
    ‖freeProfileJ ((centerB : ℝ)+b) ((centerZ : ℝ)+z)-
      ((b : ℂ)*centralX+(z : ℂ)*centralY)‖ < (25/1000000000000 : ℝ) := by
  have ht := actual_tail_error b z hb hz
  have hj := normalized_zero_tail_error b z hb hz
  have hsum := (Rat.cast_lt (K := ℝ)).mpr propagation_comparisons.2.2.1
  push_cast at hsum
  calc
    _ = ‖(freeProfileJ ((centerB : ℝ)+b) ((centerZ : ℝ)+z)-
        normalizedProfile b z 1 1/normalizedProfile b z 0 1)+
      (normalizedProfile b z 1 1/normalizedProfile b z 0 1-
        ((b : ℂ)*centralX+(z : ℂ)*centralY))‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _
    _ < (tailError : ℝ)+(jetError : ℝ) := add_lt_add_of_lt_of_le ht hj
    _ < _ := by linarith

end DefocusingNLS.ProfileCertificate

end OAI
