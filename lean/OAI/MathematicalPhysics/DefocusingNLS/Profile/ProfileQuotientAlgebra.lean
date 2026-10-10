import OAI.MathematicalPhysics.DefocusingNLS.Profile.ProfileMatrixProduct

namespace OAI

/-! Denominator and quotient estimates used by the free profile certificate. -/

open Matrix
namespace DefocusingNLS.ProfileCertificate

/-- The tail disk turns a finite matrix gap into a lower bound for the
first component of the matched column. -/
theorem matched_denominator_lower (A : Matrix (Fin 2) (Fin 2) ℂ)
    (r s : ℂ) (ρ : ℝ) (hr : ‖r+s‖ ≤ ρ) :
    ‖A 0 1-s*A 0 0‖-ρ*‖A 0 0‖ ≤ ‖A 0 0*r+A 0 1‖ := by
  have he : A 0 1-s*A 0 0 =
      (A 0 0*r+A 0 1)-A 0 0*(r+s) := by ring
  have h := norm_sub_le (A 0 0*r+A 0 1) (A 0 0*(r+s))
  rw [← he, norm_mul] at h
  have hm := mul_le_mul_of_nonneg_left hr (norm_nonneg (A 0 0))
  nlinarith

theorem matched_denominator_ne_zero (A : Matrix (Fin 2) (Fin 2) ℂ)
    (r s : ℂ) (ρ : ℝ) (hr : ‖r+s‖ ≤ ρ)
    (hgap : ρ*‖A 0 0‖ < ‖A 0 1-s*A 0 0‖) : A 0 0*r+A 0 1 ≠ 0 := by
  have h := matched_denominator_lower A r s ρ hr
  intro hz
  rw [hz, norm_zero] at h
  linarith

/-- The only change from the zero-tail quotient is a determinant term. -/
theorem matched_quotient_identity (A : Matrix (Fin 2) (Fin 2) ℂ) (r : ℂ)
    (hb : A 0 1 ≠ 0) (hd : A 0 0*r+A 0 1 ≠ 0) :
    (A 1 0*r+A 1 1)/(A 0 0*r+A 0 1)-A 1 1/A 0 1 =
      -(r*A.det)/(A 0 1*(A 0 0*r+A 0 1)) := by
  rw [div_sub_div _ _ hd hb, mul_comm (A 0 0*r+A 0 1) (A 0 1)]
  congr 1
  rw [Matrix.det_fin_two]
  ring

/-- Quantitative version after lower bounds for both denominators are known. -/
theorem matched_quotient_bound (A : Matrix (Fin 2) (Fin 2) ℂ) (r : ℂ)
    (B D : ℝ) (hB : 0 < B) (hD : 0 < D)
    (hb : B ≤ ‖A 0 1‖) (hd : D ≤ ‖A 0 0*r+A 0 1‖) :
    ‖(A 1 0*r+A 1 1)/(A 0 0*r+A 0 1)-A 1 1/A 0 1‖ ≤
      ‖r‖*‖A.det‖/(B*D) := by
  have hb0 : A 0 1 ≠ 0 := norm_pos_iff.mp (hB.trans_le hb)
  have hd0 : A 0 0*r+A 0 1 ≠ 0 := norm_pos_iff.mp (hD.trans_le hd)
  rw [matched_quotient_identity A r hb0 hd0, norm_div, norm_neg, norm_mul, norm_mul]
  exact div_le_div_of_nonneg_left (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (mul_pos hB hD) (mul_le_mul hb hd (le_of_lt hD) (norm_nonneg _))

end DefocusingNLS.ProfileCertificate

end OAI
