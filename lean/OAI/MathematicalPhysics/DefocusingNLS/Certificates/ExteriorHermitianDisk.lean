import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ForwardHermitianForm

namespace OAI

/-! Completing the exterior Hermitian form gives its exact quotient disk. -/

namespace DefocusingNLS

theorem hermitianPairForm_last_square (a d : ℝ) (c u v : ℂ) :
    d*hermitianPairForm a d c u v =
      Complex.normSq ((d : ℂ)*v+star c*u)+
        (a*d-Complex.normSq c)*Complex.normSq u := by
  simp only [hermitianPairForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,
    Complex.add_re,Complex.add_im,Complex.star_def,Complex.conj_re,Complex.conj_im,
    Complex.ofReal_re,Complex.ofReal_im]
  ring

theorem hermitianPairForm_first_ne_zero (a d : ℝ) (c u v : ℂ)
    (hd : 0 < d) (hform : hermitianPairForm a d c u v ≤ 0)
    (huv : u ≠ 0 ∨ v ≠ 0) : u ≠ 0 := by
  intro hu
  have hv := huv.resolve_left (not_not.mpr hu)
  rw [hu] at hform
  simp only [hermitianPairForm,Complex.normSq_zero,mul_zero,star_zero,zero_mul,
    Complex.zero_re,add_zero,zero_add] at hform
  exact (mul_pos hd (Complex.normSq_pos.mpr hv)).not_ge hform

theorem hermitianPairForm_quotient_disk (a d R : ℝ) (c u v : ℂ)
    (hd : 0 < d) (hR : 0 ≤ R) (hu : u ≠ 0)
    (hform : hermitianPairForm a d c u v ≤ 0)
    (hdet : a*d-Complex.normSq c = -R^2) :
    ‖v/u+star c/(d : ℂ)‖ ≤ R/d := by
  let r := v/u+star c/(d : ℂ)
  have hd0 : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
  have he : (d : ℂ)*u*r = (d : ℂ)*v+star c*u := by
    dsimp only [r]
    field_simp [hu,hd0]
  have hsq : Complex.normSq ((d : ℂ)*v+star c*u) ≤ R^2*Complex.normSq u := by
    have h := hermitianPairForm_last_square a d c u v
    rw [hdet] at h
    have hs := mul_nonpos_of_nonneg_of_nonpos hd.le hform
    nlinarith
  rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq] at hsq
  have hnorm : ‖(d : ℂ)*v+star c*u‖ ≤ R*‖u‖ := by
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hR (norm_nonneg _))).mp (by nlinarith)
  rw [← he,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hd] at hnorm
  have hu0 : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hm : d*‖r‖ ≤ R := by
    apply (mul_le_mul_iff_left₀ hu0).mp
    nlinarith
  exact (le_div_iff₀ hd).mpr (by nlinarith)

end DefocusingNLS

end OAI
