import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBSqrtApproximation

namespace OAI

/-! Conversion from complex momentum to the positive real frequency. -/

namespace DefocusingNLS

theorem spectralPositiveMomentum_ratio_error (x gamma eps : ℝ) (z : ℂ)
    (hx : 0 < x) (hgamma : |gamma| ≤ x) (heps : 0 ≤ eps)
    (hz : ‖z/Complex.sqrt ((x : ℂ)+Complex.I*(gamma : ℂ))+Complex.I‖ ≤ eps) :
    ‖z/(Real.sqrt x : ℂ)+Complex.I‖ ≤ 2*eps+|gamma|/x := by
  let s := Real.sqrt x
  let p := Complex.sqrt ((x : ℂ)+Complex.I*(gamma : ℂ))
  have hs : 0 < s := Real.sqrt_pos.mpr hx
  have hs2 : s^2 = x := Real.sq_sqrt hx.le
  have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hp : p ≠ 0 := spectralComplexSqrt_ne_zero _ (by
    intro h
    have hh := congrArg Complex.re h
    simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,
      Complex.I_im,Complex.ofReal_im,zero_mul,mul_zero,sub_self,add_zero,Complex.zero_re] at hh
    exact hx.ne' hh)
  have happrox : ‖p-(s : ℂ)‖ ≤ |gamma|/s := spectralComplexSqrt_approx x gamma hx
  have hnorms : ‖(s : ℂ)‖ = s := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hs]
  have hquot : |gamma|/s ≤ s := (div_le_iff₀ hs).mpr (by nlinarith)
  have hpn : ‖p‖ ≤ 2*s := by
    have hh := norm_add_le (p-(s : ℂ)) (s : ℂ)
    rw [sub_add_cancel,hnorms] at hh
    linarith
  have hdecomp : z/(s : ℂ)+Complex.I =
      (z/p+Complex.I)*(p/(s : ℂ))+Complex.I*((s : ℂ)-p)/(s : ℂ) := by
    field_simp
    ring
  rw [hdecomp]
  calc
    _ ≤ ‖(z/p+Complex.I)*(p/(s : ℂ))‖+‖Complex.I*((s : ℂ)-p)/(s : ℂ)‖ := norm_add_le _ _
    _ = ‖z/p+Complex.I‖*(‖p‖/s)+‖p-(s : ℂ)‖/s := by
      rw [norm_mul,norm_div,norm_div,norm_mul,Complex.norm_I,one_mul,hnorms,norm_sub_rev (s : ℂ)]
    _ ≤ eps*(2*s/s)+(|gamma|/s)/s := by
      apply add_le_add
      · exact mul_le_mul hz (div_le_div_of_nonneg_right hpn hs.le) (by positivity) heps
      · exact div_le_div_of_nonneg_right happrox hs.le
    _ = 2*eps+|gamma|/x := by
      rw [← hs2]
      field_simp

end DefocusingNLS

end OAI
