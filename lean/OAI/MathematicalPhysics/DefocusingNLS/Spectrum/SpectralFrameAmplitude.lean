import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBStateFlux

namespace OAI

/-! Terminal normalization bounds the coefficient of a single WKB branch
above and below when its real action is bounded. -/

namespace DefocusingNLS

theorem spectralFrame_amplitude_bounds (k H B : ℝ) (z u : ℂ) (hk : 0 < k)
    (hU : k*‖u‖ = Real.exp H) (hH : |H| ≤ B)
    (hzlo : 1 ≤ k*‖z‖) (hzhi : k*‖z‖ ≤ 2) :
    Real.exp (-B) ≤ ‖z/u‖ ∧ ‖z/u‖ ≤ 2*Real.exp B := by
  have hu : 0 < ‖u‖ := by
    have he := Real.exp_pos H
    nlinarith
  have heq : ‖z/u‖ = (k*‖z‖)*Real.exp (-H) := by
    rw [norm_div,Real.exp_neg]
    apply (div_eq_iff hu.ne').mpr
    field_simp
    nlinarith [hU]
  have hneg : -B ≤ -H := neg_le_neg ((le_abs_self H).trans hH)
  have hpos : -H ≤ B := (neg_le_abs H).trans hH
  rw [heq]
  constructor
  · calc
      _ = 1*Real.exp (-B) := by ring
      _ ≤ (k*‖z‖)*Real.exp (-H) := mul_le_mul hzlo (Real.exp_le_exp.mpr hneg)
        (Real.exp_pos _).le (by positivity)
  · exact mul_le_mul hzhi (Real.exp_le_exp.mpr hpos) (Real.exp_pos _).le (by norm_num)

theorem spectralScalarFlux_smul (z : ℂ) (u : ℂ × ℂ) :
    spectralScalarFlux (z • u) = ‖z‖^2*spectralScalarFlux u := by
  rw [← Complex.normSq_eq_norm_sq]
  simp only [spectralScalarFlux,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,Complex.star_def,
    Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im,Complex.normSq_apply]
  ring

end DefocusingNLS

end OAI
