import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBFrame
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralShellNorm

namespace OAI

/-! The normalized WKB frame is uniformly bounded in the scalar transfer norm. -/

namespace DefocusingNLS

theorem spectralWKB_amplitude_norm (p a : ℂ) (k : ℝ) (hk : 0<k)
    (hkp : k^2=‖p‖) (ha : p*a^2=1) : k*‖a‖=1 := by
  have hn : ‖p‖*‖a‖^2=1 := by
    have he := congrArg norm ha
    simpa only [norm_mul,norm_pow,norm_one] using he
  have he : (k*‖a‖)^2=1 := by rw [mul_pow,hkp,hn]
  nlinarith [mul_nonneg hk.le (norm_nonneg a)]

theorem spectralWKB_log_bound (chi p v : ℂ) (hp : p≠0)
    (hchi : ‖chi‖≤ 1) (hv : ‖v‖≤‖p‖^2) :
    ‖homogeneousSpectralWKBLog chi p v‖≤(3/2 : ℝ)*‖p‖ := by
  have hp0 : 0<‖p‖ := norm_pos_iff.mpr hp
  calc
    _ ≤ ‖chi*p‖+‖v/(2*p)‖ := norm_sub_le _ _
    _ = ‖chi‖*‖p‖+‖v‖/(2*‖p‖) := by rw [norm_mul,norm_div,norm_mul]; norm_num
    _ ≤ 1*‖p‖+‖p‖^2/(2*‖p‖) := by gcongr
    _ = _ := by field_simp; ring

theorem spectralWKBState_shell_bound (chi p v a S : ℂ) (k : ℝ)
    (hk : 0<k) (hkp : k^2=‖p‖) (ha : p*a^2=1)
    (hchi : ‖chi‖≤ 1) (hv : ‖v‖≤‖p‖^2) :
    spectralShellNorm k (spectralWKBState chi p v a S)≤(5/2 : ℝ)*Real.exp S.re := by
  have hp0 : 0<‖p‖ := by rw [← hkp]; positivity
  have hka := spectralWKB_amplitude_norm p a k hk hkp ha
  have hL := spectralWKB_log_bound chi p v (norm_pos_iff.mp hp0) hchi hv
  have hder : k⁻¹*‖homogeneousSpectralWKBLog chi p v‖*‖a‖≤ 3/2 := by
    apply (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hL (inv_nonneg.mpr hk.le)) (norm_nonneg a)).trans
    rw [← hkp]
    have he : k⁻¹*((3/2 : ℝ)*k^2)*‖a‖=(3/2 : ℝ)*(k*‖a‖) := by field_simp
    rw [he,hka,mul_one]
  dsimp only [spectralShellNorm,spectralWKBState,spectralWKBValue]
  rw [norm_mul,Complex.norm_exp,norm_mul,norm_mul,Complex.norm_exp]
  calc
    _ = (k*‖a‖+k⁻¹*‖homogeneousSpectralWKBLog chi p v‖*‖a‖)*Real.exp S.re := by ring
    _ ≤ (1+3/2)*Real.exp S.re := mul_le_mul_of_nonneg_right
      (by rw [hka]; linarith) (Real.exp_pos _).le
    _ = _ := by norm_num

end DefocusingNLS

end OAI
