import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBFluxMargin
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBFrameBound

namespace OAI

/-! The outgoing WKB logarithmic slope gives a lower bound for the flux of
the full Cauchy state, measured by its scaled first coordinate. -/

namespace DefocusingNLS

theorem spectralScalarFlux_graph (z L : ℂ) :
    spectralScalarFlux (z,L*z) = ‖z‖^2*L.im := by
  rw [← Complex.normSq_eq_norm_sq]
  simp only [spectralScalarFlux,Complex.star_def,Complex.mul_im,Complex.mul_re,
    Complex.conj_re,Complex.conj_im,Complex.normSq_apply]
  ring

theorem spectralWKBState_value_norm (chi p v a S : ℂ) (k : ℝ)
    (hk : 0 < k) (hkp : k^2 = ‖p‖) (ha : p*a^2 = 1) :
    k*‖(spectralWKBState chi p v a S).1‖ = Real.exp S.re := by
  have hka := spectralWKB_amplitude_norm p a k hk hkp ha
  simp only [spectralWKBState,spectralWKBValue,norm_mul,Complex.norm_exp]
  rw [← mul_assoc,hka,one_mul]

theorem spectralWKBState_flux_lower (h F gamma k : ℝ) (v a S : ℂ)
    (hh : h^2 = 1) (hF : 0 < F)
    (hkp : k^2 = ‖Complex.sqrt ((F : ℂ)+Complex.I*(gamma : ℂ))‖)
    (hv : ‖v‖ ≤ ‖Complex.sqrt ((F : ℂ)+Complex.I*(gamma : ℂ))‖^2) :
    (k*‖(spectralWKBState ((h : ℂ)*Complex.I)
      (Complex.sqrt ((F : ℂ)+Complex.I*(gamma : ℂ))) v a S).1‖)^2/6 ≤
      h*spectralScalarFlux (spectralWKBState ((h : ℂ)*Complex.I)
        (Complex.sqrt ((F : ℂ)+Complex.I*(gamma : ℂ))) v a S) := by
  let p := Complex.sqrt ((F : ℂ)+Complex.I*(gamma : ℂ))
  have hl := spectralWKB_log_flux_margin h F gamma v hh hF hv
  have hm := mul_le_mul_of_nonneg_right hl (sq_nonneg ‖spectralWKBValue a S‖)
  change (k*‖spectralWKBValue a S‖)^2/6 ≤
    h*spectralScalarFlux (spectralWKBValue a S,
      homogeneousSpectralWKBLog ((h : ℂ)*Complex.I) p v*spectralWKBValue a S)
  rw [spectralScalarFlux_graph,mul_pow,hkp]
  nlinarith

end DefocusingNLS

end OAI
