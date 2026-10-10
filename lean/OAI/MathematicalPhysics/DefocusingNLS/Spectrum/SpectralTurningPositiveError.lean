import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleTerminalError
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleOscillatoryPhase
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningPositiveTransfer

namespace OAI

/-! The actual outgoing orientation has a quantitative WKB error on the
whole positive outer interval. All phase and residual bounds are derived
from the radial frequency and turning scale. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralTurning_positive_terminal_error
    (ell : ℕ) (h b omega gamma r₀ d M E : ℝ)
    (hh : h^2 = 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) (hr₀ : 2 ≤ r₀) (hd : 0 < d) (hM : 32 ≤ M)
    (hMd : M*d ≤ r₀) (hE : 2*r₀ ≤ E) (hEscale : E^2 = 256*max ((ell : ℝ)+1) omega)
    (hz : homogeneousSpectralLocalizationFrequency h b ((ell : ℝ)*(ell+10)) omega r₀ = 0)
    (hscale : spectralLiouvilleSlope ((ell : ℝ)*(ell+10)) r₀*d^3 = 1)
    (q : ℝ → ℂ × ℂ) (hq : ContinuousOn q (Icc (r₀+M*d) E))
    (hODE : ∀ t ∈ Ioo (r₀+M*d) E, HasDerivAt q
      (spectralScalarField ((homogeneousSpectralLocalizationFrequency h b
        ((ell : ℝ)*(ell+10)) omega t : ℂ)+Complex.I*(gamma : ℂ)) (q t)) t) :
    let a := r₀+M*d
    let p := spectralLiouvilleMomentum 1 h b ((ell : ℝ)*(ell+10)) omega gamma
    let v := fun t => (spectralLiouvilleSlope ((ell : ℝ)*(ell+10)) t : ℂ)/(2*p t)
    let chi := (h : ℂ)*Complex.I
    let D := spectralWKBFrame a chi p v
    let U := spectralWKBFrame a (-chi) p v
    let W := (-2 : ℂ)*chi
    let C := (5/2 : ℝ)*Real.exp (|gamma| * 288)
    let J := 5/(3*(Real.sqrt (M/8))^3)+3*d/(r₀*Real.sqrt (M/8))+8/r₀^2
    spectralShellNorm (Real.sqrt ‖p a‖)
      (q a - ((spectralScalarWronskian (q E) (U E)/W) • D a +
        (spectralScalarWronskian (D E) (q E)/W) • U a)) ≤
      (2*(C^2)^2*Real.exp (C^2*J)*J)*spectralShellNorm (Real.sqrt ‖p E‖) (q E) := by
  dsimp only
  let eta : ℝ := (ell : ℝ)*(ell+10)
  let a := r₀+M*d
  let chi := (h : ℂ)*Complex.I
  have heta : 0 ≤ eta := by dsimp only [eta]; positivity
  have hr₀p : 0 < r₀ := by linarith
  have hMp : 0 < M := by linarith
  have ha : r₀ < a := by dsimp only [a]; nlinarith
  have ha0 : 0 < a := hr₀p.trans ha
  have haE : a ≤ E := by dsimp only [a]; linarith
  have hF (t : ℝ) (ht : t ∈ Icc a E) :
      0 < 1*homogeneousSpectralLocalizationFrequency h b eta omega t := by
    have hf := homogeneousSpectralLocalizationFrequency_strictMono h b eta omega heta
      hr₀p (ha0.trans_le ht.1) (ha.trans_le ht.1)
    simpa only [eta,hz,one_mul] using hf
  have hhabs : |h| = 1 := by nlinarith [sq_abs h,abs_nonneg h]
  have hchi : ‖chi‖ = 1 := by
    simp only [chi,norm_mul,Complex.norm_real,Real.norm_eq_abs,hhabs,Complex.norm_I,mul_one]
  have hchi2 : chi^2*(1 : ℂ) = -1 := by
    have hhC : (h : ℂ)^2 = 1 := by exact_mod_cast hh
    simp only [chi,mul_pow,hhC,Complex.I_sq,one_mul,mul_one]
  have hchiRe : chi.re = 0 := by
    simp only [chi,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,
      Complex.I_im,mul_zero,zero_mul,sub_zero]
  have hA : (∫ t in a..E, 1/Real.sqrt (homogeneousSpectralLocalizationFrequency h b eta omega t)) ≤ 288 :=
    spectralTurning_positive_outer_phase ell h b omega r₀ d M E
      hh hb hb1 hr₀p hd hMp hMd hE hEscale hz
  have hp := spectralLiouville_positive_phase_bound h b eta omega gamma a E 288 ha0 haE
    chi hchi hchiRe (fun t ht => by simpa only [one_mul] using hF t ht) hA
  have hj := spectralTurning_outer_positive_error h b eta omega gamma r₀ d M E
    heta hr₀p hd hMp hMd hE hz hscale
  have he := spectralLiouville_terminal_error 1 h b eta omega gamma a E (|gamma| * 288)
    (5/(3*(Real.sqrt (M/8))^3)+3*d/(r₀*Real.sqrt (M/8))+8/r₀^2)
    (by norm_num) ha0 haE chi hchi hchi2 hF
    (fun t ht => spectralTurning_positive_derivative_small 1 h b eta omega gamma r₀ d M t
      (by norm_num) heta hr₀ hd hM ht.1 hz hscale) hp hj q hq hODE
  simpa only [Complex.ofReal_one,one_mul] using he

end DefocusingNLS

end OAI
