import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleEndpoint
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleOrientation
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningOuterDerivative
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningOuterPhase
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningOuterPositive

namespace OAI

/-! Uniform transfer for an actual solution on the whole oscillatory outer
interval. All WKB error and orientation assumptions are discharged. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralTurning_positive_endpoint_transfer
    (ell : ℕ) (h b omega gamma r₀ d M E : ℝ)
    (hh : h^2=1) (hb : 0≤b) (hb1 : b≤1) (hr₀ : 2≤r₀) (hd : 0<d) (hM : 32≤M)
    (hMd : M*d≤r₀) (hE : 2*r₀≤E) (hEscale : E^2=256*max ((ell : ℝ)+1) omega)
    (hz : homogeneousSpectralLocalizationFrequency h b ((ell : ℝ)*(ell+10)) omega r₀=0)
    (hscale : spectralLiouvilleSlope ((ell : ℝ)*(ell+10)) r₀*d^3=1)
    (q : ℝ → ℂ × ℂ) (hq : ContinuousOn q (Icc (r₀+M*d) E))
    (hODE : ∀ t ∈ Ioo (r₀+M*d) E, HasDerivAt q
      (spectralScalarField ((homogeneousSpectralLocalizationFrequency h b
        ((ell : ℝ)*(ell+10)) omega t : ℂ)+Complex.I*(gamma : ℂ)) (q t)) t) :
    spectralShellNorm (Real.sqrt ‖spectralLiouvilleMomentum 1 h b
      ((ell : ℝ)*(ell+10)) omega gamma E‖) (q E)≤
      (25/4 : ℝ)*spectralShellNorm (Real.sqrt ‖spectralLiouvilleMomentum 1 h b
        ((ell : ℝ)*(ell+10)) omega gamma (r₀+M*d)‖) (q (r₀+M*d))*
      Real.exp (|gamma| *288+(25/4)*(5/(3*(Real.sqrt (M/8))^3)+
        3*d/(r₀*Real.sqrt (M/8))+8/r₀^2)) := by
  let eta : ℝ := (ell : ℝ)*(ell+10)
  let a := r₀+M*d
  have heta : 0≤eta := by dsimp only [eta]; positivity
  have hr₀p : 0<r₀ := by linarith
  have hMp : 0<M := by linarith
  have ha : r₀<a := by dsimp only [a]; nlinarith
  have ha0 : 0<a := hr₀p.trans ha
  have haE : a≤E := by dsimp only [a]; linarith
  have hF (t : ℝ) (ht : t ∈ Icc a E) :
      0<1*homogeneousSpectralLocalizationFrequency h b eta omega t := by
    have hf := homogeneousSpectralLocalizationFrequency_strictMono h b eta omega heta
      hr₀p (ha0.trans_le ht.1) (ha.trans_le ht.1)
    simpa only [eta,hz,one_mul] using hf
  obtain ⟨chi,hchi,hchi2,hphase⟩ := spectralLiouville_orientation 1 h b eta omega gamma a E
    (by norm_num) (fun t ht => hF t ⟨ht.1.le,ht.2.le⟩)
  have hchiRe : chi.re=0 := by
    have hc2 : chi^2=Complex.I^2 := by simpa only [Complex.ofReal_one,mul_one,Complex.I_sq] using hchi2
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hc2 with hc | hc
    · simp only [hc,Complex.I_re]
    · simp only [hc,Complex.neg_re,Complex.I_re,neg_zero]
  have ht := spectralLiouville_endpoint_bound 1 h b eta omega gamma a E 288
    (5/(3*(Real.sqrt (M/8))^3)+3*d/(r₀*Real.sqrt (M/8))+8/r₀^2)
    (by norm_num) ha0 haE chi hchi hchi2 hF
    (fun t ht => spectralTurning_positive_derivative_small 1 h b eta omega gamma r₀ d M t
      (by norm_num) heta hr₀ hd hM ht.1 hz hscale) hphase
    (by
      simpa only [one_mul] using
        spectralTurning_positive_outer_phase ell h b omega r₀ d M E
          hh hb hb1 hr₀p hd hMp hMd hE hEscale hz)
    (spectralTurning_outer_positive_error h b eta omega gamma r₀ d M E
      heta hr₀p hd hMp hMd hE hz hscale) q hq hODE
  simpa only [hchiRe,zero_mul,zero_add] using ht

end DefocusingNLS

end OAI
