import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNoTurnRemoteSlope
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNoTurnResidual
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleOutgoingBranch
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleOscillatoryPhase

namespace OAI

/-! The prescribed outgoing data follow a single WKB branch throughout
the actual frequency-dominated, no-turn channel. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralNoTurn_outgoing_branch_error
    (b eta omega gamma C R E : ℝ)
    (hb : 0 ≤ b) (heta : 0 ≤ eta) (hw : 0 < omega) (hC : 0 ≤ C) (hCw : C ≤ omega)
    (hR : 0 < R) (hRE : R ≤ E) (hE : 0 < E) (hEs : E^2 = 256*omega)
    (hL : eta+99/4 ≤ C*omega) (hCR : 2*C ≤ R^2)
    (hgamma : |gamma| ≤ 8) (hEbound : E ≤ 32*Real.sqrt (omega/2))
    (hlarge : 2/R+4*C/R^3 ≤ 2*Real.sqrt (omega/2))
    (q : ℝ → ℂ × ℂ) (hq : ContinuousOn q (Icc R E))
    (hqE : q E = spectralOscillatoryData (-1)
      (Real.sqrt (Real.sqrt (homogeneousSpectralLocalizationFrequency (-1) b eta omega E))))
    (hODE : ∀ t ∈ Ioo R E, HasDerivAt q
      (spectralScalarField ((homogeneousSpectralLocalizationFrequency (-1) b eta omega t : ℂ)+
        Complex.I*(gamma : ℂ)) (q t)) t) :
    let p := spectralLiouvilleMomentum 1 (-1) b eta omega gamma
    let v := fun t => (spectralLiouvilleSlope eta t : ℂ)/(2*p t)
    let D := spectralWKBFrame R (-Complex.I) p v
    let B := (5/2 : ℝ)*Real.exp 256
    let J := 2*((5/16)*(2/R+4*C/R^3)+3/(4*R))/Real.sqrt (omega/2)
    spectralShellNorm (Real.sqrt ‖p R‖) (q R-((q E).1/(D E).1) • D R) ≤
      (2*(B^2)^2*Real.exp (B^2*J)*J)*spectralShellNorm (Real.sqrt ‖p E‖) (q E)+
        B^2*((32*|gamma|+8)/E^2) := by
  have hF (t : ℝ) (ht : t ∈ Icc R E) :
      0 < homogeneousSpectralLocalizationFrequency (-1) b eta omega t :=
    lt_of_lt_of_le (by positivity) (spectralNoTurn_frequency_lower b eta omega C R t hb hw hR ht.1 hL hCR)
  have hsmall (t : ℝ) (ht : t ∈ Icc R E) := spectralNoTurn_derivative_small
    b eta omega gamma C R t hb heta hw hC hR ht.1 hL hCR hlarge
  have hphase := spectralNoTurn_phase_bound b eta omega C R E 32 hb hw hR hRE hL hCR hEbound
  have hp := spectralLiouville_positive_phase_bound (-1) b eta omega gamma R E 32 hR hRE
    (-Complex.I) (by simp only [norm_neg,Complex.norm_I]) (by simp only [Complex.neg_re,Complex.I_re,neg_zero]) hF hphase
  have hp' (t : ℝ) (ht : t ∈ Icc R E) :
      |(spectralWKBPhase R (-Complex.I) (spectralLiouvilleMomentum 1 (-1) b eta omega gamma) t).re| ≤ 256 :=
    (hp t ht).trans (by linarith)
  have hj := spectralNoTurn_residual_integral b eta omega gamma C R E hb heta hw hC hR hRE hL hCR
  obtain ⟨hFar,hgFar⟩ := spectralNoTurn_remote_slope b eta omega C E hb heta hw hC hCw hE hEs hL
  have hb := spectralLiouville_outgoing_branch_error (-1) b eta omega gamma R E 256
    (2*((5/16)*(2/R+4*C/R^3)+3/(4*R))/Real.sqrt (omega/2))
    (by norm_num) hR hRE hE (by simpa only [one_mul] using hF) hsmall
    (by simpa only [Complex.ofReal_neg,Complex.ofReal_one,neg_mul,one_mul] using hp')
    hj hFar hgFar q hq hqE hODE
  simpa only [Complex.ofReal_neg,Complex.ofReal_one,neg_mul,one_mul] using hb

end DefocusingNLS

end OAI
