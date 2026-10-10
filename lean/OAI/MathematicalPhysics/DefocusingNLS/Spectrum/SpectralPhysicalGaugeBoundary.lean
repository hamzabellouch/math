import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFluxRobin
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralGaugeClassicalFlux
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalGaugePair

namespace OAI

/-! A classical physical Robin condition gives the exact weighted gauge flux. -/

namespace DefocusingNLS

theorem spectralPhysicalGaugeBoundary (R μ A : ℝ) (hR : R ≠ 0) (hμ : μ ≠ 0)
    (Q f g F G : ℝ → ℂ) (hQ : DifferentiableAt ℝ Q R)
    (hf : DifferentiableAt ℝ f R) (hg : DifferentiableAt ℝ g R) (hQn : Q R ≠ 0)
    (hp : ∀ r, (Q r*(f r+Complex.I*g r),star (Q r)*(f r-Complex.I*g r))=(F r,G r))
    (M : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hM : (deriv F R,deriv G R)=M (F R,G R)) :
    ((R : ℂ)^11*((μ : ℂ)*deriv f R-(A : ℂ)*g R),
     (R : ℂ)^11*((μ : ℂ)*deriv g R+(A : ℂ)*f R))=
      spectralFluxBoundary R μ A (spectralGaugeRobin (Q R) (deriv Q R) M) (f R,g R) := by
  have hF : (fun r => Q r*(f r+Complex.I*g r))=F :=
    funext (fun r => congrArg Prod.fst (hp r))
  have hG : (fun r => star (Q r)*(f r-Complex.I*g r))=G :=
    funext (fun r => congrArg Prod.snd (hp r))
  have hdF := (hQ.hasDerivAt.mul (hf.hasDerivAt.add (hg.hasDerivAt.const_mul Complex.I))).deriv
  have hdG := (hQ.hasDerivAt.star.mul
    (hf.hasDerivAt.sub (hg.hasDerivAt.const_mul Complex.I))).deriv
  change deriv (fun r => Q r*(f r+Complex.I*g r)) R=
    deriv Q R*(f R+Complex.I*g R)+Q R*(deriv f R+Complex.I*deriv g R) at hdF
  change deriv (fun r => star (Q r)*(f r-Complex.I*g r)) R=
    star (deriv Q R)*(f R-Complex.I*g R)+star (Q R)*(deriv f R-Complex.I*deriv g R) at hdG
  rw [hF] at hdF
  rw [hG] at hdG
  apply (spectralGaugeFluxBoundary_condition R μ A hR hμ (Q R) (deriv Q R)
    hQn M (f R,g R) (deriv f R,deriv g R)).mpr
  have hv : spectralGaugeColumns (Q R) (f R,g R)=(F R,G R) := by
    rw [← spectralPhysicalGaugePair_value Q f g R]
    exact hp R
  rw [hv,← hM]
  rw [← spectralPhysicalGaugePair_slope]
  exact Prod.ext hdF.symm hdG.symm

end DefocusingNLS

end OAI
