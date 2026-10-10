import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalGaugeBoundary
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralGaugeRobinDerivative
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFluxBoundaryDerivative

namespace OAI

/-! A physical generalized mode induces exactly the differentiated weak boundary condition. -/

namespace DefocusingNLS

theorem spectralGaugeRobin_chain_iff (q dq : ℂ) (hq : q ≠ 0)
    (M M' : ℂ × ℂ →L[ℂ] ℂ × ℂ) (x₀ x₁ dx₁ : ℂ × ℂ) :
    dx₁ = spectralGaugeRobin q dq M x₁ + spectralGaugeRobinSlope q M' x₀ ↔
      spectralGaugeColumns q dx₁ + spectralGaugeColumns dq x₁ =
        M (spectralGaugeColumns q x₁) + M' (spectralGaugeColumns q x₀) := by
  constructor
  · exact spectralGaugeRobin_chain_condition q dq hq M M' x₀ x₁ dx₁
  · intro h
    have hslope : spectralGaugeColumns q (spectralGaugeRobinSlope q M' x₀)=
        M' (spectralGaugeColumns q x₀) := spectralGaugeColumns_inverse q hq _
    have hh : spectralGaugeColumns q (dx₁-spectralGaugeRobinSlope q M' x₀)+
        spectralGaugeColumns dq x₁=M (spectralGaugeColumns q x₁) := by
      calc
        _ = (spectralGaugeColumns q dx₁+spectralGaugeColumns dq x₁)-
            M' (spectralGaugeColumns q x₀) := by rw [map_sub,hslope]; abel
        _ = _ := by rw [h]; abel
    exact sub_eq_iff_eq_add.mp ((spectralGaugeRobin_condition q dq hq M x₁ _).mp hh)

theorem spectralPhysicalGaugeSourceBoundary (R μ A : ℝ) (hR : R ≠ 0) (hμ : μ ≠ 0)
    (Q f g F G f₀ g₀ : ℝ → ℂ) (hQ : DifferentiableAt ℝ Q R)
    (hf : DifferentiableAt ℝ f R) (hg : DifferentiableAt ℝ g R) (hQn : Q R ≠ 0)
    (hp : ∀ r, (Q r*(f r+Complex.I*g r),star (Q r)*(f r-Complex.I*g r))=(F r,G r))
    (M M' : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hM : (deriv F R,deriv G R)=M (F R,G R)+M' (Q R*(f₀ R+Complex.I*g₀ R),star (Q R)*(f₀ R-Complex.I*g₀ R))) :
    ((R : ℂ)^11*((μ : ℂ)*deriv f R-(A : ℂ)*g R),
     (R : ℂ)^11*((μ : ℂ)*deriv g R+(A : ℂ)*f R))=
      spectralFluxBoundary R μ A (spectralGaugeRobin (Q R) (deriv Q R) M) (f R,g R)+
      spectralFluxBoundarySlope R μ (spectralGaugeRobinSlope (Q R) M') (f₀ R,g₀ R) := by
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
  apply (spectralFluxBoundary_chain_condition R μ A hR hμ
    (spectralGaugeRobin (Q R) (deriv Q R) M) (spectralGaugeRobinSlope (Q R) M')
      (f₀ R,g₀ R) (f R,g R) (deriv f R,deriv g R)).mpr
  apply (spectralGaugeRobin_chain_iff (Q R) (deriv Q R) hQn M M'
    (f₀ R,g₀ R) (f R,g R) (deriv f R,deriv g R)).mpr
  have hv : spectralGaugeColumns (Q R) (f R,g R)=(F R,G R) := by
    rw [← spectralPhysicalGaugePair_value Q f g R]
    exact hp R
  have hv₀ : spectralGaugeColumns (Q R) (f₀ R,g₀ R)=
      (Q R*(f₀ R+Complex.I*g₀ R),star (Q R)*(f₀ R-Complex.I*g₀ R)) := by
    change (f₀ R*Q R+g₀ R*(Complex.I*Q R),f₀ R*star (Q R)+g₀ R*(-Complex.I*star (Q R)))=_
    apply Prod.ext <;> dsimp only <;> ring
  rw [hv,hv₀,← hM]
  rw [← spectralPhysicalGaugePair_slope]
  exact Prod.ext hdF.symm hdG.symm

end DefocusingNLS

end OAI
