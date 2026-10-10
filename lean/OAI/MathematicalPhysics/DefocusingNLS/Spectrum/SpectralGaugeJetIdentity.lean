import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralGaugeCoordinateEnergy
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalGaugePair

namespace OAI

/-! The physical-to-gauge value identity differentiates to the same column map. -/

namespace DefocusingNLS

theorem spectralGauge_jet_identity (Q f g F G : ℝ → ℂ) (r : ℝ)
    (hQ : DifferentiableAt ℝ Q r) (hf : DifferentiableAt ℝ f r)
    (hg : DifferentiableAt ℝ g r)
    (hp : ∀ t, (Q t*(f t+Complex.I*g t),star (Q t)*(f t-Complex.I*g t))=(F t,G t)) :
    spectralGaugeColumns (Q r) (f r,g r)=(F r,G r) ∧
      spectralGaugeColumns (Q r) (deriv f r,deriv g r)+
        spectralGaugeColumns (deriv Q r) (f r,g r)=(deriv F r,deriv G r) := by
  have hF : (fun t => Q t*(f t+Complex.I*g t))=F :=
    funext (fun t => congrArg Prod.fst (hp t))
  have hG : (fun t => star (Q t)*(f t-Complex.I*g t))=G :=
    funext (fun t => congrArg Prod.snd (hp t))
  have hdF := (hQ.hasDerivAt.mul (hf.hasDerivAt.add (hg.hasDerivAt.const_mul Complex.I))).deriv
  have hdG := (hQ.hasDerivAt.star.mul
    (hf.hasDerivAt.sub (hg.hasDerivAt.const_mul Complex.I))).deriv
  change deriv (fun t => Q t*(f t+Complex.I*g t)) r=
    deriv Q r*(f r+Complex.I*g r)+Q r*(deriv f r+Complex.I*deriv g r) at hdF
  change deriv (fun t => star (Q t)*(f t-Complex.I*g t)) r=
    star (deriv Q r)*(f r-Complex.I*g r)+star (Q r)*(deriv f r-Complex.I*deriv g r) at hdG
  rw [hF] at hdF
  rw [hG] at hdG
  constructor
  · rw [spectralGaugeColumns_apply]
    exact hp r
  · rw [spectralGaugeColumns_apply,spectralGaugeColumns_apply]
    apply Prod.ext
    · exact add_comm _ _ |>.trans hdF.symm
    · exact add_comm _ _ |>.trans hdG.symm

end DefocusingNLS

end OAI
