import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWeightedCircularEquation

namespace OAI

/-! Classical circular equation obtained from the weighted divergence flux. -/

namespace DefocusingNLS

theorem spectralForcedWeightedCircularEquation (σ ζ η F : ℂ) (μ A : ℝ → ℝ)
    (u : ℝ → ℂ) (r dμ : ℝ) (hr : r ≠ 0)
    (hμ : HasDerivAt μ dμ r)
    (hA : HasDerivAt A (6*μ r-11/r*A r) r)
    (hu : DifferentiableAt ℝ u r) (hDu : DifferentiableAt ℝ (deriv u) r)
    (hF : HasDerivAt (spectralWeightedCircularFlux σ μ A u)
      (η*(r : ℂ)^9*(μ r : ℂ)*u r+
        σ*Complex.I*(6-ζ)*(r : ℂ)^11*(μ r : ℂ)*u r +
        (r : ℂ)^11*(μ r : ℂ)*F) r) :
    (μ r : ℂ)*deriv (deriv u) r+
      (11*(μ r : ℂ)/(r : ℂ)+(dμ : ℂ)+σ*Complex.I*(A r : ℂ))*deriv u r+
      (σ*Complex.I*ζ*(μ r : ℂ)-η*(μ r : ℂ)/(r : ℂ)^2)*u r=(μ r : ℂ)*F := by
  have hd := (((hasDerivAt_id r).ofReal_comp).pow 11).mul
    ((hμ.ofReal_comp.mul hDu.hasDerivAt).add
      ((hA.ofReal_comp.const_mul (σ*Complex.I)).mul hu.hasDerivAt))
  have he := hd.unique hF
  dsimp only [id_eq,Pi.pow_apply,Pi.mul_apply,Pi.add_apply] at he
  push_cast at he
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  linear_combination (norm := (field_simp [hrC]; ring_nf)) (1/(r : ℂ)^11)*he

theorem spectralForcedFreeGaugeJet_hasDerivAt (σ b ζ η F : ℂ) (μ A : ℝ → ℝ)
    (Q u : ℝ → ℂ) (r dμ : ℝ) (hr : r ≠ 0) (hμn : μ r ≠ 0)
    (hμ : HasDerivAt μ dμ r)
    (hA : HasDerivAt A (6*μ r-11/r*A r) r)
    (hQ : DifferentiableAt ℝ Q r) (hDQ : DifferentiableAt ℝ (deriv Q) r)
    (hu : DifferentiableAt ℝ u r) (hDu : DifferentiableAt ℝ (deriv u) r)
    (hQE : deriv (deriv Q) r+(11/(r : ℂ)+σ*Complex.I*(r : ℂ)/2)*deriv Q r+b*Q r=0)
    (hC : ((dμ : ℂ)+σ*Complex.I*(A r : ℂ))*Q r=
      (μ r : ℂ)*(2*deriv Q r+σ*Complex.I*(r : ℂ)/2*Q r))
    (hF : HasDerivAt (spectralWeightedCircularFlux σ μ A u)
      (η*(r : ℂ)^9*(μ r : ℂ)*u r+
        σ*Complex.I*(6-ζ)*(r : ℂ)^11*(μ r : ℂ)*u r +
        (r : ℂ)^11*(μ r : ℂ)*F) r) :
    HasDerivAt (fun t => (Q t*u t,deriv Q t*u t+Q t*deriv u t))
      (deriv Q r*u r+Q r*deriv u r,
       -(11/(r : ℂ)+σ*Complex.I*(r : ℂ)/2)*(deriv Q r*u r+Q r*deriv u r)-
         (b+σ*Complex.I*ζ-η/(r : ℂ)^2)*(Q r*u r) + Q r*F) r := by
  have hU := spectralForcedWeightedCircularEquation σ ζ η F μ A u r dμ hr hμ hA hu hDu hF
  have he : deriv (deriv Q) r*u r+2*deriv Q r*deriv u r+Q r*deriv (deriv u) r+
      (11/(r : ℂ)+σ*Complex.I*(r : ℂ)/2)*(deriv Q r*u r+Q r*deriv u r)+
      (b+σ*Complex.I*ζ-η/(r : ℂ)^2)*(Q r*u r)=Q r*F := by
    apply (mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hμn))
    linear_combination Q r*hU-deriv u r*hC+(μ r : ℂ)*u r*hQE
  apply ((hQ.hasDerivAt.mul hu.hasDerivAt).prodMk
    ((hDQ.hasDerivAt.mul hu.hasDerivAt).add (hQ.hasDerivAt.mul hDu.hasDerivAt))).congr_deriv
  apply Prod.ext
  · rfl
  · dsimp only
    linear_combination he

end DefocusingNLS

end OAI
