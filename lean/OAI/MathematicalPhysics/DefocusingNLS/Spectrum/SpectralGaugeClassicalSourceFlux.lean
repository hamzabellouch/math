import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralGaugeClassicalFlux

namespace OAI

/-! Flux derivatives for a radial source pair, including its first-chain forcing. -/

namespace DefocusingNLS

theorem spectralGaugeClassicalSourceFlux (μ A : ℝ → ℝ) (f g F G : ℝ → ℂ)
    (r dμ c : ℝ) (η lam pressure : ℂ) (hr : r ≠ 0) (hμn : μ r ≠ 0)
    (hμ : HasDerivAt μ dμ r)
    (hA : HasDerivAt A (c*μ r-11/r*A r) r)
    (hf : DifferentiableAt ℝ f r) (hg : DifferentiableAt ℝ g r)
    (hdf : DifferentiableAt ℝ (deriv f) r) (hdg : DifferentiableAt ℝ (deriv g) r)
    (heF : lam*f r+F r=-(deriv (deriv g) r+
      (11/(r : ℂ)+(dμ : ℂ)/(μ r : ℂ))*deriv g r-η/(r : ℂ)^2*g r)-
        (A r : ℂ)/(μ r : ℂ)*deriv f r)
    (heG : lam*g r+G r=deriv (deriv f) r+
      (11/(r : ℂ)+(dμ : ℂ)/(μ r : ℂ))*deriv f r-η/(r : ℂ)^2*f r-
        (A r : ℂ)/(μ r : ℂ)*deriv g r-pressure*f r) :
    HasDerivAt (spectralGaugeFirstFlux μ A f g)
      (η*(r : ℂ)^9*(μ r : ℂ)*f r+
        (r : ℂ)^11*(μ r : ℂ)*(pressure*f r+(lam-(c : ℂ))*g r+G r)) r ∧
    HasDerivAt (spectralGaugeSecondFlux μ A f g)
      (η*(r : ℂ)^9*(μ r : ℂ)*g r+
        (r : ℂ)^11*(μ r : ℂ)*(((c : ℂ)-lam)*f r-F r)) r := by
  have hpow := ((hasDerivAt_id r).ofReal_comp).pow 11
  have hfirst := hpow.mul ((hμ.ofReal_comp.mul hdf.hasDerivAt).sub
    (hA.ofReal_comp.mul hg.hasDerivAt))
  have hsecond := hpow.mul ((hμ.ofReal_comp.mul hdg.hasDerivAt).add
    (hA.ofReal_comp.mul hf.hasDerivAt))
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  have hμC : (μ r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hμn
  constructor
  · apply hfirst.congr_deriv
    dsimp only [id_eq,Pi.pow_apply,Pi.mul_apply,Pi.sub_apply,Pi.add_apply]
    push_cast
    linear_combination (norm := (field_simp [hrC,hμC]; ring_nf))
      -(r : ℂ)^11*(μ r : ℂ)*heG
  · apply hsecond.congr_deriv
    dsimp only [id_eq,Pi.pow_apply,Pi.mul_apply,Pi.sub_apply,Pi.add_apply]
    push_cast
    linear_combination (norm := (field_simp [hrC,hμC]; ring_nf))
      (r : ℂ)^11*(μ r : ℂ)*heF

end DefocusingNLS

end OAI
