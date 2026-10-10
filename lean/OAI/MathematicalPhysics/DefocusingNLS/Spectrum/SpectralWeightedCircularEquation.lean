import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreeGaugeAlgebra

namespace OAI

/-! Classical circular equation obtained from the weighted divergence flux. -/

namespace DefocusingNLS

noncomputable def spectralWeightedCircularFlux (σ : ℂ) (μ A : ℝ → ℝ)
    (u : ℝ → ℂ) (r : ℝ) : ℂ :=
  (r : ℂ)^11*((μ r : ℂ)*deriv u r+σ*Complex.I*(A r : ℂ)*u r)

theorem spectralWeightedCircularEquation (σ ζ η : ℂ) (μ A : ℝ → ℝ)
    (u : ℝ → ℂ) (r dμ : ℝ) (hr : r ≠ 0)
    (hμ : HasDerivAt μ dμ r)
    (hA : HasDerivAt A (6*μ r-11/r*A r) r)
    (hu : DifferentiableAt ℝ u r) (hDu : DifferentiableAt ℝ (deriv u) r)
    (hF : HasDerivAt (spectralWeightedCircularFlux σ μ A u)
      (η*(r : ℂ)^9*(μ r : ℂ)*u r+
        σ*Complex.I*(6-ζ)*(r : ℂ)^11*(μ r : ℂ)*u r) r) :
    (μ r : ℂ)*deriv (deriv u) r+
      (11*(μ r : ℂ)/(r : ℂ)+(dμ : ℂ)+σ*Complex.I*(A r : ℂ))*deriv u r+
      (σ*Complex.I*ζ*(μ r : ℂ)-η*(μ r : ℂ)/(r : ℂ)^2)*u r=0 := by
  have hd := (((hasDerivAt_id r).ofReal_comp).pow 11).mul
    ((hμ.ofReal_comp.mul hDu.hasDerivAt).add
      ((hA.ofReal_comp.const_mul (σ*Complex.I)).mul hu.hasDerivAt))
  have he := hd.unique hF
  dsimp only [id_eq,Pi.pow_apply,Pi.mul_apply,Pi.add_apply] at he
  push_cast at he
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  linear_combination (norm := (field_simp [hrC]; ring_nf)) (1/(r : ℂ)^11)*he

theorem spectralFreeGaugeJet_hasDerivAt (σ b ζ η : ℂ) (μ A : ℝ → ℝ)
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
        σ*Complex.I*(6-ζ)*(r : ℂ)^11*(μ r : ℂ)*u r) r) :
    HasDerivAt (fun t => (Q t*u t,deriv Q t*u t+Q t*deriv u t))
      (deriv Q r*u r+Q r*deriv u r,
       -(11/(r : ℂ)+σ*Complex.I*(r : ℂ)/2)*(deriv Q r*u r+Q r*deriv u r)-
         (b+σ*Complex.I*ζ-η/(r : ℂ)^2)*(Q r*u r)) r := by
  have hU := spectralWeightedCircularEquation σ ζ η μ A u r dμ hr hμ hA hu hDu hF
  have he := spectralFreeGauge_algebra (r : ℂ) (μ r : ℂ) (dμ : ℂ) (A r : ℂ)
    σ b ζ η (Q r) (deriv Q r) (deriv (deriv Q) r) (u r) (deriv u r)
    (deriv (deriv u) r) (Complex.ofReal_ne_zero.mpr hμn) hQE hC hU
  apply ((hQ.hasDerivAt.mul hu.hasDerivAt).prodMk
    ((hDQ.hasDerivAt.mul hu.hasDerivAt).add (hQ.hasDerivAt.mul hDu.hasDerivAt))).congr_deriv
  apply Prod.ext
  · rfl
  · dsimp only
    linear_combination he

end DefocusingNLS

end OAI
