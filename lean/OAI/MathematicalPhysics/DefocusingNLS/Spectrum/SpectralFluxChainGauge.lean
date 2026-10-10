import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralChainCircular
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralChainFluxSmoothness
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralForcedGauge
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeFluxGauge

namespace OAI

/-! A parameter chain of the weighted flux ODE becomes the forced physical ODE. -/

open Set
open scoped ContDiff
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem spectralFluxChainGauge_hasDerivAt (ell : ℕ) (σ b ζ : ℂ) (hσ : σ^2=1)
    (μ A : ℝ → ℝ) (Q : ℝ → ℂ) (U₀ U₁ : ℝ → E₄)
    (l R : ℝ) (hl : 0 < l) (r dμ : ℝ) (hr : r ∈ Ioo l R)
    (hμn : ∀ t ∈ Ioo l R, μ t ≠ 0)
    (hU : ∀ t ∈ Ioo l R, HasDerivAt U₁
      (spectralFluxField ell (μ t) (A t) 6 ζ t (U₁ t) + spectralFluxFieldSlope (μ t) t (U₀ t)) t)
    (hUs : ContDiffAt ℝ ∞ U₁ r)
    (hμ : HasDerivAt μ dμ r) (hA : HasDerivAt A (6*μ r-11/r*A r) r)
    (hQ : DifferentiableAt ℝ Q r) (hDQ : DifferentiableAt ℝ (deriv Q) r)
    (hQE : deriv (deriv Q) r+(11/(r : ℂ)+σ*Complex.I*(r : ℂ)/2)*deriv Q r+b*Q r=0)
    (hC : ((dμ : ℂ)+σ*Complex.I*(A r : ℂ))*Q r=
      (μ r : ℂ)*(2*deriv Q r+σ*Complex.I*(r : ℂ)/2*Q r)) :
    HasDerivAt (spectralFluxGaugeJet Q σ U₁)
      (spectralFreePhysicalField σ b ζ ((ell : ℂ)*((ell : ℂ)+10)) r
        (spectralFluxGaugeJet Q σ U₁ r) +
        (0,-σ*Complex.I*(spectralFluxGaugeJet Q σ U₀ r).1)) r := by
  let V := spectralFluxCircularValue σ U₁
  have hV : ContDiffAt ℝ ∞ V r := hUs.fst.fst.add (contDiffAt_const.mul hUs.fst.snd)
  have hVd := hV.differentiableAt (by simp)
  have hDV := (hV.derivWithin (m := 1) (by simp)).differentiableAt (by simp)
  have hF := spectralFluxChainCircular_hasDerivAt ell σ ζ hσ μ A U₀ U₁ l R hl hμn hU r hr
  have hF' : HasDerivAt (spectralWeightedCircularFlux σ μ A V)
      (((ell : ℂ)*((ell : ℂ)+10))*(r : ℂ)^9*(μ r : ℂ)*V r+
        σ*Complex.I*(6-ζ)*(r : ℂ)^11*(μ r : ℂ)*V r+
        (r : ℂ)^11*(μ r : ℂ)*(-σ*Complex.I*spectralFluxCircularValue σ U₀ r)) r := by
    apply hF.congr_deriv
    ring
  have hd := spectralForcedFreeGaugeJet_hasDerivAt σ b ζ ((ell : ℂ)*((ell : ℂ)+10))
    (-σ*Complex.I*spectralFluxCircularValue σ U₀ r) μ A Q V r dμ (hl.trans hr.1).ne'
    (hμn r hr) hμ hA hQ hDQ hVd hDV hQE hC hF'
  apply hd.congr_deriv
  apply Prod.ext
  · simp only [Prod.fst_add,add_zero]
    rfl
  · dsimp only [Prod.snd_add,spectralFreePhysicalField,spectralFluxGaugeJet]
    ring

end DefocusingNLS

end OAI
