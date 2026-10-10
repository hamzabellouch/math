import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFluxChainGauge
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFluxLocalSmoothness
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeConjugate

namespace OAI

/-! The actual limiting flux system gives the two decoupled free physical equations. -/

open Set
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem radialMatchedFreeFluxChain_contDiffOn (ell : ℕ) (z : ProfileMatchingBall)
    (hz₁ : z.val.1=0) (hz : diskProfile (profileMatchingParameter z)=0)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (R : ℝ) (ζ : ℂ) (U₀ U : ℝ → E₄)
    (hU₀ : ∀ r ∈ Ioo (radialShootingR (profileMatchingParameter z)) R,
      HasDerivAt U₀ (spectralFluxField ell (radialMatchedFreeMassFunction z r)
        (radialMatchedFreeTransportFunction z r) 6 ζ r (U₀ r)) r)
    (hU : ∀ r ∈ Ioo (radialShootingR (profileMatchingParameter z)) R,
      HasDerivAt U (spectralFluxField ell (radialMatchedFreeMassFunction z r)
        (radialMatchedFreeTransportFunction z r) 6 ζ r (U r) +
        spectralFluxFieldSlope (radialMatchedFreeMassFunction z r) r (U₀ r)) r) :
    ContDiffOn ℝ ∞ U (Ioo (radialShootingR (profileMatchingParameter z)) R) := by
  apply spectralFluxChain_contDiffOn ell _ _ 6 ζ _ R
    (lt_of_lt_of_le (by norm_num) (radialShooting_geometry (profileMatchingParameter z)).2.1) U₀ U
    _ _ _ (radialMatchedFreeFlux_contDiffOn ell z hz₁ hz hc R ζ U₀ hU₀) hU
  · intro α β hα _
    exact (radialMatchedFreeMass_contDiffOn_matched z hz₁ hz).mono
      (fun _ hr => hα.trans_le hr.1)
  · intro α β hα _
    exact radialMatchedFreeTransport_contDiffOn_matched z hz₁ hz hc α β hα
  · intro r hr
    exact (radialMatchedFreeMass_pos z r
      (le_trans (by linarith [(radialShooting_geometry (profileMatchingParameter z)).2.1]) hr.1.le)).ne'

private theorem fluxChainGauge_at (ell : ℕ) (z : ProfileMatchingBall)
    (hz₁ : z.val.1=0) (hz : diskProfile (profileMatchingParameter z)=0)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (R : ℝ) (ζ σ : ℂ) (hσ : σ^2=1)
    (U₀ U : ℝ → E₄)
    (hU₀ : ∀ r ∈ Ioo (radialShootingR (profileMatchingParameter z)) R,
      HasDerivAt U₀ (spectralFluxField ell (radialMatchedFreeMassFunction z r)
        (radialMatchedFreeTransportFunction z r) 6 ζ r (U₀ r)) r)
    (hU : ∀ r ∈ Ioo (radialShootingR (profileMatchingParameter z)) R,
      HasDerivAt U (spectralFluxField ell (radialMatchedFreeMassFunction z r)
        (radialMatchedFreeTransportFunction z r) 6 ζ r (U r) +
        spectralFluxFieldSlope (radialMatchedFreeMassFunction z r) r (U₀ r)) r)
    (Q : ℝ → ℂ) (r : ℝ) (hr : r ∈ Ioo (radialShootingR (profileMatchingParameter z)) R)
    (hQ : DifferentiableAt ℝ Q r) (hDQ : DifferentiableAt ℝ (deriv Q) r)
    (hQE : deriv (deriv Q) r+(11/(r : ℂ)+σ*Complex.I*(r : ℂ)/2)*deriv Q r+
      (radialShootingB (profileMatchingParameter z) : ℂ)*Q r=0)
    (hC : (((2*(star (radialShootingFreeExterior z r)*deriv (radialShootingFreeExterior z) r).re : ℝ) : ℂ)+
        σ*Complex.I*(radialMatchedFreeTransportFunction z r : ℂ))*Q r=
      (radialMatchedFreeMassFunction z r : ℂ)*(2*deriv Q r+σ*Complex.I*(r : ℂ)/2*Q r)) :
    HasDerivAt (spectralFluxGaugeJet Q σ U)
      (spectralFreePhysicalField σ (radialShootingB (profileMatchingParameter z)) ζ
        ((ell : ℂ)*((ell : ℂ)+10)) r (spectralFluxGaugeJet Q σ U r) + (0,-σ*Complex.I*(spectralFluxGaugeJet Q σ U₀ r).1)) r := by
  have hL : 0 < radialShootingR (profileMatchingParameter z) :=
    lt_of_lt_of_le (by norm_num) (radialShooting_geometry (profileMatchingParameter z)).2.1
  have hr0 := hL.trans hr.1
  have hpos (t : ℝ) (ht : t ∈ Ioo (radialShootingR (profileMatchingParameter z)) R) :
      radialMatchedFreeMassFunction z t ≠ 0 :=
    (radialMatchedFreeMass_pos z t (hL.trans ht.1).le).ne'
  exact spectralFluxChainGauge_hasDerivAt ell σ (radialShootingB (profileMatchingParameter z)) ζ hσ
    (radialMatchedFreeMassFunction z) (radialMatchedFreeTransportFunction z) Q U₀ U _ R hL r
    (2*(star (radialShootingFreeExterior z r)*deriv (radialShootingFreeExterior z) r).re)
    hr hpos hU
    (((radialMatchedFreeFluxChain_contDiffOn ell z hz₁ hz hc R ζ U₀ U hU₀ hU) r hr).contDiffAt
      (isOpen_Ioo.mem_nhds hr))
    (radialMatchedFreeMass_hasDerivAt z hz₁ hz r hr.1)
    (radialMatchedFreeTransport_hasDerivAt z hc r hr0.ne') hQ hDQ hQE hC

theorem radialMatchedFreeFluxChain_gauge_positive (ell : ℕ) (z : ProfileMatchingBall)
    (hz₁ : z.val.1=0) (hz : diskProfile (profileMatchingParameter z)=0)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (R : ℝ) (ζ : ℂ) (U₀ U : ℝ → E₄)
    (hU₀ : ∀ r ∈ Ioo (radialShootingR (profileMatchingParameter z)) R,
      HasDerivAt U₀ (spectralFluxField ell (radialMatchedFreeMassFunction z r)
        (radialMatchedFreeTransportFunction z r) 6 ζ r (U₀ r)) r)
    (hU : ∀ r ∈ Ioo (radialShootingR (profileMatchingParameter z)) R,
      HasDerivAt U (spectralFluxField ell (radialMatchedFreeMassFunction z r)
        (radialMatchedFreeTransportFunction z r) 6 ζ r (U r) +
        spectralFluxFieldSlope (radialMatchedFreeMassFunction z r) r (U₀ r)) r)
    (r : ℝ) (hr : r ∈ Ioo (radialShootingR (profileMatchingParameter z)) R) :
    HasDerivAt (spectralFluxGaugeJet (radialShootingFreeExterior z) 1 U)
      (spectralFreePhysicalField 1 (radialShootingB (profileMatchingParameter z)) ζ
        ((ell : ℂ)*((ell : ℂ)+10)) r
        (spectralFluxGaugeJet (radialShootingFreeExterior z) 1 U r) +
        (0,-(1 : ℂ)*Complex.I*(spectralFluxGaugeJet (radialShootingFreeExterior z) 1 U₀ r).1)) r := by
  have hr0 : 0 < r := lt_trans
    (by linarith [(radialShooting_geometry (profileMatchingParameter z)).2.1]) hr.1
  apply fluxChainGauge_at ell z hz₁ hz hc R ζ 1 (by simp) U₀ U hU₀ hU _ r hr
    (radialShootingFreeExterior_hasDerivAt z r hr0).differentiableAt
    (radialShootingFreeExterior_hasDerivAt_deriv z r hr0).differentiableAt
  · simpa only [one_mul] using radialShootingFreeExterior_equation z r hr0
  · simpa only [one_mul,Complex.ofReal_div,Complex.ofReal_ofNat,mul_div_assoc] using
      radialMatchedFreeGaugeCoefficient z hz₁ hz hc r hr.1.le

theorem radialMatchedFreeFluxChain_gauge_negative (ell : ℕ) (z : ProfileMatchingBall)
    (hz₁ : z.val.1=0) (hz : diskProfile (profileMatchingParameter z)=0)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (R : ℝ) (ζ : ℂ) (U₀ U : ℝ → E₄)
    (hU₀ : ∀ r ∈ Ioo (radialShootingR (profileMatchingParameter z)) R,
      HasDerivAt U₀ (spectralFluxField ell (radialMatchedFreeMassFunction z r)
        (radialMatchedFreeTransportFunction z r) 6 ζ r (U₀ r)) r)
    (hU : ∀ r ∈ Ioo (radialShootingR (profileMatchingParameter z)) R,
      HasDerivAt U (spectralFluxField ell (radialMatchedFreeMassFunction z r)
        (radialMatchedFreeTransportFunction z r) 6 ζ r (U r) +
        spectralFluxFieldSlope (radialMatchedFreeMassFunction z r) r (U₀ r)) r)
    (r : ℝ) (hr : r ∈ Ioo (radialShootingR (profileMatchingParameter z)) R) :
    HasDerivAt (spectralFluxGaugeJet (fun t => star (radialShootingFreeExterior z t)) (-1) U)
      (spectralFreePhysicalField (-1) (radialShootingB (profileMatchingParameter z)) ζ
        ((ell : ℂ)*((ell : ℂ)+10)) r
        (spectralFluxGaugeJet (fun t => star (radialShootingFreeExterior z t)) (-1) U r) +
        (0,-(-1 : ℂ)*Complex.I*(spectralFluxGaugeJet (fun t => star (radialShootingFreeExterior z t)) (-1) U₀ r).1)) r := by
  have hr0 : 0 < r := lt_trans
    (by linarith [(radialShooting_geometry (profileMatchingParameter z)).2.1]) hr.1
  apply fluxChainGauge_at ell z hz₁ hz hc R ζ (-1) (by norm_num) U₀ U hU₀ hU _ r hr
    (radialShootingFreeExterior_hasDerivAt z r hr0).star.differentiableAt
  · rw [deriv.star']
    exact (radialShootingFreeExterior_hasDerivAt_deriv z r hr0).star.differentiableAt
  · simpa only [neg_mul,one_mul,sub_eq_add_neg,neg_div] using
      radialShootingFreeConjugate_equation z r hr0
  · simpa only [deriv.star',neg_mul,one_mul,sub_eq_add_neg,neg_div,Complex.ofReal_div,
      Complex.ofReal_ofNat,mul_div_assoc] using
      radialMatchedFreeConjugateGaugeCoefficient z hz₁ hz hc r hr.1.le

end DefocusingNLS

end OAI
