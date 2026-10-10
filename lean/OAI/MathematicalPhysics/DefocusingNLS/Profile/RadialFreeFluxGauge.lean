import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFluxCircular
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFluxLocalSmoothness
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeConjugate

namespace OAI

/-! The actual limiting flux system gives the two decoupled free physical equations. -/

open Set
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

noncomputable def spectralFluxGaugeJet (Q : ℝ → ℂ) (σ : ℂ) (U : ℝ → E₄) (r : ℝ) : ℂ × ℂ :=
  (Q r*spectralFluxCircularValue σ U r,
   deriv Q r*spectralFluxCircularValue σ U r+Q r*deriv (spectralFluxCircularValue σ U) r)

noncomputable def spectralFreePhysicalField (σ b ζ η : ℂ) (r : ℝ) (V : ℂ × ℂ) : ℂ × ℂ :=
  (V.2,-(11/(r : ℂ)+σ*Complex.I*(r : ℂ)/2)*V.2-
    (b+σ*Complex.I*ζ-η/(r : ℂ)^2)*V.1)

private theorem fluxGauge_at (ell : ℕ) (z : ProfileMatchingBall)
    (hz₁ : z.val.1=0) (hz : diskProfile (profileMatchingParameter z)=0)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (R : ℝ) (ζ σ : ℂ) (hσ : σ^2=1)
    (U : ℝ → E₄)
    (hU : ∀ r ∈ Ioo (radialShootingR (profileMatchingParameter z)) R,
      HasDerivAt U (spectralFluxField ell (radialMatchedFreeMassFunction z r)
        (radialMatchedFreeTransportFunction z r) 6 ζ r (U r)) r)
    (Q : ℝ → ℂ) (r : ℝ) (hr : r ∈ Ioo (radialShootingR (profileMatchingParameter z)) R)
    (hQ : DifferentiableAt ℝ Q r) (hDQ : DifferentiableAt ℝ (deriv Q) r)
    (hQE : deriv (deriv Q) r+(11/(r : ℂ)+σ*Complex.I*(r : ℂ)/2)*deriv Q r+
      (radialShootingB (profileMatchingParameter z) : ℂ)*Q r=0)
    (hC : (((2*(star (radialShootingFreeExterior z r)*deriv (radialShootingFreeExterior z) r).re : ℝ) : ℂ)+
        σ*Complex.I*(radialMatchedFreeTransportFunction z r : ℂ))*Q r=
      (radialMatchedFreeMassFunction z r : ℂ)*(2*deriv Q r+σ*Complex.I*(r : ℂ)/2*Q r)) :
    HasDerivAt (spectralFluxGaugeJet Q σ U)
      (spectralFreePhysicalField σ (radialShootingB (profileMatchingParameter z)) ζ
        ((ell : ℂ)*((ell : ℂ)+10)) r (spectralFluxGaugeJet Q σ U r)) r := by
  let V := spectralFluxCircularValue σ U
  have hL : 0 < radialShootingR (profileMatchingParameter z) :=
    lt_of_lt_of_le (by norm_num) (radialShooting_geometry (profileMatchingParameter z)).2.1
  have hr0 := hL.trans hr.1
  have hpos (t : ℝ) (ht : t ∈ Ioo (radialShootingR (profileMatchingParameter z)) R) :
      radialMatchedFreeMassFunction z t ≠ 0 :=
    (radialMatchedFreeMass_pos z t (hL.trans ht.1).le).ne'
  have hs := ((radialMatchedFreeFlux_contDiffOn ell z hz₁ hz hc R ζ U hU) r hr).contDiffAt
    (isOpen_Ioo.mem_nhds hr)
  have hf : ContDiffAt ℝ ∞ (fun t => (U t).1.1) r := hs.fst.fst
  have hg : ContDiffAt ℝ ∞ (fun t => (U t).1.2) r := hs.fst.snd
  have hV : ContDiffAt ℝ ∞ V r := hf.add (contDiffAt_const.mul hg)
  have hVd := hV.differentiableAt (by simp)
  have hDV := (hV.derivWithin (m := 1) (by simp)).differentiableAt (by simp)
  exact spectralFreeGaugeJet_hasDerivAt σ (radialShootingB (profileMatchingParameter z)) ζ
    ((ell : ℂ)*((ell : ℂ)+10)) (radialMatchedFreeMassFunction z)
    (radialMatchedFreeTransportFunction z) Q V r
    (2*(star (radialShootingFreeExterior z r)*deriv (radialShootingFreeExterior z) r).re)
    hr0.ne' (hpos r hr) (radialMatchedFreeMass_hasDerivAt z hz₁ hz r hr.1)
    (radialMatchedFreeTransport_hasDerivAt z hc r hr0.ne') hQ hDQ hVd hDV hQE hC
    (spectralFluxCircular_hasDerivAt ell σ ζ hσ _ _ U _ R hL hpos hU r hr)

theorem radialMatchedFreeFlux_gauge_positive (ell : ℕ) (z : ProfileMatchingBall)
    (hz₁ : z.val.1=0) (hz : diskProfile (profileMatchingParameter z)=0)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (R : ℝ) (ζ : ℂ) (U : ℝ → E₄)
    (hU : ∀ r ∈ Ioo (radialShootingR (profileMatchingParameter z)) R,
      HasDerivAt U (spectralFluxField ell (radialMatchedFreeMassFunction z r)
        (radialMatchedFreeTransportFunction z r) 6 ζ r (U r)) r)
    (r : ℝ) (hr : r ∈ Ioo (radialShootingR (profileMatchingParameter z)) R) :
    HasDerivAt (spectralFluxGaugeJet (radialShootingFreeExterior z) 1 U)
      (spectralFreePhysicalField 1 (radialShootingB (profileMatchingParameter z)) ζ
        ((ell : ℂ)*((ell : ℂ)+10)) r
        (spectralFluxGaugeJet (radialShootingFreeExterior z) 1 U r)) r := by
  have hr0 : 0 < r := lt_trans
    (by linarith [(radialShooting_geometry (profileMatchingParameter z)).2.1]) hr.1
  apply fluxGauge_at ell z hz₁ hz hc R ζ 1 (by simp) U hU _ r hr
    (radialShootingFreeExterior_hasDerivAt z r hr0).differentiableAt
    (radialShootingFreeExterior_hasDerivAt_deriv z r hr0).differentiableAt
  · simpa only [one_mul] using radialShootingFreeExterior_equation z r hr0
  · simpa only [one_mul,Complex.ofReal_div,Complex.ofReal_ofNat,mul_div_assoc] using
      radialMatchedFreeGaugeCoefficient z hz₁ hz hc r hr.1.le

theorem radialMatchedFreeFlux_gauge_negative (ell : ℕ) (z : ProfileMatchingBall)
    (hz₁ : z.val.1=0) (hz : diskProfile (profileMatchingParameter z)=0)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (R : ℝ) (ζ : ℂ) (U : ℝ → E₄)
    (hU : ∀ r ∈ Ioo (radialShootingR (profileMatchingParameter z)) R,
      HasDerivAt U (spectralFluxField ell (radialMatchedFreeMassFunction z r)
        (radialMatchedFreeTransportFunction z r) 6 ζ r (U r)) r)
    (r : ℝ) (hr : r ∈ Ioo (radialShootingR (profileMatchingParameter z)) R) :
    HasDerivAt (spectralFluxGaugeJet (fun t => star (radialShootingFreeExterior z t)) (-1) U)
      (spectralFreePhysicalField (-1) (radialShootingB (profileMatchingParameter z)) ζ
        ((ell : ℂ)*((ell : ℂ)+10)) r
        (spectralFluxGaugeJet (fun t => star (radialShootingFreeExterior z t)) (-1) U r)) r := by
  have hr0 : 0 < r := lt_trans
    (by linarith [(radialShooting_geometry (profileMatchingParameter z)).2.1]) hr.1
  apply fluxGauge_at ell z hz₁ hz hc R ζ (-1) (by norm_num) U hU _ r hr
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
