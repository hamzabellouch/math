import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarFlux
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralShellPositiveForm
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalLiouvillePair

namespace OAI

/-! Hermitian cancellation of the two forcing terms in the physical
Liouville flux identity. -/

namespace DefocusingNLS

theorem spectralScalarForcedFlux_hasDerivAt (q : ℝ → ℂ × ℂ) (V F : ℂ) (r : ℝ)
    (hq : HasDerivAt q (spectralScalarField V (q r)+(0,F)) r) :
    HasDerivAt (fun t => spectralScalarFlux (q t))
      (-V.im*Complex.normSq (q r).1+(star (q r).1*F).im) r := by
  have h1 := (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt r hq
  have h2 := (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt r hq
  have hd := Complex.imCLM.hasFDerivAt.comp_hasDerivAt r (h1.star.mul h2)
  simp only [ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',Function.comp_apply,
    spectralScalarField,Prod.fst_add,Prod.snd_add,add_zero] at hd
  apply hd.congr_deriv
  change (star (q r).2*(q r).2+star (q r).1*(-V*(q r).1+F)).im = _
  simp only [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    Complex.neg_re,Complex.neg_im,Complex.star_def,Complex.conj_re,Complex.conj_im,Complex.normSq_apply]
  ring

theorem spectralLiouville_phase_star (h r : ℝ) (hr : 0 < r) :
    star (homogeneousSpectralLocalizationFactor h r/homogeneousSpectralLocalizationFactor (-h) r) =
      homogeneousSpectralLocalizationFactor (-h) r/homogeneousSpectralLocalizationFactor h r := by
  rw [Complex.star_def,← Complex.inv_eq_conj (homogeneousSpectralLocalization_phase_norm h r hr)]
  exact inv_div _ _

theorem spectralShellForcing_flux_zero (m : ℕ) (Q : ℂ) (r : ℝ) (hr : 0 < r)
    (u : (ℂ × ℂ) × (ℂ × ℂ)) :
    (star u.1.1*spectralShellPlusForcing m Q r u).im+
      (star u.2.1*spectralShellMinusForcing m Q r u).im = 0 := by
  let C := spectralCrossCoefficient m Q*(homogeneousSpectralLocalizationFactor 1 r/
      homogeneousSpectralLocalizationFactor (-1) r)
  have hC : star (spectralCrossCoefficient m Q)*
      (homogeneousSpectralLocalizationFactor (-1) r/homogeneousSpectralLocalizationFactor 1 r) = star C := by
    simp only [C,star_mul,spectralLiouville_phase_star 1 r hr]
    ring
  rw [spectralShellPlusForcing,spectralShellMinusForcing,hC,spectralDiagonalCoefficient_real]
  change (star u.1.1*(((((m : ℝ)+1)*‖Q‖^(2*m) : ℝ) : ℂ)*u.1.1+C*u.2.1)).im+
    (star u.2.1*(star (((((m : ℝ)+1)*‖Q‖^(2*m) : ℝ) : ℂ))*u.2.1+star C*u.1.1)).im = 0
  simp only [Complex.star_def,Complex.conj_ofReal,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.conj_re,Complex.conj_im]
  ring

theorem spectralPhysicalLiouvillePair_flux_hasDerivAt
    (a b eta : ℝ) (m : ℕ) (Q : ℝ → ℂ) (lam : ℂ) (f g : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (he : IsHarmonicRadialEigenpair a b m Q (eta : ℂ) lam f g)
    (r : ℝ) (hr : 0 < r) :
    let q := spectralPhysicalLiouvillePair f g
    HasDerivAt (fun t => spectralScalarFlux (q t).1+spectralScalarFlux (q t).2)
      ((a+lam.re-3)*(Complex.normSq (q r).2.1-Complex.normSq (q r).1.1)) r := by
  intro q
  obtain ⟨hp,hm⟩ := spectralPhysicalLiouvillePair_equation a b eta m Q lam f g hf hg he r hr
  have hd := (spectralScalarForcedFlux_hasDerivAt _ _ _ r hp).add
    (spectralScalarForcedFlux_hasDerivAt _ _ _ r hm)
  apply hd.congr_deriv
  have hc := spectralShellForcing_flux_zero m (Q r) r hr (q r)
  simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,Complex.I_im,
    Complex.ofReal_re,zero_mul,one_mul,zero_add] at *
  linarith

end DefocusingNLS

end OAI
