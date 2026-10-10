import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarModulus
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralShellPositiveForm
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalLiouvillePair

namespace OAI

/-! The real momentum identity for the actual forced scalar pair. -/

namespace DefocusingNLS

theorem spectralScalarForcedMomentum_hasDerivAt (q : ℝ → ℂ × ℂ) (V F : ℂ) (r : ℝ)
    (hq : HasDerivAt q (spectralScalarField V (q r)+(0,F)) r) :
    HasDerivAt (fun t => spectralScalarMomentum (q t))
      (Complex.normSq (q r).2-V.re*spectralScalarMass (q r)+(star (q r).1*F).re) r := by
  have h1 := (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt r hq
  have h2 := (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt r hq
  have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt r (h1.star.mul h2)
  simp only [ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',Function.comp_apply,
    spectralScalarField,Prod.fst_add,Prod.snd_add,add_zero] at hd
  apply hd.congr_deriv
  change (star (q r).2*(q r).2+star (q r).1*(-V*(q r).1+F)).re = _
  simp only [spectralScalarMass,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    Complex.neg_re,Complex.neg_im,Complex.star_def,Complex.conj_re,Complex.conj_im,Complex.normSq_apply]
  ring

noncomputable def spectralPairMomentum (q : (ℂ × ℂ) × (ℂ × ℂ)) : ℝ :=
  spectralScalarMomentum q.1+spectralScalarMomentum q.2

theorem spectralPhysicalLiouvillePair_momentum_differentiableAt
    (a b eta : ℝ) (m : ℕ) (Q : ℝ → ℂ) (lam : ℂ) (f g : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (he : IsHarmonicRadialEigenpair a b m Q (eta : ℂ) lam f g)
    (r : ℝ) (hr : 0 < r) :
    DifferentiableAt ℝ (fun t => spectralPairMomentum (spectralPhysicalLiouvillePair f g t)) r := by
  obtain ⟨hp,hm⟩ := spectralPhysicalLiouvillePair_equation a b eta m Q lam f g hf hg he r hr
  exact ((spectralScalarForcedMomentum_hasDerivAt _ _ _ r hp).add
    (spectralScalarForcedMomentum_hasDerivAt _ _ _ r hm)).differentiableAt

theorem spectralPhysicalLiouvillePair_momentum_deriv
    (a b eta : ℝ) (m : ℕ) (hm : 1 ≤ m) (Q : ℝ → ℂ) (lam : ℂ) (f g : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (he : IsHarmonicRadialEigenpair a b m Q (eta : ℂ) lam f g)
    (r : ℝ) (hr : 0 < r)
    (hp : homogeneousSpectralLocalizationFrequency 1 b eta lam.im r ≤ 0)
    (hn : homogeneousSpectralLocalizationFrequency (-1) b eta lam.im r ≤ 0) :
    0 ≤ deriv (fun t => spectralPairMomentum (spectralPhysicalLiouvillePair f g t)) r := by
  let q := spectralPhysicalLiouvillePair f g
  obtain ⟨hqp,hqm⟩ := spectralPhysicalLiouvillePair_equation a b eta m Q lam f g hf hg he r hr
  have hd := (spectralScalarForcedMomentum_hasDerivAt (fun t => (q t).1) _ _ r hqp).add
    (spectralScalarForcedMomentum_hasDerivAt (fun t => (q t).2) _ _ r hqm)
  change 0 ≤ deriv ((fun t => spectralScalarMomentum (q t).1)+
    (fun t => spectralScalarMomentum (q t).2)) r
  rw [hd.deriv]
  have hpos := spectralShellForcing_nonnegative m hm (Q r) r hr (q r)
  have hp0 := mul_nonneg (neg_nonneg.mpr hp) (Complex.normSq_nonneg (q r).1.1)
  have hn0 := mul_nonneg (neg_nonneg.mpr hn) (Complex.normSq_nonneg (q r).2.1)
  have hd1 := Complex.normSq_nonneg (q r).1.2
  have hd2 := Complex.normSq_nonneg (q r).2.2
  simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,Complex.I_im,
    Complex.ofReal_im,mul_zero,zero_mul,sub_zero,add_zero,spectralScalarMass] at *
  linarith

end DefocusingNLS

end OAI
