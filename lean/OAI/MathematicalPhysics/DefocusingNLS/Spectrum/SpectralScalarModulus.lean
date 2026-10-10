import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarFlux

namespace OAI

/-! Exact real identities behind the forbidden-side Airy growth argument. -/

namespace DefocusingNLS

noncomputable def spectralScalarMass (q : ℂ × ℂ) : ℝ := Complex.normSq q.1
noncomputable def spectralScalarMomentum (q : ℂ × ℂ) : ℝ := (star q.1*q.2).re

theorem spectralScalarFlux_identity (q : ℂ × ℂ) :
    spectralScalarMass q*Complex.normSq q.2=
      (spectralScalarMomentum q)^2+(spectralScalarFlux q)^2 := by
  dsimp only [spectralScalarMass,spectralScalarMomentum,spectralScalarFlux]
  simp only [Complex.star_def,Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im,
    Complex.normSq_apply]
  ring

theorem spectralScalarMass_hasDerivAt (q : ℝ → ℂ × ℂ) (V : ℂ) (r : ℝ)
    (hq : HasDerivAt q (spectralScalarField V (q r)) r) :
    HasDerivAt (fun t => spectralScalarMass (q t)) (2*spectralScalarMomentum (q r)) r := by
  have h1 := (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt r hq
  have hh := Complex.reCLM.hasFDerivAt.comp_hasDerivAt r (h1.star.mul h1)
  have heq : (fun t => (star (q t).1*(q t).1).re)=(fun t => spectralScalarMass (q t)) := by
    funext t
    dsimp only [spectralScalarMass]
    simp only [Complex.star_def,Complex.mul_re,Complex.conj_re,Complex.conj_im,Complex.normSq_apply]
    ring
  change HasDerivAt (fun t => (star (q t).1*(q t).1).re) _ r at hh
  rw [heq] at hh
  apply hh.congr_deriv
  change (star (q r).2*(q r).1+star (q r).1*(q r).2).re=2*spectralScalarMomentum (q r)
  simp only [spectralScalarMomentum,Complex.add_re,Complex.mul_re,Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

theorem spectralScalarMomentum_hasDerivAt (q : ℝ → ℂ × ℂ) (V : ℂ) (r : ℝ)
    (hq : HasDerivAt q (spectralScalarField V (q r)) r) :
    HasDerivAt (fun t => spectralScalarMomentum (q t))
      (Complex.normSq (q r).2-V.re*spectralScalarMass (q r)) r := by
  have h1 := (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt r hq
  have h2 := (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt r hq
  apply (Complex.reCLM.hasFDerivAt.comp_hasDerivAt r (h1.star.mul h2)).congr_deriv
  change (star (q r).2*(q r).2+star (q r).1*(-V*(q r).1)).re=
    Complex.normSq (q r).2-V.re*spectralScalarMass (q r)
  simp only [spectralScalarMass,Complex.add_re,Complex.mul_re,Complex.mul_im,
    Complex.neg_re,Complex.neg_im,Complex.star_def,Complex.conj_re,Complex.conj_im,Complex.normSq_apply]
  ring

end DefocusingNLS

end OAI
