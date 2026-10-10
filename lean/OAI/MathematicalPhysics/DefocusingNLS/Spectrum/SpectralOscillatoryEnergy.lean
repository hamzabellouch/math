import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralForcedMomentum

namespace OAI

/-! Exact oscillator energy for the forced no-turn channel. -/

namespace DefocusingNLS

theorem spectralComplex_normSq_hasDerivAt (f : ℝ → ℂ) (f' : ℂ) (r : ℝ)
    (hf : HasDerivAt f f' r) :
    HasDerivAt (fun t => Complex.normSq (f t)) (2*(star (f r)*f').re) r := by
  have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt r (hf.star.mul hf)
  have he : (fun t => (star (f t)*f t).re) = (fun t => Complex.normSq (f t)) := by
    funext t
    simp only [Complex.star_def,Complex.mul_re,Complex.conj_re,Complex.conj_im,Complex.normSq_apply]
    ring
  change HasDerivAt (fun t => (star (f t)*f t).re) _ r at hd
  rw [he] at hd
  apply hd.congr_deriv
  change (star f'*f r+star (f r)*f').re = _
  simp only [Complex.add_re,Complex.mul_re,Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

noncomputable def spectralOscillatoryEnergy (F : ℝ) (q : ℂ × ℂ) : ℝ :=
  Complex.normSq q.2+F*Complex.normSq q.1

theorem spectralOscillatoryEnergy_hasDerivAt (q : ℝ → ℂ × ℂ) (F : ℝ → ℝ)
    (Fp gamma : ℝ) (forcing : ℂ) (r : ℝ) (hF : HasDerivAt F Fp r)
    (hq : HasDerivAt q (spectralScalarField ((F r : ℂ)+Complex.I*(gamma : ℂ)) (q r)+
      (0,forcing)) r) :
    HasDerivAt (fun t => spectralOscillatoryEnergy (F t) (q t))
      (Fp*Complex.normSq (q r).1-2*gamma*spectralScalarFlux (q r)+
        2*(star (q r).2*forcing).re) r := by
  have h1 := (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt r hq
  have h2 := (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt r hq
  have hN1 := spectralComplex_normSq_hasDerivAt _ _ r h1
  have hN2 := spectralComplex_normSq_hasDerivAt _ _ r h2
  apply (hN2.add (hF.mul hN1)).congr_deriv
  simp only [ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',Function.comp_apply,
    spectralScalarField,Prod.fst_add,Prod.snd_add,add_zero]
  dsimp only [spectralScalarFlux]
  simp only [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,Complex.neg_re,
    Complex.neg_im,Complex.star_def,Complex.conj_re,Complex.conj_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.normSq_apply]
  ring

theorem spectralOscillatoryEnergy_nonneg (F : ℝ) (q : ℂ × ℂ) (hF : 0 ≤ F) :
    0 ≤ spectralOscillatoryEnergy F q :=
  add_nonneg (Complex.normSq_nonneg _) (mul_nonneg hF (Complex.normSq_nonneg _))

end DefocusingNLS

end OAI
