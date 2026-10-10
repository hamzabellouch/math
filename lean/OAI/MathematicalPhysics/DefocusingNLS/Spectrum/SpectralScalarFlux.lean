import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarGreen

namespace OAI

/-! The scalar flux is conserved by the limiting real Airy equation.
Its derivative for a complex coefficient is computed exactly. -/

open Set MeasureTheory
namespace DefocusingNLS

noncomputable def spectralScalarFlux (q : ℂ × ℂ) : ℝ := (star q.1*q.2).im

theorem spectralScalarFlux_hasDerivAt (q : ℝ → ℂ × ℂ) (V : ℂ) (r : ℝ)
    (hq : HasDerivAt q (spectralScalarField V (q r)) r) :
    HasDerivAt (fun t => spectralScalarFlux (q t)) (-V.im*Complex.normSq (q r).1) r := by
  have h1 := (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt r hq
  have h2 := (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt r hq
  apply (Complex.imCLM.hasFDerivAt.comp_hasDerivAt r (h1.star.mul h2)).congr_deriv
  change (star (q r).2*(q r).2+star (q r).1*(-V*(q r).1)).im= -V.im*Complex.normSq (q r).1
  simp only [Complex.add_im,Complex.mul_im,Complex.mul_re,Complex.neg_re,Complex.neg_im,
    Complex.star_def,Complex.conj_re,Complex.conj_im,Complex.normSq_apply]
  ring

theorem spectralScalarFlux_const (a b : ℝ) (q : ℝ → ℂ × ℂ) (V : ℝ → ℝ)
    (hq : ContinuousOn q (Icc a b))
    (hD : ∀ t ∈ Ioo a b, HasDerivAt q (spectralScalarField (V t) (q t)) t)
    (r : ℝ) (hr : r ∈ Icc a b) : spectralScalarFlux (q r)=spectralScalarFlux (q a) := by
  have hc : ContinuousOn (fun t => spectralScalarFlux (q t)) (Icc a b) :=
    Complex.continuous_im.comp_continuousOn (hq.fst.star.mul hq.snd)
  have hd (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt (fun s => spectralScalarFlux (q s)) 0 t := by
    simpa only [Complex.ofReal_im,neg_zero,zero_mul] using
      spectralScalarFlux_hasDerivAt q (V t) t (hD t ht)
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hr.1
    (hc.mono (Icc_subset_Icc le_rfl hr.2))
    (fun t ht => hd t ⟨ht.1,ht.2.trans_le hr.2⟩)
    (continuous_const.intervalIntegrable a r)
  rw [intervalIntegral.integral_zero] at hh
  exact sub_eq_zero.mp hh.symm

theorem spectralScalarFlux_ne_zero_value (q : ℂ × ℂ) (hJ : spectralScalarFlux q≠0) : q.1≠0 := by
  intro hz
  apply hJ
  simp only [spectralScalarFlux,hz,star_zero,zero_mul,Complex.zero_im]

end DefocusingNLS

end OAI
