import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralAiryMomentum
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace OAI

/-! The logarithmic modulus slope of a nonzero-flux Airy solution satisfies
an exact scalar Riccati equation. -/

namespace DefocusingNLS

noncomputable def spectralAirySlope (q : ℝ → ℂ × ℂ) (t : ℝ) : ℝ :=
  spectralScalarMomentum (q t)/(Real.sqrt t*spectralScalarMass (q t))

private theorem slope_algebra (P Q D J s t : ℝ) (hQ : Q≠0) (hs : s≠0)
    (hst : s^2=t) (hrel : Q*D=P^2+J^2) :
    ((D+t*Q)*(s*Q)-P*((2*s)⁻¹*Q+s*(2*P)))/(s*Q)^2=
      s*(1-(P/(s*Q))^2)-(P/(s*Q))/(2*t)+J^2/(s*Q^2) := by
  rw [← hst]
  field_simp
  linear_combination 2*s^2*hrel

theorem spectralAirySlope_hasDerivAt (q : ℝ → ℂ × ℂ) (t : ℝ) (ht : 0<t)
    (hq : HasDerivAt q (spectralScalarField (-(t : ℂ)) (q t)) t)
    (hQ : spectralScalarMass (q t)≠0) :
    HasDerivAt (spectralAirySlope q)
      (Real.sqrt t*(1-(spectralAirySlope q t)^2)-spectralAirySlope q t/(2*t)+
        (spectralScalarFlux (q t))^2/(Real.sqrt t*(spectralScalarMass (q t))^2)) t := by
  have hs : Real.sqrt t≠0 := (Real.sqrt_pos.mpr ht).ne'
  have hP : HasDerivAt (fun s => spectralScalarMomentum (q s))
      (Complex.normSq (q t).2+t*spectralScalarMass (q t)) t := by
    simpa only [Complex.neg_re,Complex.ofReal_re,neg_mul,sub_neg_eq_add] using
      spectralScalarMomentum_hasDerivAt q (-(t : ℂ)) t hq
  have hM := spectralScalarMass_hasDerivAt q (-(t : ℂ)) t hq
  have hden := (Real.hasDerivAt_sqrt ht.ne').mul hM
  have hd := hP.div hden (mul_ne_zero hs hQ)
  apply hd.congr_deriv
  simpa only [Pi.mul_apply,spectralAirySlope,one_div] using
    slope_algebra _ _ _ _ _ _ hQ hs (Real.sq_sqrt ht.le) (spectralScalarFlux_identity (q t))

end DefocusingNLS

end OAI
