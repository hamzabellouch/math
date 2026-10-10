import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarUniqueness

namespace OAI

/-! A nonzero scalar Cauchy solution cannot vanish at an earlier point. -/

open Set
namespace DefocusingNLS

theorem spectralScalar_ne_zero_of_right (a b : ℝ) (hab : a ≤ b)
    (V : ℝ → ℂ) (hV : ContinuousOn V (Icc a b)) (q : ℝ → ℂ × ℂ)
    (hq : ContinuousOn q (Icc a b))
    (hD : ∀ t ∈ Ioo a b, HasDerivAt q (spectralScalarField (V t) (q t)) t)
    (hb : q b ≠ 0) : q a ≠ 0 := by
  intro ha
  have he := spectralScalar_unique_right a b hab V hV q (fun _ => 0) hq continuousOn_const
    hD (fun t _ => by simpa only [spectralScalarField,Prod.fst_zero,Prod.snd_zero,mul_zero,neg_zero,
      Prod.mk_zero_zero] using hasDerivAt_const t (0 : ℂ × ℂ)) ha
  exact hb he

end DefocusingNLS

end OAI
