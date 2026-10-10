import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBResidualIntegral

namespace OAI

/-! Reflection gives the endpoint form for decreasing momentum, as used on
 the forbidden side of a turning point. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralWKB_decreasing_residual_integral (a b A B : ℝ) (hab : a≤b)
    (hA : 0≤A) (hB : 0≤B) (p g e : ℝ → ℝ)
    (hp : ContinuousOn p (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (he : ContinuousOn e (Icc a b)) (hp0 : ∀ t ∈ Icc a b, 0<p t)
    (hg0 : ∀ t ∈ Icc a b, 0≤g t) (hgB : ∀ t ∈ Icc a b, g t≤B)
    (heA : ∀ t ∈ Icc a b, |e t|≤A*g t)
    (hD : ∀ t ∈ Ioo a b, HasDerivAt p (-(g t/(2*p t))) t) :
    (∫ t in a..b, (5/16 : ℝ)*(g t)^2/(p t)^5+|e t|/(4*(p t)^3))≤
      5*B/(24*(p b)^3)+A/(2*p b) := by
  let R := fun t : ℝ => a+b-t
  have hR : ContinuousOn R (Icc a b) := (continuous_const.sub continuous_id).continuousOn
  have hmaps : MapsTo R (Icc a b) (Icc a b) := by
    intro t ht
    dsimp only [R]
    constructor <;> linarith [ht.1,ht.2]
  have hmapsO (t : ℝ) (ht : t ∈ Ioo a b) : R t ∈ Ioo a b := by
    dsimp only [R]
    constructor <;> linarith [ht.1,ht.2]
  have hD' (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt (fun t => p (R t)) (g (R t)/(2*p (R t))) t := by
    have hh := (hD (R t) (hmapsO t ht)).comp t ((hasDerivAt_id t).const_sub (a+b))
    apply hh.congr_deriv
    ring
  have hb := spectralWKB_residual_integral a b A B hab hA hB
    (fun t => p (R t)) (fun t => g (R t)) (fun t => e (R t))
    (hp.comp hR hmaps) (hg.comp hR hmaps) (he.comp hR hmaps)
    (fun t ht => hp0 (R t) (hmaps ht)) (fun t ht => hg0 (R t) (hmaps ht))
    (fun t ht => hgB (R t) (hmaps ht)) (fun t ht => heA (R t) (hmaps ht)) hD'
  dsimp only [R] at hb
  have hi := intervalIntegral.integral_comp_sub_left
    (fun t => (5/16 : ℝ)*(g t)^2/(p t)^5+|e t|/(4*(p t)^3)) (a+b) (a := a) (b := b)
  rw [hi] at hb
  simpa only [add_sub_cancel_right,add_sub_cancel_left] using hb

end DefocusingNLS

end OAI
