import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBWeightedPrimitives

namespace OAI

/-! Integrated WKB error from exact momentum primitives. The constants only
use derivative bounds and the momentum at the near endpoint. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralWKB_residual_integral (a b A B : ℝ) (hab : a≤b)
    (hA : 0≤A) (hB : 0≤B) (p g e : ℝ → ℝ)
    (hp : ContinuousOn p (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (he : ContinuousOn e (Icc a b)) (hp0 : ∀ t ∈ Icc a b, 0<p t)
    (hg0 : ∀ t ∈ Icc a b, 0≤g t) (hgB : ∀ t ∈ Icc a b, g t≤B)
    (heA : ∀ t ∈ Icc a b, |e t|≤A*g t)
    (hD : ∀ t ∈ Ioo a b, HasDerivAt p (g t/(2*p t)) t) :
    (∫ t in a..b, (5/16 : ℝ)*(g t)^2/(p t)^5+|e t|/(4*(p t)^3))≤
      5*B/(24*(p a)^3)+A/(2*p a) := by
  have hpn (t : ℝ) (ht : t ∈ Icc a b) : p t≠0 := (hp0 t ht).ne'
  have hi3 : IntervalIntegrable (fun t => g t/(p t)^3) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab
      (hg.div (hp.pow 3) (fun t ht => pow_ne_zero _ (hpn t ht)))
  have hi5 : IntervalIntegrable (fun t => g t/(p t)^5) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab
      (hg.div (hp.pow 5) (fun t ht => pow_ne_zero _ (hpn t ht)))
  have hif : IntervalIntegrable
      (fun t => (5/16 : ℝ)*(g t)^2/(p t)^5+|e t|/(4*(p t)^3)) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab
      (((continuousOn_const.mul (hg.pow 2)).div (hp.pow 5)
        (fun t ht => pow_ne_zero _ (hpn t ht))).add
        (he.abs.div (continuousOn_const.mul (hp.pow 3))
          (fun t ht => mul_ne_zero (by norm_num) (pow_ne_zero _ (hpn t ht)))))
  have hbound : (∫ t in a..b, (5/16 : ℝ)*(g t)^2/(p t)^5+|e t|/(4*(p t)^3))≤
      (5*B/16)*(∫ t in a..b, g t/(p t)^5)+(A/4)*(∫ t in a..b, g t/(p t)^3) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (hi5.const_mul _) (hi3.const_mul _)]
    apply intervalIntegral.integral_mono_on hab hif
      ((hi5.const_mul _).add (hi3.const_mul _))
    intro t ht
    have hp5 : 0≤(p t)^5 := (pow_pos (hp0 t ht) _).le
    have hp3 : 0≤(p t)^3 := (pow_pos (hp0 t ht) _).le
    have hb : (g t)^2≤B*g t := by nlinarith [hg0 t ht,hgB t ht]
    have h1 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ)≤5/16)) hp5
    have h2 := div_le_div_of_nonneg_right (heA t ht)
      (mul_nonneg (by norm_num : (0 : ℝ)≤4) hp3)
    convert add_le_add h1 h2 using 1
    ring
  rw [spectralWKB_integral_fifth a b hab p g hp hg hp0 hD,
    spectralWKB_integral_cube a b hab p g hp hg hp0 hD] at hbound
  have hpa : 0<p a := hp0 a ⟨le_rfl,hab⟩
  have hpb : 0<p b := hp0 b ⟨hab,le_rfl⟩
  have h3 : 0≤2/(3*(p b)^3) := by positivity
  have h1 : 0≤2/p b := by positivity
  have hdrop3 := mul_nonneg (show 0≤5*B/16 by positivity) h3
  have hdrop1 := mul_nonneg (show 0≤A/4 by positivity) h1
  calc
    _ ≤ (5*B/16)*(2/(3*(p a)^3)-2/(3*(p b)^3))+(A/4)*(2/p a-2/p b) := hbound
    _ ≤ (5*B/16)*(2/(3*(p a)^3))+(A/4)*(2/p a) := by nlinarith
    _ = _ := by ring

end DefocusingNLS

end OAI
