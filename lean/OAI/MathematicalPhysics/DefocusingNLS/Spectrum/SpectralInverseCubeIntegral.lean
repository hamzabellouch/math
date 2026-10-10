import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBWeightedPrimitives

namespace OAI

/-! Exact inverse-cubic integration for the far oscillatory error. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectral_inverse_cube_integral (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    (∫ t in a..b, 1/t^3)=1/(2*a^2)-1/(2*b^2) := by
  let A := fun t : ℝ => (-1/2)*(t^2)⁻¹
  have hp (t : ℝ) (ht : t ∈ Icc a b) : t≠0 := (ha.trans_le ht.1).ne'
  have hAc : ContinuousOn A (Icc a b) :=
    continuousOn_const.mul ((continuousOn_id.pow 2).inv₀ (fun t ht => pow_ne_zero _ (hp t ht)))
  have hAd (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt A (1/t^3) t := by
    apply (((hasDerivAt_id t).pow 2).inv (pow_ne_zero _ (hp t ⟨ht.1.le,ht.2.le⟩)) |>.const_mul (-1/2)).congr_deriv
    simp only [Pi.pow_apply,id_eq]
    field_simp [hp t ⟨ht.1.le,ht.2.le⟩]
    ring
  have hi : IntervalIntegrable (fun t => 1/t^3) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab
      (continuousOn_const.div (continuousOn_id.pow 3) (fun t ht => pow_ne_zero _ (hp t ht)))
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hAc hAd hi
  dsimp only [A] at he
  calc
    _ = (-1/2)*(b^2)⁻¹-(-1/2)*(a^2)⁻¹ := he
    _ = _ := by ring

theorem spectral_inverse_cube_bound (a b : ℝ) (ha : 0<a) (hab : a≤b)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc a b))
    (hbound : ∀ t ∈ Icc a b, f t≤64/t^3) :
    (∫ t in a..b, f t)≤32/a^2 := by
  have hp (t : ℝ) (ht : t ∈ Icc a b) : t≠0 := (ha.trans_le ht.1).ne'
  have hi : IntervalIntegrable (fun t => 64/t^3) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab
      (continuousOn_const.div (continuousOn_id.pow 3) (fun t ht => pow_ne_zero _ (hp t ht)))
  calc
    _ ≤ ∫ t in a..b, 64/t^3 := intervalIntegral.integral_mono_on hab
      (hf.intervalIntegrable_of_Icc hab) hi hbound
    _ = 64*(1/(2*a^2)-1/(2*b^2)) := by
      rw [show (fun t : ℝ => 64/t^3)=(fun t => 64*(1/t^3)) by funext t; ring,
        intervalIntegral.integral_const_mul,spectral_inverse_cube_integral a b ha hab]
    _ ≤ 32/a^2 := by
      have hb : 0<b := ha.trans_le hab
      have hh : 0≤1/(2*b^2) := by positivity
      calc
        _ ≤ 64*(1/(2*a^2)) := by linarith
        _ = _ := by ring

end DefocusingNLS

end OAI
