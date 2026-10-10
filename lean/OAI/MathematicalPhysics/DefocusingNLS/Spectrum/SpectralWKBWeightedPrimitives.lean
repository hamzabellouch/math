import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralIntegralGronwall
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace OAI

/-! The two exact weighted primitives used in the outer WKB residual integral. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralWKB_integral_cube (a b : ℝ) (hab : a≤b) (p g : ℝ → ℝ)
    (hp : ContinuousOn p (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hp0 : ∀ t ∈ Icc a b, 0<p t)
    (hD : ∀ t ∈ Ioo a b, HasDerivAt p (g t/(2*p t)) t) :
    (∫ t in a..b, g t/(p t)^3)=2/p a-2/p b := by
  let A := fun t => (-2 : ℝ)*(p t)⁻¹
  have hAc : ContinuousOn A (Icc a b) := continuousOn_const.mul (hp.inv₀ (fun t ht => (hp0 t ht).ne'))
  have hAd (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt A (g t/(p t)^3) t := by
    apply ((hD t ht).inv (hp0 t ⟨ht.1.le,ht.2.le⟩).ne' |>.const_mul (-2)).congr_deriv
    field_simp
  have hi : IntervalIntegrable (fun t => g t/(p t)^3) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab
      (hg.div (hp.pow 3) (fun t ht => pow_ne_zero _ (hp0 t ht).ne'))
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hAc hAd hi
  dsimp only [A] at he
  calc
    _ = -2*(p b)⁻¹-(-2*(p a)⁻¹) := he
    _ = _ := by ring

theorem spectralWKB_integral_fifth (a b : ℝ) (hab : a≤b) (p g : ℝ → ℝ)
    (hp : ContinuousOn p (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hp0 : ∀ t ∈ Icc a b, 0<p t)
    (hD : ∀ t ∈ Ioo a b, HasDerivAt p (g t/(2*p t)) t) :
    (∫ t in a..b, g t/(p t)^5)=2/(3*(p a)^3)-2/(3*(p b)^3) := by
  let A := fun t => (-2/3 : ℝ)*((p t)^3)⁻¹
  have hAc : ContinuousOn A (Icc a b) :=
    continuousOn_const.mul ((hp.pow 3).inv₀ (fun t ht => pow_ne_zero _ (hp0 t ht).ne'))
  have hAd (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt A (g t/(p t)^5) t := by
    apply (((hD t ht).pow 3).inv (pow_ne_zero _ (hp0 t ⟨ht.1.le,ht.2.le⟩).ne') |>.const_mul (-2/3)).congr_deriv
    simp only [Pi.pow_apply]
    field_simp [(hp0 t ⟨ht.1.le,ht.2.le⟩).ne']
    ring
  have hi : IntervalIntegrable (fun t => g t/(p t)^5) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab
      (hg.div (hp.pow 5) (fun t ht => pow_ne_zero _ (hp0 t ht).ne'))
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hAc hAd hi
  dsimp only [A] at he
  calc
    _ = (-2/3)*((p b)^3)⁻¹-((-2/3)*((p a)^3)⁻¹) := he
    _ = _ := by ring

end DefocusingNLS

end OAI
