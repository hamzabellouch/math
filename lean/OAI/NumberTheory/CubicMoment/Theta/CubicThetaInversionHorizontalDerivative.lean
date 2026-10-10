import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInversionGeometry
import Mathlib.Analysis.Complex.RealDeriv

namespace OAI

/-! The horizontal differential of inversion at the centre of a cusp.
It conjugates the direction, with zero first-order vertical variation. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaInversion_horizontal_hasDerivAt {q : ℂ} (hq : q≠0)
    {v : ℝ} (hv : 0<v) (h : ℂ) :
    HasDerivAt (fun t : ℝ => cubicThetaInversion q ((t:ℂ)*h,v))
      (-star h/(q^2*(v:ℂ)^2),0) 0 := by
  let D : ℝ → ℝ := fun t => t^2*Complex.normSq h+v^2
  have hD : HasDerivAt D 0 0 := by
    convert (((hasDerivAt_id (0:ℝ)).pow 2).mul_const (Complex.normSq h)).add_const (v^2) using 1 <;>
      norm_num [D]
  have hn : q^2*(D 0:ℂ)≠0 := by
    simp only [D,zero_pow (by norm_num : (2:ℕ)≠0),zero_mul,zero_add,Complex.ofReal_pow]
    exact mul_ne_zero (pow_ne_zero _ hq) (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hv.ne'))
  have hz := ((Complex.ofRealCLM.hasDerivAt (x:=(0:ℝ))).const_mul (-star h)).div
    (hD.ofReal_comp.const_mul (q^2)) hn
  have hy := (hasDerivAt_const (0:ℝ) v).div (hD.const_mul (Complex.normSq q)) (by
    change Complex.normSq q*D 0≠0
    simp only [D,zero_pow (by norm_num : (2:ℕ)≠0),zero_mul,zero_add]
    exact mul_ne_zero (Complex.normSq_pos.mpr hq).ne' (pow_ne_zero _ hv.ne'))
  have H := hz.prodMk hy
  convert H using 1
  · funext t
    apply Prod.ext
    · change -star ((t:ℂ)*h)/(q^2*(cubicThetaRadius ((t:ℂ)*h,v):ℂ))=
        (-star h*(t:ℂ))/(q^2*(D t:ℂ))
      simp only [cubicThetaRadius,D,Complex.normSq_mul,Complex.normSq_ofReal,
        star_mul,Complex.star_def,Complex.conj_ofReal]
      push_cast
      ring
    · change v/(Complex.normSq q*cubicThetaRadius ((t:ℂ)*h,v))=
        v/(Complex.normSq q*D t)
      simp only [cubicThetaRadius,D,Complex.normSq_mul,Complex.normSq_ofReal]
      ring
  · apply Prod.ext
    · simp only [D,zero_pow (by norm_num : (2:ℕ)≠0),zero_mul,zero_add,
        Complex.ofRealCLM_apply,Complex.ofReal_zero,Complex.ofReal_one,
        Complex.ofReal_pow,mul_one,mul_zero,sub_zero]
      field_simp [hq,Complex.ofReal_ne_zero.mpr hv.ne']
    · simp [D]

end CubicFirstMoment

end

end OAI
