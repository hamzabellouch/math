import OAI.NumberTheory.Ostmann.QuadraticSieveSquareIntegralBase

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve
open MeasureTheory Set

theorem integral_Ioi_div_sqrt (W : ℝ → ℂ) :
    (∫ t : ℝ in Ioi 0, W t/(Real.sqrt t : ℂ)) =
      2*(∫ x : ℝ in Ioi 0, W (x^2)) := by
  have h := integral_comp_rpow_Ioi_of_pos
    (g := fun t : ℝ => W t/(Real.sqrt t : ℂ)) (p := 2) (by norm_num : (0 : ℝ)<2)
  rw [←h,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hxpos : 0<x := hx
  have hxne : (x : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hxpos.ne'
  norm_num only [show (2-1 : ℝ)=1 by norm_num,Real.rpow_one,Real.rpow_two,
    Real.sqrt_sq_eq_abs,abs_of_pos hxpos]
  rw [Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_ofNat]
  field_simp

end Ostmann.QuadraticSieve

end

end OAI
