import OAI.MeasureTheory.Falconer.Estimates.QuadraticDampingLimit

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped FourierTransform SchwartzMap

 theorem quadratic_fresnel_coefficient {b : ℝ} (hb : 0 < b) :
    ((Real.pi:ℂ)/((b:ℂ)*Complex.I))^(1/2:ℂ) =
      (((Real.pi/b)^(1/2:ℝ):ℝ):ℂ) * Complex.exp (-(Real.pi:ℂ)/4*Complex.I) := by
  have hr : 0 < Real.pi/b := div_pos Real.pi_pos hb
  have hi : -Complex.I ≠ 0 := neg_ne_zero.mpr Complex.I_ne_zero
  have he : (Real.pi:ℂ)/((b:ℂ)*Complex.I) = ((Real.pi/b:ℝ):ℂ)*(-Complex.I) := by
    push_cast
    field_simp
    simp [Complex.I_sq,div_eq_mul_inv]
  rw [he,Complex.cpow_def_of_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') hi),
    Complex.log_ofReal_mul hr hi,Complex.log_neg_I]
  have hex : (((Real.log (Real.pi/b):ℝ):ℂ)+(-((Real.pi:ℂ)/2)*Complex.I))*(1/2:ℂ) =
      ((Real.log (Real.pi/b):ℝ):ℂ)*(1/2:ℂ) + (-(Real.pi:ℂ)/4*Complex.I) := by ring
  rw [hex,Complex.exp_add]
  congr 1
  rw [Real.rpow_def_of_pos hr]
  push_cast
  rfl

 theorem quadratic_imaginary_exponent {b : ℝ} (hb : 0 < b) (s : ℝ) :
    -((s:ℂ)^2)/(4*((b:ℂ)*Complex.I)) = Complex.I*((s:ℂ)^2/(4*(b:ℂ))) := by
  field_simp [Complex.ofReal_ne_zero.mpr hb.ne']
  simp [Complex.I_sq]

 theorem quadratic_stationary_identity {b : ℝ} (hb : 0 < b) (φ : 𝓢(ℝ,ℂ)) :
    (∫ x : ℝ, Complex.exp (-((b:ℂ)*Complex.I)*(x:ℂ)^2) * φ x) =
      ((((Real.pi/b)^(1/2:ℝ):ℝ):ℂ)*Complex.exp (-(Real.pi:ℂ)/4*Complex.I)) *
      ∫ ξ : ℝ, Complex.exp (Complex.I*(((2*Real.pi*ξ:ℝ):ℂ)^2/(4*(b:ℂ)))) * 𝓕⁻ φ ξ := by
  have hh := quadratic_oscillatory_pairing hb (𝓕⁻ φ)
  simp only [FourierTransform.fourier_fourierInv_eq] at hh
  rw [hh]
  simp only [quadraticFourierKernel,quadratic_fresnel_coefficient hb,quadratic_imaginary_exponent hb]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with ξ
  ring

end PlanarFalconer

end OAI
