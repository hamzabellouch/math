import OAI.Probability.LatticePassage.PositiveMoment
import OAI.Probability.LatticePassage.LocalizationMean

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

lemma exponential_weighted_density (a x : ℝ) (ha : a < 1) :
    exponentialPDF 1 x * ENNReal.ofReal (exp (a*x)) =
      ENNReal.ofReal (1/(1-a)) * exponentialPDF (1-a) x := by
  by_cases hx : 0 ≤ x
  · rw [exponentialPDF_of_nonneg hx, exponentialPDF_of_nonneg hx,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [one_mul]
    rw [← exp_add]
    have he : -x + a*x = -((1-a)*x) := by ring
    rw [he]
    field_simp [show 1-a ≠ 0 by linarith]
  · rw [exponentialPDF_of_neg (lt_of_not_ge hx),
      exponentialPDF_of_neg (lt_of_not_ge hx)]
    simp

theorem exponential_lmoment (a : ℝ) (ha : a < 1) :
    (∫⁻ x, ENNReal.ofReal (exp (a*x)) ∂expMeasure 1) = ENNReal.ofReal (1/(1-a)) := by
  change (∫⁻ x, ENNReal.ofReal (exp (a*x)) ∂volume.withDensity (exponentialPDF 1)) = _
  rw [lintegral_withDensity_eq_lintegral_mul volume (by unfold exponentialPDF; fun_prop)
    (by fun_prop)]
  simp only [Pi.mul_apply, exponential_weighted_density a _ ha]
  rw [lintegral_const_mul _ (by unfold exponentialPDF; fun_prop),
    lintegral_exponentialPDF_eq_one (by linarith : 0 < 1-a), mul_one]

lemma integrable_exponential (a : ℝ) (ha : a < 1) :
    Integrable (fun x => exp (a*x)) (expMeasure 1) := by
  apply (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
    (by filter_upwards [] with x; positivity)).mp
  rw [exponential_lmoment a ha]
  exact ENNReal.ofReal_ne_top

theorem integral_exponential (a : ℝ) (ha : a < 1) :
    (∫ x, exp (a*x) ∂expMeasure 1) = 1/(1-a) := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (by filter_upwards [] with x; positivity) (by fun_prop), exponential_lmoment a ha,
    ENNReal.toReal_ofReal (by positivity)]

lemma exponential_increment_square (a u : ℝ) :
    (exp (a*u)-1)^2 = exp ((2*a)*u)-2*exp (a*u)+1 := by
  rw [show (2*a)*u = a*u+a*u by ring, exp_add]
  ring

lemma integrable_exponential_increment_square (a : ℝ) (ha : 2*a < 1) :
    Integrable (fun u => (exp (a*u)-1)^2) (expMeasure 1) := by
  simp_rw [exponential_increment_square]
  exact ((integrable_exponential (2*a) ha).sub
    ((integrable_exponential a (by linarith)).const_mul 2)).add (integrable_const 1)

theorem integral_exponential_increment_square (a : ℝ) (ha : 2*a < 1) :
    (∫ u, (exp (a*u)-1)^2 ∂expMeasure 1) =
      2*a^2/((1-2*a)*(1-a)) := by
  simp_rw [exponential_increment_square]
  rw [integral_add (f := fun u => exp ((2*a)*u)-2*exp (a*u)) (g := fun _ => (1 : ℝ)) ((integrable_exponential (2*a) ha).sub
      ((integrable_exponential a (by linarith)).const_mul 2)) (integrable_const 1),
    integral_sub (f := fun u => exp ((2*a)*u)) (g := fun u => 2*exp (a*u)) (integrable_exponential (2*a) ha)
      ((integrable_exponential a (by linarith)).const_mul 2), integral_const_mul,
    integral_exponential (2*a) ha, integral_exponential a (by linarith)]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  field_simp [show 1-a ≠ 0 by linarith, show 1-2*a ≠ 0 by linarith]
  ring

theorem exponential_half_increment_square_le (a : ℝ) (ha : |a| ≤ 1/2) :
    (∫⁻ u, ENNReal.ofReal ((exp (a*u/2)-1)^2) ∂expMeasure 1) ≤
      ENNReal.ofReal (2*a^2) := by
  have hb := abs_le.mp ha
  have hp : 2*(a/2) < 1 := by linarith
  have he (u : ℝ) : a*u/2 = (a/2)*u := by ring
  simp_rw [he]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exponential_increment_square (a/2) hp)
    (by filter_upwards [] with u; positivity), integral_exponential_increment_square (a/2) hp]
  apply ENNReal.ofReal_le_ofReal
  have hd : 0 < (1-2*(a/2))*(1-a/2) := mul_pos (by linarith) (by linarith)
  apply (div_le_iff₀ hd).mpr
  have hden : (3/8 : ℝ) ≤ (1-2*(a/2))*(1-a/2) := by nlinarith
  nlinarith [mul_nonneg (sq_nonneg a) (sub_nonneg.mpr hden)]

end CompanionFPP

end OAI
