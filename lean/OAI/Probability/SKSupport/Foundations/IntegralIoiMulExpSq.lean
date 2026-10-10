import Mathlib
import OAI.Probability.SKSupport.Model

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.Gaussian

lemma integral_Ioi_mul_exp_sq {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ in Set.Ioi 0, x * Real.exp (-a*x^2)) = (2*a)⁻¹ := by
  have hderiv (x : ℝ) : HasDerivAt (fun y : ℝ => -(2*a)⁻¹ * Real.exp (-a*y^2))
      (x * Real.exp (-a*x^2)) x := by
    apply ((((hasDerivAt_id x).pow 2).const_mul (-a)).exp.const_mul (-(2*a)⁻¹)).congr_deriv
    simp only [id_eq, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    field_simp
  have hlim : Tendsto (fun y : ℝ => -(2*a)⁻¹ * Real.exp (-a*y^2))
      atTop (𝓝 (-(2*a)⁻¹ * 0)) := by
    apply Tendsto.const_mul
    exact Real.tendsto_exp_atBot.comp
      ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).const_mul_atTop_of_neg (neg_lt_zero.mpr ha))
  simpa using integral_Ioi_of_hasDerivAt_of_tendsto' (a := (0 : ℝ)) (fun x _ => hderiv x)
    (integrable_mul_exp_neg_mul_sq ha).integrableOn hlim

lemma integral_abs_mul_exp_sq {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ, |x| * Real.exp (-a*x^2)) = a⁻¹ := by
  have hi : Integrable (fun x : ℝ => |x| * Real.exp (-a*x^2)) := by
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using
      (integrable_mul_exp_neg_mul_sq ha).norm
  have hp : (∫ x : ℝ in Set.Ioi 0, |x| * Real.exp (-a*x^2)) = (2*a)⁻¹ := by
    rw [← integral_Ioi_mul_exp_sq ha]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp only [abs_of_pos (show 0 < x from hx)]
  have hneg (x : ℝ) : |(-x)| * Real.exp (-a*(-x)^2) = |x| * Real.exp (-a*x^2) := by
    rw [abs_neg]
    congr 2
    ring
  have he : (∫ x : ℝ in Set.Ioi 0, |x| * Real.exp (-a*x^2)) =
      ∫ x : ℝ in Set.Iic 0, |x| * Real.exp (-a*x^2) := by
    have h := integral_comp_neg_Ioi (0 : ℝ) (fun x : ℝ => |x| * Real.exp (-a*x^2))
    change (∫ x : ℝ in Set.Ioi 0, |(-x)| * Real.exp (-a*(-x)^2)) =
      ∫ x : ℝ in Set.Iic (-0), |x| * Real.exp (-a*x^2) at h
    simpa only [hneg, neg_zero] using h
  calc
    _ = (∫ x : ℝ in Set.Ioi 0, |x| * Real.exp (-a*x^2)) +
        ∫ x : ℝ in Set.Iic 0, |x| * Real.exp (-a*x^2) := by
      simpa only [Set.compl_Ioi] using (integral_add_compl measurableSet_Ioi hi).symm
    _ = (2*a)⁻¹ + (2*a)⁻¹ := by rw [← he, hp]
    _ = a⁻¹ := by field_simp; norm_num

theorem gaussian_abs_moment (v : ℝ≥0) :
    (∫ x : ℝ, |x| ∂gaussianReal 0 v) = Real.sqrt (2*(v:ℝ)/Real.pi) := by
  by_cases hv : v = 0
  · simp [hv]
  have hv' : (0 : ℝ) < v := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  have ha : 0 < (2*(v:ℝ))⁻¹ := by positivity
  rw [integral_gaussianReal_eq_integral_smul hv]
  have heq : (fun x : ℝ => gaussianPDFReal 0 v x • |x|) =
      (fun x : ℝ => (Real.sqrt (2*Real.pi*v))⁻¹ * (|x| * Real.exp (-(2*(v:ℝ))⁻¹*x^2))) := by
    funext x
    simp only [gaussianPDFReal, sub_zero, smul_eq_mul]
    have hexp : -x^2/(2*(v:ℝ)) = -(2*(v:ℝ))⁻¹*x^2 := by ring
    rw [hexp]
    ring
  rw [heq, integral_const_mul, integral_abs_mul_exp_sq ha, inv_inv]
  have hs : 0 < Real.sqrt (2*Real.pi*(v:ℝ)) := Real.sqrt_pos.mpr (by positivity)
  have hr : 0 ≤ Real.sqrt (2*(v:ℝ)/Real.pi) := Real.sqrt_nonneg _
  have hs2 := Real.sq_sqrt (show 0 ≤ 2*Real.pi*(v:ℝ) by positivity)
  have hr2 := Real.sq_sqrt (show 0 ≤ 2*(v:ℝ)/Real.pi by positivity)
  rw [inv_mul_eq_div]
  apply (div_eq_iff (ne_of_gt hs)).mpr
  have he : (2*(v:ℝ))^2 = (Real.sqrt (2*(v:ℝ)/Real.pi) * Real.sqrt (2*Real.pi*(v:ℝ)))^2 := by
    simp only [mul_pow]
    rw [hs2, hr2]
    field_simp
  nlinarith [mul_nonneg hr hs.le]

end ZeroTemperatureSK.Gaussian

end
end

end OAI
