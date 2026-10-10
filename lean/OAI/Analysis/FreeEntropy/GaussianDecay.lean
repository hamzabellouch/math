import OAI.Analysis.FreeEntropy.BlockGaussianQuantitative

namespace OAI

universe u1

noncomputable section
open MeasureTheory
namespace FiniteEntropySeparation
variable {E : Type u1} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
 theorem gaussianDecay_integrable {c : ℝ} (hc : 0<c) : Integrable (fun x : E => Real.exp (-c*‖x‖^2)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (b := (c:ℂ)) (by simpa using hc) 0 (0:E)).re
  convert h using 1
  funext x
  simp only [zero_mul,add_zero]
  change Real.exp (-c*‖x‖^2) = (Complex.exp (-(c:ℂ)*(‖x‖:ℂ)^2)).re
  rw [← Complex.ofReal_pow,← Complex.ofReal_neg,← Complex.ofReal_mul,← Complex.ofReal_exp]
  rfl
 theorem polynomial_gaussian_bound {c : ℝ} (hc : 0<c) (m : ℕ) (r : ℝ) (hr : 0≤r) :
    (1+r)^m*Real.exp (-c*r) ≤
      ((m.factorial:ℝ)*(2/c)^m*Real.exp (c/2))*Real.exp (-(c/2)*r) := by
  have hy : 0≤(c/2)*(1+r) := by positivity
  have he := Real.pow_div_factorial_le_exp _ hy m
  have hf : 0<(m.factorial:ℝ) := by positivity
  have hh : (1+r)^m ≤ (m.factorial:ℝ)*(2/c)^m*Real.exp ((c/2)*(1+r)) := by
    have hpow : 0<(c/2)^m := by positivity
    have he' : (c/2)^m*(1+r)^m ≤ Real.exp ((c/2)*(1+r))*(m.factorial:ℝ) := by
      simpa only [mul_pow] using (div_le_iff₀ hf).mp he
    calc
      _ ≤ Real.exp ((c/2)*(1+r))*(m.factorial:ℝ)/(c/2)^m := (le_div_iff₀ hpow).mpr (by simpa [mul_comm] using he')
      _ = _ := by rw [div_eq_mul_inv,← inv_pow,inv_div]; ring
  apply (mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le).trans_eq
  calc
    _ = ((m.factorial:ℝ)*(2/c)^m)*(Real.exp ((c/2)*(1+r))*Real.exp (-c*r)) := by ring
    _ = ((m.factorial:ℝ)*(2/c)^m)*Real.exp (c/2 + -(c/2)*r) := by rw [← Real.exp_add]; congr 2; ring
    _ = _ := by rw [Real.exp_add]; ring
 theorem polynomial_gaussian_integrable {c : ℝ} (hc : 0<c) (m : ℕ) :
    Integrable (fun x : E => (1+‖x‖^2)^m*Real.exp (-c*‖x‖^2)) := by
  apply ((gaussianDecay_integrable (E := E) (show 0<c/2 by positivity)).const_mul
    ((m.factorial:ℝ)*(2/c)^m*Real.exp (c/2))).mono'
  · exact (by fun_prop : Continuous (fun x : E => (1+‖x‖^2)^m*Real.exp (-c*‖x‖^2))).aestronglyMeasurable
  · exact ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      exact polynomial_gaussian_bound hc m (‖x‖^2) (sq_nonneg _))
end FiniteEntropySeparation

end

end OAI
