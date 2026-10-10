import OAI.MeasureTheory.Falconer.Fourier.OscillatoryTaylor
import OAI.MeasureTheory.Falconer.Angular.QuadraticStationaryIdentity

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped FourierTransform SchwartzMap

 theorem schwartz_monomial_integrable (φ : 𝓢(ℝ,ℂ)) (p : ℕ) :
    Integrable (fun x : ℝ => (x:ℂ)^p * φ x) := by
  apply (φ.integrable_pow_mul volume p).mono' (by fun_prop)
  filter_upwards with x
  simp [norm_pow, Complex.norm_real]

 theorem imaginaryTaylor_quadratic_integrable (φ : 𝓢(ℝ,ℂ)) (n : ℕ) (β : ℝ) :
    Integrable (fun x => imaginaryTaylor n (β*x^2) * φ x) := by
  have he : (fun x => imaginaryTaylor n (β*x^2)*φ x) =
      fun x : ℝ => ∑ k ∈ Finset.range (n+1),
        ((((k.factorial:ℝ)⁻¹*β^k):ℝ):ℂ)*Complex.I^k * ((x:ℂ)^(2*k)*φ x) := by
    funext x
    unfold imaginaryTaylor
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    simp only [Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_pow,mul_pow,pow_mul]
    ring
  rw [he]
  apply integrable_finsetSum
  intro k _
  exact (schwartz_monomial_integrable φ (2*k)).const_mul _

 theorem imaginaryExponential_quadratic_integrable (φ : 𝓢(ℝ,ℂ)) (β : ℝ) :
    Integrable (fun x => imaginaryExponential (β*x^2)*φ x) := by
  apply φ.integrable.norm.mono' (by unfold imaginaryExponential; fun_prop)
  filter_upwards with x
  have h := imaginaryExponential_derivative_norm 0 (β*x^2)
  simp only [iteratedDeriv_zero] at h
  rw [norm_mul,h,one_mul]

 theorem quadratic_taylor_integral_bound (φ : 𝓢(ℝ,ℂ)) (n : ℕ) {β : ℝ} (hβ : 0 ≤ β) :
    ‖(∫ x, imaginaryExponential (β*x^2)*φ x) - (∫ x, imaginaryTaylor n (β*x^2)*φ x)‖ ≤
      (β^(n+1)/(n.factorial:ℝ)) * ∫ x : ℝ, ‖x‖^(2*(n+1))*‖φ x‖ := by
  rw [← integral_sub (imaginaryExponential_quadratic_integrable φ β)
    (imaginaryTaylor_quadratic_integrable φ n β),← integral_const_mul]
  apply norm_integral_le_of_norm_le
    ((φ.integrable_pow_mul volume (2*(n+1))).const_mul _) _
  filter_upwards with x
  rw [← sub_mul,norm_mul]
  have ht : 0 ≤ β*x^2 := mul_nonneg hβ (sq_nonneg x)
  calc
    _ ≤ ((β*x^2)^(n+1)/(n.factorial:ℝ))*‖φ x‖ :=
      mul_le_mul_of_nonneg_right (imaginaryExponential_taylor_bound n ht) (norm_nonneg _)
    _ = _ := by
      rw [Real.norm_eq_abs,pow_mul,sq_abs,mul_pow]
      ring

end PlanarFalconer

end OAI
