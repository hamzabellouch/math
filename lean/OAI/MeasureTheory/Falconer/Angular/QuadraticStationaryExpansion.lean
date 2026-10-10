import OAI.MeasureTheory.Falconer.Fourier.SchwartzFourierMoments

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped FourierTransform SchwartzMap

 theorem imaginaryTaylor_integral (φ : 𝓢(ℝ,ℂ)) (n : ℕ) (β : ℝ) :
    (∫ x, imaginaryTaylor n (β*x^2)*φ x) =
      ∑ k ∈ Finset.range (n+1),
        ((((k.factorial:ℝ)⁻¹*β^k):ℝ):ℂ)*Complex.I^k * ∫ x : ℝ, (x:ℂ)^(2*k)*φ x := by
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
  rw [he,integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k _
    exact integral_const_mul _ _
  · intro k _
    exact (schwartz_monomial_integrable φ (2*k)).const_mul _

noncomputable def quadraticExpansion (φ : 𝓢(ℝ,ℂ)) (n : ℕ) (b : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n+1),
    ((((k.factorial:ℝ)⁻¹*(Real.pi^2/b)^k):ℝ):ℂ)*Complex.I^k *
      (((-2*(Real.pi:ℂ)*Complex.I)^(2*k))⁻¹ * iteratedDeriv (2*k) (φ : ℝ → ℂ) 0)

noncomputable def fresnelCoefficient (b : ℝ) : ℂ :=
  (((Real.pi/b)^(1/2:ℝ):ℝ):ℂ)*Complex.exp (-(Real.pi:ℂ)/4*Complex.I)

 theorem fresnelCoefficient_norm {b : ℝ} (hb : 0 < b) :
    ‖fresnelCoefficient b‖ = (Real.pi/b)^(1/2:ℝ) := by
  simp [fresnelCoefficient,Complex.norm_exp,Complex.mul_re,
    Complex.norm_real,abs_of_nonneg (Real.rpow_nonneg (div_pos Real.pi_pos hb).le _)]

 theorem quadratic_stationary_expansion {b : ℝ} (hb : 0 < b) (φ : 𝓢(ℝ,ℂ)) (n : ℕ) :
    ‖(∫ x : ℝ, Complex.exp (-((b:ℂ)*Complex.I)*(x:ℂ)^2)*φ x) -
      fresnelCoefficient b * quadraticExpansion φ n b‖ ≤
    (Real.pi/b)^(1/2:ℝ) * ((Real.pi^2/b)^(n+1)/(n.factorial:ℝ)) *
      ∫ ξ : ℝ, ‖ξ‖^(2*(n+1))*‖𝓕⁻ φ ξ‖ := by
  have he : (∫ x, imaginaryTaylor n ((Real.pi^2/b)*x^2)*𝓕⁻ φ x) = quadraticExpansion φ n b := by
    rw [imaginaryTaylor_integral]
    simp only [schwartz_inverse_moment,quadraticExpansion]
  have hex (ξ : ℝ) : Complex.exp (Complex.I*(((2*Real.pi*ξ:ℝ):ℂ)^2/(4*(b:ℂ)))) =
      imaginaryExponential ((Real.pi^2/b)*ξ^2) := by
    unfold imaginaryExponential
    congr 1
    push_cast
    ring
  rw [quadratic_stationary_identity hb φ]
  simp only [hex]
  change ‖fresnelCoefficient b * _ - fresnelCoefficient b * _‖ ≤ _
  rw [← mul_sub,norm_mul,fresnelCoefficient_norm hb,← he]
  have hh := quadratic_taylor_integral_bound (𝓕⁻ φ) n (div_nonneg (sq_nonneg Real.pi) hb.le)
  calc
    _ ≤ (Real.pi/b)^(1/2:ℝ) * (((Real.pi^2/b)^(n+1)/(n.factorial:ℝ)) *
      ∫ ξ : ℝ, ‖ξ‖^(2*(n+1))*‖𝓕⁻ φ ξ‖) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring

end PlanarFalconer

end OAI
