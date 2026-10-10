import OAI.MeasureTheory.Falconer.Estimates.QuadraticTaylorRemainder

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped FourierTransform SchwartzMap

 theorem schwartz_fourier_derivative_zero (φ : 𝓢(ℝ,ℂ)) (n : ℕ) :
    iteratedDeriv n (fun x => 𝓕 φ x) 0 =
      (-2*(Real.pi:ℂ)*Complex.I)^n * ∫ x : ℝ, (x:ℂ)^n*φ x := by
  have hh := Real.iteratedDeriv_fourier (f := (φ : ℝ → ℂ)) (N := (⊤ : ℕ∞))
    (fun k _ => by simpa only [Complex.real_smul,Complex.ofReal_pow] using schwartz_monomial_integrable φ k) (n := n) (by simp)
  have hh := congrFun hh 0
  simp only [Real.fourier_eq,inner_zero_right,neg_zero,AddChar.map_zero_eq_one,one_smul,smul_eq_mul] at hh
  change iteratedDeriv n (fun x => 𝓕 φ x) 0 = _ at hh
  rw [hh]
  simp only [mul_pow,mul_assoc]
  simp_rw [integral_const_mul]

 theorem schwartz_inverse_moment (φ : 𝓢(ℝ,ℂ)) (n : ℕ) :
    (∫ x : ℝ, (x:ℂ)^n*𝓕⁻ φ x) =
      ((-2*(Real.pi:ℂ)*Complex.I)^n)⁻¹ * iteratedDeriv n (φ : ℝ → ℂ) 0 := by
  have hh := schwartz_fourier_derivative_zero (𝓕⁻ φ) n
  simp only [FourierTransform.fourier_fourierInv_eq] at hh
  have hn : (-2*(Real.pi:ℂ)*Complex.I)^n ≠ 0 := pow_ne_zero _
    (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
  rw [hh,← mul_assoc,inv_mul_cancel₀ hn,one_mul]

end PlanarFalconer

end OAI
