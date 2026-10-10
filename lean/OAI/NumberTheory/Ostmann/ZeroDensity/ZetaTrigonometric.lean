import OAI.NumberTheory.Ostmann.ZeroDensity.ZetaNearZeroBound
import OAI.NumberTheory.Ostmann.ZeroDensity.ComplexCharacterTrigonometric
import OAI.NumberTheory.Ostmann.ZeroDensity.NonquadraticZeroBound

namespace OAI

/-! # The zeta 3-4-1 inequality and the reciprocal-gap bound -/

namespace Ostmann

open Complex

theorem zeta_trigonometric_nonneg (σ t : ℝ) (hσ : 1 < σ) :
    0 ≤ 3 * (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ)).re +
      4 * (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        ((σ : ℂ) + (t : ℂ) * I)).re +
      (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I)).re := by
  have hprincipal (n : ℕ) : (1 : DirichletCharacter ℂ 1) n = 1 := by
    rw [Subsingleton.elim (n : ZMod 1) 1]
    exact map_one _
  simpa only [one_pow, hprincipal, one_mul] using
    complex_character_trigonometric_sum_nonneg (1 : DirichletCharacter ℂ 1) σ t hσ

theorem zeta_near_zero_trigonometric_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (ρ : ℂ), regularizedZeta ρ = 0 → 1 / 2 ≤ ρ.re →
      ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
        4 / (σ - ρ.re) ≤ 3 / (σ - 1) +
          4 * realZeroKernel (σ - 1) ρ.im +
          realZeroKernel (σ - 1) (2 * ρ.im) + C * (Real.log (|ρ.im| + 2) + 1) := by
  obtain ⟨A, hA, ha⟩ := zeta_near_zero_gap_bound
  obtain ⟨B, hB, hb⟩ := exists_vonMangoldt_logarithmic_upper
  obtain ⟨V, hV, hv⟩ := exists_vonMangoldt_series_bound
  refine ⟨4 * A + 2 * B + 3 * V, by positivity, ?_⟩
  intro ρ hρ hρhalf σ hσ hσ2
  let s : ℂ := (σ : ℂ) + (ρ.im : ℂ) * I
  have ht := zeta_trigonometric_nonneg σ ρ.im hσ
  have hgap := ha ρ hρ hρhalf σ hσ hσ2
  have hright := hb ((σ : ℂ) + ((2 * ρ.im : ℝ) : ℂ) * I)
    (by simpa using hσ) (by simpa using hσ2)
  have hreal := (Complex.re_le_norm _).trans (hv σ hσ hσ2)
  have hformula := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
    (s := s) (by simpa [s] using hσ)
  change LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s = _ at hformula
  have hreg := regularizedZeta_logDeriv s (by simpa [s] using hσ)
  have hker : ((s - 1)⁻¹).re = realZeroKernel (σ - 1) ρ.im := by
    simpa [s] using realZeroKernel_complex_sub s 1
  have hid : (logDeriv regularizedZeta s).re = realZeroKernel (σ - 1) ρ.im -
      (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s).re := by
    rw [hreg, Complex.add_re, hker, hformula, neg_div, Complex.neg_re]
    simp only [logDeriv_apply]
    ring
  change 1 / (σ - ρ.re) ≤ (logDeriv regularizedZeta s).re + _ at hgap
  rw [hid] at hgap
  have hdouble := log_double_abs_height_le ρ.im
  have hlog : 0 ≤ Real.log (|ρ.im| + 2) := Real.log_nonneg (by linarith [abs_nonneg ρ.im])
  have hBdouble := mul_le_mul_of_nonneg_left hdouble hB.le
  have hAlog := mul_nonneg hA.le hlog
  have hBlog := mul_nonneg hB.le hlog
  have hVlog := mul_nonneg hV.le hlog
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, add_zero, zero_add, sub_zero] at hright
  dsimp only [s] at hgap
  simp only [div_eq_mul_inv] at hreal hgap ⊢
  nlinarith

end Ostmann

end OAI
