import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowKernelIntegrability
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

namespace OAI

/-! # The usual integral in the positive parameter half-plane -/

open MeasureTheory

namespace DefocusingNLS

noncomputable def slowLaplaceKernel (q : ℂ) (m : ℕ) (x : ℂ) (u : ℝ) : ℂ :=
  Complex.exp (-(u : ℂ)) * (u : ℂ) ^ (q - 1) *
    (1 + (u : ℂ) / x) ^ ((m : ℂ) - 1 - q)

theorem slowLaplaceKernel_eq (q : ℂ) (m : ℕ) (x : ℂ) (u : ℝ) :
    slowLaplaceKernel q m x u = regularizedSlowKernel q m x u +
      Complex.exp (-(u : ℂ)) * (u : ℂ) ^ (q - 1) := by
  simp only [slowLaplaceKernel, regularizedSlowKernel, regularizingBracket]
  ring

theorem integrable_slowLaplaceKernel (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : 0 < q.re) (hx : 0 ≤ x.re) (hx0 : x ≠ 0) :
    IntegrableOn (slowLaplaceKernel q m x) (Set.Ioi 0) := by
  have hg : IntegrableOn
      (fun u : ℝ => Complex.exp (-(u : ℂ)) * (u : ℂ) ^ (q - 1)) (Set.Ioi 0) := by
    simpa only [Complex.ofReal_exp, Complex.ofReal_neg] using
      Complex.GammaIntegral_convergent hq
  have he : slowLaplaceKernel q m x = (fun u => regularizedSlowKernel q m x u +
      Complex.exp (-(u : ℂ)) * (u : ℂ) ^ (q - 1)) :=
    funext (slowLaplaceKernel_eq q m x)
  rw [he]
  exact (integrable_regularizedSlowKernel q m x (by linarith) hx hx0).add hg

/-- For positive real part of the parameter, the regularized definition
agrees with the ordinary Laplace integral. -/
theorem regularizedSlowSolution_eq_laplace (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : 0 < q.re) (hx : 0 ≤ x.re) (hx0 : x ≠ 0) :
    regularizedSlowSolution q m x =
      x ^ (-q) * (Complex.Gamma q)⁻¹ *
        ∫ u : ℝ in Set.Ioi 0, slowLaplaceKernel q m x u := by
  have hg : IntegrableOn
      (fun u : ℝ => Complex.exp (-(u : ℂ)) * (u : ℂ) ^ (q - 1)) (Set.Ioi 0) := by
    simpa only [Complex.ofReal_exp, Complex.ofReal_neg] using
      Complex.GammaIntegral_convergent hq
  have hΓ : (∫ u : ℝ in Set.Ioi 0,
      Complex.exp (-(u : ℂ)) * (u : ℂ) ^ (q - 1)) = Complex.Gamma q := by
    rw [Complex.Gamma_eq_integral hq]
    simp only [Complex.GammaIntegral, Complex.ofReal_exp, Complex.ofReal_neg]
  simp_rw [slowLaplaceKernel_eq]
  rw [integral_add (integrable_regularizedSlowKernel q m x (by linarith) hx hx0) hg, hΓ]
  unfold regularizedSlowSolution
  have hne := Complex.Gamma_ne_zero_of_re_pos hq
  field_simp
  ring

end DefocusingNLS

end OAI
