import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Tactic
import OAI.NumberTheory.Jacobsthal.Primes.DirichletZeroPenalty
import OAI.NumberTheory.Ostmann.Dirichlet.GrowthIntegral
import OAI.NumberTheory.Ostmann.Dirichlet.LogDerivativeRight

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

namespace Ostmann.Dirichlet

lemma real_zero_kernel_le {x z t K : ℝ} (hx : 0 < x) (hxz : x ≤ z)
    (hK : 1 ≤ K) (hzK : z ≤ K * x) :
    x / (x ^ 2 + t ^ 2) ≤ K * (z / (z ^ 2 + t ^ 2)) := by
  have hz : 0 < z := hx.trans_le hxz
  have hdx : 0 < x ^ 2 + t ^ 2 := by positivity
  have hdz : 0 < z ^ 2 + t ^ 2 := by positivity
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ hdx hdz).mpr
  have hxK : x ≤ K * z := hxz.trans (by nlinarith)
  have h1 := mul_le_mul_of_nonneg_right hzK (mul_nonneg hz.le hx.le)
  have h2 := mul_le_mul_of_nonneg_right hxK (sq_nonneg t)
  nlinarith only [h1, h2]

lemma real_zero_term_le_mul {u v K : ℝ} {rho : ℂ} (m : ℕ)
    (hu : rho.re < u) (huv : u ≤ v) (hK : 1 ≤ K)
    (hgap : v - rho.re ≤ K * (u - rho.re)) :
    (((m : ℂ) / ((u : ℂ) - rho)).re) ≤
      K * (((m : ℂ) / ((v : ℂ) - rho)).re) := by
  have h := mul_le_mul_of_nonneg_left
    (real_zero_kernel_le (t := rho.im) (by linarith) (by linarith) hK hgap)
    (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  simp only [Complex.div_re, Complex.natCast_re, Complex.natCast_im,
    Complex.sub_re, Complex.ofReal_re, zero_mul, zero_div, add_zero]
  have hnorm (w : ℝ) : Complex.normSq ((w : ℂ) - rho) =
      (w - rho.re) ^ 2 + rho.im ^ 2 := by
    simp [Complex.normSq, pow_two]
  rw [hnorm u, hnorm v]
  simpa only [mul_div_assoc, mul_left_comm] using h

end Ostmann.Dirichlet

end OAI
