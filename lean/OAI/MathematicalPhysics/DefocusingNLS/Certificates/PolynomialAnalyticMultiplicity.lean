import OAI.MathematicalPhysics.DefocusingNLS.Certificates.RectangleRoucheInput
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Algebra.Polynomial.Roots

namespace OAI

/-! # Polynomial root multiplicities equal analytic vanishing orders -/

open Polynomial

namespace DefocusingNLS

theorem analyticOrderAt_polynomial_eval (p : Polynomial ℂ) (hp : p ≠ 0) (z : ℂ) :
    analyticOrderAt (fun w => p.eval w) z = (p.rootMultiplicity z : ℕ∞) := by
  obtain ⟨q, hq, hn⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp z
  have hnq : q.eval z ≠ 0 := by
    simpa only [dvd_iff_isRoot, Polynomial.IsRoot] using hn
  have he : (fun w => p.eval w) =
      (fun w => (w - z) ^ p.rootMultiplicity z) * (fun w => q.eval w) := by
    funext w
    conv_lhs => rw [hq]
    simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, Pi.mul_apply]
  have hqa : AnalyticAt ℂ (fun w => q.eval w) z :=
    (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) q) z (Set.mem_univ z)
  have hpow : analyticOrderAt (fun w : ℂ => (w - z) ^ p.rootMultiplicity z) z =
      (p.rootMultiplicity z : ℕ∞) := by
    convert! (analyticOrderAt_centeredMonomial (𝕜 := ℂ) (z₀ := z)
      (n := p.rootMultiplicity z)) using 1
  rw [he, analyticOrderAt_mul (by fun_prop) hqa,
    hpow, hqa.analyticOrderAt_eq_zero.mpr hnq, add_zero]

theorem analyticOrderAt_polynomial_translate (p : Polynomial ℂ) (hp : p ≠ 0) (c z : ℂ) :
    analyticOrderAt (fun w => p.eval (w + c)) z = (p.rootMultiplicity (z + c) : ℕ∞) := by
  have ht : AnalyticAt ℂ (fun w : ℂ => w + c) z := by fun_prop
  have hd : deriv (fun w : ℂ => w + c) z ≠ 0 := by simp
  rw [show (fun w => p.eval (w + c)) = (fun w => p.eval w) ∘ (fun w => w + c) from rfl,
    analyticOrderAt_comp_of_deriv_ne_zero ht hd, analyticOrderAt_polynomial_eval p hp]

end DefocusingNLS

end OAI
