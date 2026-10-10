import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ZeroTailPolynomialRoots
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.PolynomialRectangleCount

namespace OAI

/-! # Analytic zero counts for the central zero-tail determinant -/

open Polynomial
open scoped Classical

namespace DefocusingNLS

theorem analyticOrderAt_const_mul (c : ℂ) (hc : c ≠ 0) (f : ℂ → ℂ) (z : ℂ)
    (hf : AnalyticAt ℂ f z) :
    analyticOrderAt (fun w => c * f w) z = analyticOrderAt f z := by
  have h := analyticOrderAt_mul (f := fun _ : ℂ => c) (g := f) analyticAt_const hf
  have hcz : analyticOrderAt (fun _ : ℂ => c) z = 0 :=
    (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => c) z).analyticOrderAt_eq_zero.mpr hc
  rw [hcz, zero_add] at h
  convert! h using 1

namespace SeparatorArithmetic

attribute [local irreducible] spectralHomotopyDeterminant windingPolynomial

theorem central_zeroTail_order (ell : ℕ) (z : ℂ) (hz : -(1 / 32 : ℝ) ≤ z.re) :
    analyticOrderAt
      (spectralHomotopyDeterminant ell (33477607 / 100000000) (270506819 / 100000000) 0) z =
    analyticOrderAt (fun w => ((windingPolynomial ell).map (Int.castRingHom ℂ)).eval
      (w + 1 / 32)) z := by
  let p := (windingPolynomial ell).map (Int.castRingHom ℂ)
  let f := spectralHomotopyDeterminant ell (33477607 / 100000000) (270506819 / 100000000) 0
  have he : (fun w : ℂ => (2 * Complex.I) * p.eval (w + 1 / 32)) =
      (fun w => (100000000 : ℂ) ^ 16 * f w) := by
    funext w
    simpa only [add_sub_cancel_right] using
      windingPolynomial_eval_zeroTailDeterminant ell (w + 1 / 32)
  have hp : AnalyticAt ℂ (fun w => p.eval (w + 1 / 32)) z :=
    ((AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) p) _ (Set.mem_univ _)).comp
      (analyticAt_id.add analyticAt_const)
  have hf : AnalyticAt ℂ f z :=
    analyticAt_spectralHomotopyDeterminant ell _ _ 0 z (by norm_num) hz
  have h := congrArg (fun g : ℂ → ℂ => analyticOrderAt g z) he
  rw [analyticOrderAt_const_mul _ (by norm_num) _ z hp,
    analyticOrderAt_const_mul _ (by norm_num) _ z hf] at h
  exact h.symm

theorem central_zeroTail_rectangle_count (ell : Fin 4) (V : ℝ) :
    rectangleZeroCount V
      (spectralHomotopyDeterminant ell (33477607 / 100000000) (270506819 / 100000000) 0) =
    ((((windingPolynomial ell).map (Int.castRingHom ℂ)).roots.toFinset.filter
      (fun w => w - 1 / 32 ∈ countingRectangle V)).card : ℕ∞) := by
  rw [← rectangleZeroCount_polynomial_translate _ (windingPolynomial_complex_ne_zero ell)
    (windingPolynomial_roots_nodup ell) (1 / 32) V]
  unfold rectangleZeroCount
  apply tsum_congr
  intro z
  exact central_zeroTail_order ell z z.2.1.le

end SeparatorArithmetic
end DefocusingNLS

end OAI
