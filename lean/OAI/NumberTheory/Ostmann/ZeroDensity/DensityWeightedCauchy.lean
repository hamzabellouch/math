import OAI.NumberTheory.Ostmann.ZeroDensity.DensityFiniteContourShift

namespace OAI

/-! # The weighted Cauchy inequality used for the finite contour polynomials -/

namespace Ostmann

open MeasureTheory

 theorem density_weighted_cauchy (g p : ℝ → ℝ)
    (hg : Integrable g) (hgp : Integrable (fun u => g u * p u))
    (hgpp : Integrable (fun u => g u * (p u) ^ 2))
    (hg0 : ∀ u, 0 ≤ g u) (hpos : 0 < ∫ u, g u) :
    (∫ u, g u * p u) ^ 2 ≤ (∫ u, g u) * ∫ u, g u * (p u) ^ 2 := by
  let A := ∫ u, g u
  let B := ∫ u, g u * p u
  let D := ∫ u, g u * (p u) ^ 2
  let t := B / A
  have hA : 0 < A := hpos
  have htA : t * A = B := div_mul_cancel₀ B hA.ne'
  have he : (∫ u, g u * (p u - t) ^ 2) = D - 2 * t * B + t ^ 2 * A := by
    have hf : (fun u => g u * (p u - t) ^ 2) =
        (fun u => (g u * (p u) ^ 2 - (2 * t) * (g u * p u)) + t ^ 2 * g u) := by
      funext u
      ring
    rw [hf]
    have hadd := integral_add (hgpp.sub (hgp.const_mul (2 * t))) (hg.const_mul (t ^ 2))
    have hsub := integral_sub hgpp (hgp.const_mul (2 * t))
    simp only [Pi.sub_apply] at hadd hsub
    rw [hadd, hsub, integral_const_mul, integral_const_mul]
  have hn : 0 ≤ D - 2 * t * B + t ^ 2 * A := by
    rw [← he]
    exact integral_nonneg (fun u => mul_nonneg (hg0 u) (sq_nonneg _))
  have hm := mul_nonneg hA.le hn
  have hs : (t * A) ^ 2 = B ^ 2 := congrArg (fun x : ℝ => x ^ 2) htA
  change B ^ 2 ≤ A * D
  nlinarith

end Ostmann

end OAI
