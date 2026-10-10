import OAI.MathematicalPhysics.DefocusingNLS.Certificates.RectangleAnalyticFactorization
import Mathlib.Analysis.Complex.CauchyIntegral

namespace OAI

/-! # Cauchy's theorem on the exact spectral counting rectangle -/

open Set MeasureTheory
namespace DefocusingNLS

noncomputable def countingBoundaryIntegral (V : ℝ) (f : ℂ → ℂ) : ℂ :=
  (∫ x : ℝ in (-(1 / 32 : ℝ))..8, f ((x : ℂ) - (V : ℂ) * Complex.I)) -
  (∫ x : ℝ in (-(1 / 32 : ℝ))..8, f ((x : ℂ) + (V : ℂ) * Complex.I)) +
  Complex.I * (∫ y : ℝ in (-V)..V, f (8 + (y : ℂ) * Complex.I)) -
  Complex.I * (∫ y : ℝ in (-V)..V, f (-(1 / 32 : ℂ) + (y : ℂ) * Complex.I))

theorem countingBoundaryIntegral_eq_zero (V : ℝ) (hV : 0 < V) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedCountingRectangle V)) :
    countingBoundaryIntegral V f = 0 := by
  let z : ℂ := -(1 / 32 : ℂ) - (V : ℂ) * Complex.I
  let w : ℂ := 8 + (V : ℂ) * Complex.I
  have hzre : z.re = -(1 / 32 : ℝ) := by simp [z]
  have hzim : z.im = -V := by simp [z]
  have hwre : w.re = 8 := by simp [w]
  have hwim : w.im = V := by simp [w]
  have hrect : (uIcc z.re w.re ×ℂ uIcc z.im w.im) = closedCountingRectangle V := by
    rw [hzre, hzim, hwre, hwim, uIcc_of_le (by norm_num : -(1 / 32 : ℝ) ≤ 8),
      uIcc_of_le (by linarith : -V ≤ V)]
    ext u
    simp only [Complex.mem_reProdIm, mem_Icc, closedCountingRectangle, mem_ofPred_eq]
    tauto
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f z w
    (hrect.symm ▸ hf.differentiableOn)
  simpa [hzre, hzim, hwre, hwim, sub_eq_add_neg, smul_eq_mul,
    countingBoundaryIntegral] using h

end DefocusingNLS

end OAI
