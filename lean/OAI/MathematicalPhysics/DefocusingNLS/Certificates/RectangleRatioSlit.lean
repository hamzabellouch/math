import OAI.MathematicalPhysics.DefocusingNLS.Certificates.RectangleAnalyticFactorization
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

namespace OAI

/-! # Ratios associated to two interior points avoid the logarithm's cut -/

open Set
namespace DefocusingNLS

theorem countingBoundary_ne_interior {V : ℝ} {z a : ℂ}
    (hz : z ∈ countingRectangleBoundary V) (ha : a ∈ countingRectangle V) : z ≠ a := by
  rintro rfl
  exact hz.2 ha

theorem countingBoundary_ratio_mem_slitPlane {V : ℝ} {z a b : ℂ}
    (hz : z ∈ countingRectangleBoundary V) (ha : a ∈ countingRectangle V)
    (hb : b ∈ countingRectangle V) : (z - a) / (z - b) ∈ Complex.slitPlane := by
  have hzb : z - b ≠ 0 := sub_ne_zero.mpr (countingBoundary_ne_interior hz hb)
  by_contra hc
  have hc' : ((z - a) / (z - b)).re ≤ 0 ∧ ((z - a) / (z - b)).im = 0 := by
    simpa only [Complex.slitPlane, mem_ofPred_eq, not_or, not_lt, not_not] using hc
  let q : ℝ := ((z - a) / (z - b)).re
  have hq : q ≤ 0 := hc'.1
  have he : (q : ℂ) * (z - b) = z - a := by
    have heq : (q : ℂ) = (z - a) / (z - b) := by
      apply Complex.ext <;> simp [q, hc'.2]
    rw [heq, div_mul_cancel₀ _ hzb]
  have hre := congrArg Complex.re he
  have him := congrArg Complex.im he
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hre him
  rcases (mem_countingRectangleBoundary_iff V z).mp hz with ⟨hz, hside⟩
  change -(1/32 : ℝ) < a.re ∧ a.re < 8 ∧ -V < a.im ∧ a.im < V at ha
  change -(1/32 : ℝ) < b.re ∧ b.re < 8 ∧ -V < b.im ∧ b.im < V at hb
  rcases hside with hs | hs | hs | hs
  · rw [hs] at hre
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hq (sub_nonneg.mpr hb.1.le)]
  · rw [hs] at hre
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hq (sub_nonneg.mpr hb.2.1.le)]
  · rw [hs] at him
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hq (sub_nonneg.mpr hb.2.2.1.le)]
  · rw [hs] at him
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hq (sub_nonneg.mpr hb.2.2.2.le)]

end DefocusingNLS

end OAI
