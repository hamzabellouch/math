import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Complex.Basic

namespace OAI

/-! Real and imaginary quadratic forms sum to the complex norm square. -/

open MeasureTheory
namespace DefocusingNLS

theorem spectralComplex_integral_sq (R : ℝ) (w : ℝ → ℝ) (u : ℝ → ℂ)
    (hw : Continuous w) (hu : Continuous u) :
    (∫ r in (0 : ℝ)..R, w r*(u r).re^2)+(∫ r in (0 : ℝ)..R, w r*(u r).im^2) =
      ∫ r in (0 : ℝ)..R, w r*‖u r‖^2 := by
  have hr : IntervalIntegrable (fun r => w r*(u r).re^2) volume 0 R :=
    (hw.mul ((Complex.continuous_re.comp hu).pow 2)).intervalIntegrable 0 R
  have hi : IntervalIntegrable (fun r => w r*(u r).im^2) volume 0 R :=
    (hw.mul ((Complex.continuous_im.comp hu).pow 2)).intervalIntegrable 0 R
  rw [← intervalIntegral.integral_add hr hi]
  apply intervalIntegral.integral_congr
  intro r _
  simp only [Complex.sq_norm,Complex.normSq_apply]
  ring

end DefocusingNLS

end OAI
