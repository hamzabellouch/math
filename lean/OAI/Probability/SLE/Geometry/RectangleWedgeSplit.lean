import Mathlib.Analysis.Complex.HasPrimitives

namespace OAI

/-! Splitting a rectangular Cauchy integral along a horizontal line. This
is the local gluing identity needed for a constant boundary interval. -/
noncomputable section
open Complex MeasureTheory Set
open scoped Interval

namespace SLEExactGauge

lemma rectangle_wedge_split (f : ℂ → ℂ) (z w : ℂ) (c : ℝ)
    (hz₁ : IntervalIntegrable (fun y : ℝ => f (z.re+y*I)) volume z.im c)
    (hz₂ : IntervalIntegrable (fun y : ℝ => f (z.re+y*I)) volume c w.im)
    (hw₁ : IntervalIntegrable (fun y : ℝ => f (w.re+y*I)) volume z.im c)
    (hw₂ : IntervalIntegrable (fun y : ℝ => f (w.re+y*I)) volume c w.im) :
    wedgeIntegral z w f+wedgeIntegral w z f=
      (wedgeIntegral z (⟨w.re,c⟩:ℂ) f+wedgeIntegral (⟨w.re,c⟩:ℂ) z f)+
      (wedgeIntegral (⟨z.re,c⟩:ℂ) w f+wedgeIntegral w (⟨z.re,c⟩:ℂ) f) := by
  simp only [wedgeIntegral_add_wedgeIntegral_eq]
  rw [← intervalIntegral.integral_add_adjacent_intervals hz₁ hz₂,
    ← intervalIntegral.integral_add_adjacent_intervals hw₁ hw₂]
  simp only [smul_add]
  abel

end SLEExactGauge

end

end OAI
