import OAI.NumberTheory.Ostmann.ZeroDensity.RectangleBoundary

namespace OAI

namespace Ostmann

open Complex MeasureTheory Set
open scoped Interval

def contourRectangleBoundary (a b c d : ℝ) : Set ℂ :=
  {z | z.re ∈ uIcc a b ∧ z.im ∈ uIcc c d ∧
    (z.re = a ∨ z.re = b ∨ z.im = c ∨ z.im = d)}

theorem contourBoundary_bottom {a b c d x : ℝ} (hx : x ∈ uIcc a b) :
    (x : ℂ) + c * I ∈ contourRectangleBoundary a b c d := by
  simpa [contourRectangleBoundary] using hx

theorem contourBoundary_top {a b c d x : ℝ} (hx : x ∈ uIcc a b) :
    (x : ℂ) + d * I ∈ contourRectangleBoundary a b c d := by
  simpa [contourRectangleBoundary] using hx

theorem contourBoundary_right {a b c d y : ℝ} (hy : y ∈ uIcc c d) :
    (b : ℂ) + y * I ∈ contourRectangleBoundary a b c d := by
  simpa [contourRectangleBoundary] using hy

theorem contourBoundary_left {a b c d y : ℝ} (hy : y ∈ uIcc c d) :
    (a : ℂ) + y * I ∈ contourRectangleBoundary a b c d := by
  simpa [contourRectangleBoundary] using hy

theorem rectangleIntegrable_of_continuousOn {f : ℂ → ℂ} {a b c d : ℝ}
    (hf : ContinuousOn f (contourRectangleBoundary a b c d)) :
    RectangleIntegrable f a b c d := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (hf.comp (continuous_ofReal.add continuous_const).continuousOn
      (fun _ hx => contourBoundary_bottom hx)).intervalIntegrable
  · exact (hf.comp (continuous_ofReal.add continuous_const).continuousOn
      (fun _ hx => contourBoundary_top hx)).intervalIntegrable
  · exact (hf.comp (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn
      (fun _ hy => contourBoundary_right hy)).intervalIntegrable
  · exact (hf.comp (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn
      (fun _ hy => contourBoundary_left hy)).intervalIntegrable

theorem rectangleBoundaryIntegral_congr {f g : ℂ → ℂ} {a b c d : ℝ}
    (h : EqOn f g (contourRectangleBoundary a b c d)) :
    rectangleBoundaryIntegral f a b c d = rectangleBoundaryIntegral g a b c d := by
  unfold rectangleBoundaryIntegral
  rw [intervalIntegral.integral_congr (fun x hx => h (contourBoundary_bottom hx)),
    intervalIntegral.integral_congr (fun x hx => h (contourBoundary_top hx)),
    intervalIntegral.integral_congr (fun y hy => h (contourBoundary_right hy)),
    intervalIntegral.integral_congr (fun y hy => h (contourBoundary_left hy))]

theorem contourBoundary_ne_interior {a b c d : ℝ} {z w : ℂ}
    (hz : a < z.re ∧ z.re < b ∧ c < z.im ∧ z.im < d)
    (hw : w ∈ contourRectangleBoundary a b c d) : w ≠ z := by
  intro he
  subst w
  rcases hw.2.2 with ha | hb | hc | hd <;> linarith [hz.1, hz.2.1, hz.2.2.1, hz.2.2.2]

theorem rectangleIntegrable_sub_inv {a b c d : ℝ} {z : ℂ}
    (hz : a < z.re ∧ z.re < b ∧ c < z.im ∧ z.im < d) :
    RectangleIntegrable (fun w => (w - z)⁻¹) a b c d := by
  apply rectangleIntegrable_of_continuousOn
  exact (continuous_id.sub continuous_const).continuousOn.inv₀
    (fun w hw => sub_ne_zero.mpr (contourBoundary_ne_interior hz hw))

theorem rectangleBoundaryIntegral_eq_zero {f : ℂ → ℂ} {a b c d : ℝ}
    (hf : AnalyticOnNhd ℂ f (uIcc a b ×ℂ uIcc c d)) :
    rectangleBoundaryIntegral f a b c d = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
    ((a : ℂ) + c * I) ((b : ℂ) + d * I) (by simpa using hf.differentiableOn)
  simpa [rectangleBoundaryIntegral, smul_eq_mul] using h

end Ostmann

end OAI
