import OAI.Analysis.LipschitzHilbert.Fourier.PositiveConvolution

namespace OAI

/-! The positive planar kernel in coordinates (x,Y), and its exact
factorization into the two line convolutions used for concentration. -/

noncomputable section
open MeasureTheory

namespace LipschitzHilbert

def planarPositiveConvolution (l W : ℝ) (f : ℝ × ℝ → ℝ) (x y : ℝ) : ℝ :=
  ∫ z : ℝ × ℝ, (lineKernel l (x-z.1) * lineKernel W (y-z.2)) * f z

theorem planarPositiveConvolution_integrable (l W : ℝ) (f : ℝ × ℝ → ℝ)
    (hf : Measurable f) (hl : 0 < l) (hW : 0 < W) {C : ℝ}
    (hbound : ∀ z, ‖f z‖ ≤ C) (x y : ℝ) :
    Integrable (fun z : ℝ × ℝ => (lineKernel l (x-z.1) * lineKernel W (y-z.2)) * f z) := by
  have hx : Integrable (fun s => lineKernel l (x-s)) := by
    simp_rw [lineKernel_sub_comm l x]
    exact lineKernel_integrable l x hl
  have hy : Integrable (fun s => lineKernel W (y-s)) := by
    simp_rw [lineKernel_sub_comm W y]
    exact lineKernel_integrable W y hW
  exact (hx.mul_prod hy).mul_bdd hf.aestronglyMeasurable (Filter.Eventually.of_forall hbound)

theorem planarPositiveConvolution_eq_iterated (l W : ℝ) (f : ℝ × ℝ → ℝ)
    (hf : Measurable f) (hl : 0 < l) (hW : 0 < W) {C : ℝ}
    (hbound : ∀ z, ‖f z‖ ≤ C) (x y : ℝ) :
    planarPositiveConvolution l W f x y =
      positiveConvolution l (fun s => positiveConvolution W (fun t => f (s,t)) y) x := by
  unfold planarPositiveConvolution
  rw [Measure.volume_eq_prod, integral_prod _ (planarPositiveConvolution_integrable l W f hf hl hW hbound x y)]
  simp_rw [mul_assoc, integral_const_mul]
  rfl

end LipschitzHilbert

end

end OAI
