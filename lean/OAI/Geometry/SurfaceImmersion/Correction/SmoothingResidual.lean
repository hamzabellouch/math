import OAI.Geometry.SurfaceImmersion.Correction.SmoothingFirstMoment

namespace OAI

/-! Iterated smoothing residuals give arbitrary finite approximation order. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory
open JetPolynomial (Base)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def residual (s : ℝ) : ℕ → (Base → E) → (Base → E)
  | 0, f => f
  | n + 1, f => residual s n f - smooth 0 s (residual s n f)

lemma smooth_compact (r : ℕ) {s : ℝ} (hs : 0 < s) {f : Base → E}
    (hfc : HasCompactSupport f) : HasCompactSupport (smooth r s f) :=
  (compact_dilate (kernel_compact r) hs.ne').convolution (ContinuousLinearMap.lsmul ℝ ℝ) hfc

lemma residual_smooth {s : ℝ} (hs : 0 < s) (n : ℕ) {f : Base → E}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (residual s n f) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact ih.sub (smooth_smooth 0 hs ih.continuous.locallyIntegrable)

lemma residual_compact {s : ℝ} (hs : 0 < s) (n : ℕ) {f : Base → E}
    (hfc : HasCompactSupport f) : HasCompactSupport (residual s n f) := by
  induction n with
  | zero => exact hfc
  | succ n ih => exact ih.sub (smooth_compact 0 hs ih)

/-- Differentiation commutes with every finite residual. -/
lemma fderiv_residual {s : ℝ} (hs : 0 < s) (n : ℕ) {f : Base → E}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    fderiv ℝ (residual s n f) = residual s n (fderiv ℝ f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext x
    have hr := residual_smooth hs n hf
    change fderiv ℝ (residual s n f - smooth 0 s (residual s n f)) x = _
    rw [fderiv_sub (hr.differentiable (by simp) x)
      ((smooth_smooth 0 hs hr.continuous.locallyIntegrable).differentiable (by simp) x)]
    rw [fderiv_smooth 0 hs hr (residual_compact hs n hfc), ih]
    rfl

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
