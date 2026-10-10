import OAI.Geometry.SurfaceImmersion.Correction.SmoothingResidualOperator
import OAI.Geometry.SurfaceImmersion.Correction.SmoothingGain

namespace OAI

/-! A concrete smoother of any prescribed finite approximation order. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory
open JetPolynomial (Base)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The finite sum `S + S(I-S) + ... + S(I-S)^(n-1)`. -/
def finiteSmooth (n : ℕ) (s : ℝ) (f : Base → E) : Base → E :=
  ∑ i ∈ Finset.range n, smooth 0 s (residual s i f)

lemma finiteSmooth_eq (n : ℕ) (s : ℝ) (f : Base → E) :
    finiteSmooth n s f = f - residual s n f := by
  induction n with
  | zero => simp [finiteSmooth, residual]
  | succ n ih =>
    unfold finiteSmooth at ih ⊢
    rw [Finset.sum_range_succ, ih]
    funext x
    simp only [Pi.sub_apply, Pi.add_apply, residual]
    abel

lemma finiteSmooth_smooth (n : ℕ) {s : ℝ} (hs : 0 < s)
    {f : Base → E} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (finiteSmooth n s f) := by
  rw [finiteSmooth_eq]
  exact hf.sub (residual_smooth hs n hf)

lemma finiteSmooth_compact (n : ℕ) {s : ℝ} (hs : 0 < s)
    {f : Base → E} (hfc : HasCompactSupport f) : HasCompactSupport (finiteSmooth n s f) := by
  rw [finiteSmooth_eq]
  exact hfc.sub (residual_compact hs n hfc)

lemma fderiv_finiteSmooth (n : ℕ) {s : ℝ} (hs : 0 < s)
    {f : Base → E} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    fderiv ℝ (finiteSmooth n s f) = finiteSmooth n s (fderiv ℝ f) := by
  rw [finiteSmooth_eq, finiteSmooth_eq]
  funext x
  rw [fderiv_sub (hf.differentiable (by simp) x)
    ((residual_smooth hs n hf).differentiable (by simp) x),
    fderiv_residual hs n hf hfc]
  rfl

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
