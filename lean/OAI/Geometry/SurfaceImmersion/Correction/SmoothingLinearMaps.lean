import OAI.Geometry.SurfaceImmersion.Correction.FiniteSmootherLinearity

namespace OAI

/-! Smoothing commutes with fixed linear constraints on the fiber. -/
noncomputable section
open scoped ContDiff Convolution

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory ContinuousLinearMap
open JetPolynomial (Base)

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

lemma smooth_clm (r : ℕ) {s : ℝ} (hs : 0 < s) (L : E →L[ℝ] F)
    {f : Base → E} (hf : LocallyIntegrable f volume) :
    smooth r s (fun x => L (f x)) = fun x => L (smooth r s f x) := by
  funext x
  have hi := (compact_dilate (kernel_compact r) hs.ne').convolutionExists_left
    (lsmul ℝ ℝ) (smooth_dilate (kernel_smooth r) s).continuous hf x
  change (∫ y, dilate (kernel r) s y • L (f (x - y))) =
    L (∫ y, dilate (kernel r) s y • f (x - y))
  simp_rw [← L.map_smul]
  exact L.integral_comp_comm hi

lemma residual_clm (n : ℕ) {s : ℝ} (hs : 0 < s) (L : E →L[ℝ] F)
    {f : Base → E} (hf : ContDiff ℝ ∞ f) :
    residual s n (fun x => L (f x)) = fun x => L (residual s n f x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [residual, ih]
    rw [smooth_clm 0 hs L (residual_smooth hs n hf).continuous.locallyIntegrable]
    ext x
    simp only [Pi.sub_apply, L.map_sub]

lemma finiteSmooth_clm (n : ℕ) {s : ℝ} (hs : 0 < s) (L : E →L[ℝ] F)
    {f : Base → E} (hf : ContDiff ℝ ∞ f) :
    finiteSmooth n s (fun x => L (f x)) = fun x => L (finiteSmooth n s f x) := by
  simp only [finiteSmooth_eq, residual_clm n hs L hf]
  ext x
  simp only [Pi.sub_apply, L.map_sub]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
