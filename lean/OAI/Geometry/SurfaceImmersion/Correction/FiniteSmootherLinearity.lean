import OAI.Geometry.SurfaceImmersion.Correction.FiniteSmootherApproximation

namespace OAI

/-! Linearity of the actual finite-order smoothing construction. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma residual_add (n : ℕ) {s : ℝ} (hs : 0 < s) {f g : Base → E}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    residual s n (f + g) = residual s n f + residual s n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [residual, ih]
    rw [smooth_add 0 hs (residual_smooth hs n hf).continuous.locallyIntegrable
      (residual_smooth hs n hg).continuous.locallyIntegrable]
    abel

lemma residual_smul (n : ℕ) (s a : ℝ) (f : Base → E) :
    residual s n (a • f) = a • residual s n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [residual, ih, smooth_smul, smul_sub]

lemma finiteSmooth_add (n : ℕ) {s : ℝ} (hs : 0 < s) {f g : Base → E}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    finiteSmooth n s (f + g) = finiteSmooth n s f + finiteSmooth n s g := by
  simp only [finiteSmooth_eq, residual_add n hs hf hg]
  abel

lemma finiteSmooth_smul (n : ℕ) (s a : ℝ) (f : Base → E) :
    finiteSmooth n s (a • f) = a • finiteSmooth n s f := by
  simp only [finiteSmooth_eq, residual_smul, smul_sub]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
