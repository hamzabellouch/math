import OAI.Geometry.SurfaceImmersion.Correction.FiniteSmootherBounds

namespace OAI

/-! The finite-order smoother approximates using only the displayed finite
number of input derivatives. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory
open JetPolynomial (Base)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma residual_add_orders (s : ℝ) (n m : ℕ) (f : Base → E) :
    residual s (n + m) f = residual s n (residual s m f) := by
  induction n with
  | zero => simp only [Nat.zero_add, residual]
  | succ n ih =>
    rw [show n + 1 + m = (n + m) + 1 by omega]
    simp only [residual, ih]

lemma error_finiteSmooth (n : ℕ) (s : ℝ) (f : Base → E) :
    f - finiteSmooth n s f = residual s n f := by
  rw [finiteSmooth_eq]
  abel

def approximationConstant (r j : ℕ) : ℝ :=
  (1 + ∫ y, ‖kernel 0 y‖) ^ j * firstMoment (kernel 0) ^ (r - j)

lemma approximationConstant_nonneg (r j : ℕ) : 0 ≤ approximationConstant r j :=
  mul_nonneg
    (pow_nonneg (add_nonneg zero_le_one (integral_nonneg fun _ => norm_nonneg _)) _)
    (pow_nonneg (firstMoment_nonneg _) _)

variable [CompleteSpace E]

/-- The `q+j`-th error derivative gains `s^(r-j)`, using input derivatives
only through `q+r`. Constants do not depend on the input or the scale. -/
theorem finiteSmooth_approximation (r q j : ℕ) (hj : j ≤ r)
    {s C : ℝ} (hs : 0 < s) {f : Base → E}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hb : ∀ x, ‖iteratedFDeriv ℝ (q + r) f x‖ ≤ C) (x : Base) :
    ‖iteratedFDeriv ℝ (q + j) (f - finiteSmooth r s f) x‖ ≤
      approximationConstant r j * s ^ (r - j) * C := by
  rw [error_finiteSmooth]
  have heq : residual s r f = residual s j (residual s (r - j) f) := by
    rw [← residual_add_orders, Nat.add_sub_of_le hj]
  rw [heq]
  have hb' : ∀ y, ‖iteratedFDeriv ℝ (q + j) (residual s (r - j) f) y‖ ≤
      (s * firstMoment (kernel 0)) ^ (r - j) * C := by
    intro y
    apply iterated_residual_norm_le hs (r - j) (q + j) hf hfc
    intro z
    rw [show r - j + (q + j) = q + r by omega]
    exact hb z
  have h := iterated_residual_bounded hs j (q + j)
    (residual_smooth hs (r - j) hf) (residual_compact hs (r - j) hfc) hb' x
  apply h.trans_eq
  unfold approximationConstant
  rw [mul_pow]
  ring

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
