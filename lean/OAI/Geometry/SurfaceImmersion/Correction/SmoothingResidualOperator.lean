import OAI.Geometry.SurfaceImmersion.Correction.SmoothingResidualBounds

namespace OAI

/-! Bounds in unchanged derivative norms for repeated residual operators. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory
open JetPolynomial (Base)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The residual operator is bounded in the original norm, independently of
its smoothing scale. -/
theorem residual_bounded {s C : ℝ} (hs : 0 < s) (n : ℕ)
    {f : Base → E} (hb : ∀ x, ‖f x‖ ≤ C) (x : Base) :
    ‖residual s n f x‖ ≤ (1 + ∫ y, ‖kernel 0 y‖) ^ n * C := by
  induction n generalizing x with
  | zero => simpa only [residual, pow_zero, one_mul] using hb x
  | succ n ih =>
    change ‖residual s n f x - smooth 0 s (residual s n f) x‖ ≤ _
    calc
      _ ≤ ‖residual s n f x‖ + ‖smooth 0 s (residual s n f) x‖ := norm_sub_le _ _
      _ ≤ (1 + ∫ y, ‖kernel 0 y‖) ^ n * C +
          (∫ y, ‖kernel 0 y‖) * ((1 + ∫ y, ‖kernel 0 y‖) ^ n * C) :=
        add_le_add (ih x) (smooth_norm_le 0 hs ih x)
      _ = _ := by rw [pow_succ]; ring

/-- Repeated residuals are bounded in every original derivative norm. -/
theorem iterated_residual_bounded {s C : ℝ} (hs : 0 < s) (n m : ℕ)
    {f : Base → E} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hb : ∀ x, ‖iteratedFDeriv ℝ m f x‖ ≤ C) (x : Base) :
    ‖iteratedFDeriv ℝ m (residual s n f) x‖ ≤
      (1 + ∫ y, ‖kernel 0 y‖) ^ n * C := by
  induction m generalizing E with
  | zero =>
    simp only [norm_iteratedFDeriv_zero] at hb ⊢
    exact residual_bounded hs n hb x
  | succ m ih =>
    rw [← norm_iteratedFDeriv_fderiv, fderiv_residual hs n hf hfc]
    apply ih (hf.fderiv_right (m := ∞) (by simp)) (hfc.fderiv ℝ)
    intro y
    rw [norm_iteratedFDeriv_fderiv]
    exact hb y

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
