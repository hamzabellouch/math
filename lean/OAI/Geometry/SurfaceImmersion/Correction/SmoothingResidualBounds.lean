import OAI.Geometry.SurfaceImmersion.Correction.SmoothingResidual

namespace OAI

/-! Arbitrary finite approximation order from a finite input derivative bound. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory
open JetPolynomial (Base)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Applying the smoothing residual `n` times gains `s^n`, using just the
`n`-th derivative of the original input. -/
theorem residual_norm_le {s C : ℝ} (hs : 0 < s) (n : ℕ)
    {f : Base → E} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hb : ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ C) (x : Base) :
    ‖residual s n f x‖ ≤ (s * firstMoment (kernel 0)) ^ n * C := by
  induction n generalizing E x with
  | zero => simpa only [residual, pow_zero, one_mul, norm_iteratedFDeriv_zero] using hb x
  | succ n ih =>
    have hb' : ∀ y, ‖fderiv ℝ (residual s n f) y‖ ≤
        (s * firstMoment (kernel 0)) ^ n * C := by
      intro y
      rw [fderiv_residual hs n hf hfc]
      apply ih (hf.fderiv_right (m := ∞) (by simp)) (hfc.fderiv ℝ) (x := y)
      intro z
      rw [norm_iteratedFDeriv_fderiv]
      exact hb z
    have h := smooth_sub_norm_le 0 hs (residual_smooth hs n hf) hb' x
    change ‖residual s n f x - smooth 0 s (residual s n f) x‖ ≤ _
    apply h.trans_eq
    rw [pow_succ]
    ring

/-- The same finite-order approximation estimate in each higher derivative. -/
theorem iterated_residual_norm_le {s C : ℝ} (hs : 0 < s) (n m : ℕ)
    {f : Base → E} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hb : ∀ x, ‖iteratedFDeriv ℝ (n + m) f x‖ ≤ C) (x : Base) :
    ‖iteratedFDeriv ℝ m (residual s n f) x‖ ≤
      (s * firstMoment (kernel 0)) ^ n * C := by
  induction m generalizing E with
  | zero =>
    rw [norm_iteratedFDeriv_zero]
    exact residual_norm_le hs n hf hfc (by simpa only [Nat.add_zero] using hb) x
  | succ m ih =>
    rw [← norm_iteratedFDeriv_fderiv, fderiv_residual hs n hf hfc]
    apply ih (hf.fderiv_right (m := ∞) (by simp)) (hfc.fderiv ℝ)
    intro y
    rw [norm_iteratedFDeriv_fderiv]
    rw [Nat.add_assoc]
    exact hb y

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
