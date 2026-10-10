import OAI.Geometry.SurfaceImmersion.Correction.FiniteOrderSmoother

namespace OAI

/-! Uniform bounds and derivative gain for the same finite-order smoother. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory
open JetPolynomial (Base)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every original derivative norm remains bounded independently of scale. -/
theorem finiteSmooth_bounded (n m : ℕ) {s C : ℝ} (hs : 0 < s)
    {f : Base → E} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hb : ∀ x, ‖iteratedFDeriv ℝ m f x‖ ≤ C) (x : Base) :
    ‖iteratedFDeriv ℝ m (finiteSmooth n s f) x‖ ≤
      (1 + (1 + ∫ y, ‖kernel 0 y‖) ^ n) * C := by
  rw [finiteSmooth_eq, iteratedFDeriv_sub_apply
    ((hf.of_le (by simp)).contDiffAt)
    (((residual_smooth hs n hf).of_le (by simp)).contDiffAt)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ m f x‖ + ‖iteratedFDeriv ℝ m (residual s n f) x‖ := norm_sub_le _ _
    _ ≤ C + (1 + ∫ y, ‖kernel 0 y‖) ^ n * C :=
      add_le_add (hb x) (iterated_residual_bounded hs n m hf hfc hb x)
    _ = _ := by ring

def gainConstant (n m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (∫ y, ‖iteratedFDeriv ℝ m (kernel 0) y‖) *
    (1 + ∫ y, ‖kernel 0 y‖) ^ i

lemma gainConstant_nonneg (n m : ℕ) : 0 ≤ gainConstant n m := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (integral_nonneg fun _ => norm_nonneg _)
    (pow_nonneg (add_nonneg zero_le_one (integral_nonneg fun _ => norm_nonneg _)) _)

/-- A gain of `m` derivatives uses just the zeroth input norm. -/
theorem finiteSmooth_gain (n m : ℕ) {s C : ℝ} (hs : 0 < s)
    {f : Base → E} (hf : ContDiff ℝ ∞ f) (hb : ∀ x, ‖f x‖ ≤ C) (x : Base) :
    ‖iteratedFDeriv ℝ m (finiteSmooth n s f) x‖ ≤
      (s ^ m)⁻¹ * gainConstant n m * C := by
  unfold finiteSmooth
  rw [iteratedFDeriv_sum_apply (fun i _ =>
    ((smooth_smooth 0 hs (residual_smooth hs i hf).continuous.locallyIntegrable).of_le
      (by simp)).contDiffAt)]
  calc
    _ ≤ ∑ i ∈ Finset.range n, ‖iteratedFDeriv ℝ m (smooth 0 s (residual s i f)) x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range n, (s ^ m)⁻¹ *
        ((∫ y, ‖iteratedFDeriv ℝ m (kernel 0) y‖) *
          (1 + ∫ y, ‖kernel 0 y‖) ^ i) * C := by
      apply Finset.sum_le_sum
      intro i _
      have h := smooth_derivative_gain 0 m hs (residual_smooth hs i hf).continuous
        (fun y => residual_bounded hs i hb y) x
      convert h using 1
      ring
    _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]; rfl

/-- Additional output derivatives cost the smoothing scale, while the
original `q` input derivatives commute through the same operator. -/
theorem finiteSmooth_gain_from_derivatives (n q m : ℕ) {s C : ℝ} (hs : 0 < s)
    {f : Base → E} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hb : ∀ x, ‖iteratedFDeriv ℝ q f x‖ ≤ C) (x : Base) :
    ‖iteratedFDeriv ℝ (q + m) (finiteSmooth n s f) x‖ ≤
      (s ^ m)⁻¹ * gainConstant n m * C := by
  induction q generalizing E with
  | zero =>
    rw [Nat.zero_add]
    simp only [norm_iteratedFDeriv_zero] at hb
    exact finiteSmooth_gain n m hs hf hb x
  | succ q ih =>
    rw [show q + 1 + m = (q + m) + 1 by omega, ← norm_iteratedFDeriv_fderiv,
      fderiv_finiteSmooth n hs hf hfc]
    apply ih (hf.fderiv_right (m := ∞) (by simp)) (hfc.fderiv ℝ)
    intro y
    rw [norm_iteratedFDeriv_fderiv]
    exact hb y

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
