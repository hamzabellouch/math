import OAI.Geometry.SurfaceImmersion.Correction.SmoothingDerivatives
import OAI.Geometry.Immersion.ClosedSurface.WeightedBounds

namespace OAI

/-! Smoothing is bounded in every original derivative norm. The bound uses
only the input derivative of that order and the fixed kernel L1 norm. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory WeightedEstimates
open JetPolynomial (Base)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Exact derivative commutation gives the scale-independent bound at every
order on localized inputs. -/
theorem iterated_smooth_norm_le (r : ℕ) {s : ℝ} (hs : 0 < s) (n : ℕ)
    {f : Base → E} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) {C : ℝ}
    (hb : ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ C) (x : Base) :
    ‖iteratedFDeriv ℝ n (smooth r s f) x‖ ≤ (∫ y, ‖kernel r y‖) * C := by
  induction n generalizing E with
  | zero =>
    simp only [norm_iteratedFDeriv_zero] at hb ⊢
    exact smooth_norm_le r hs hb x
  | succ n ih =>
    rw [← norm_iteratedFDeriv_fderiv]
    have heq : fderiv ℝ (smooth r s f) = smooth r s (fderiv ℝ f) :=
      funext (fderiv_smooth r hs hf hfc)
    rw [heq]
    apply ih (hf.fderiv_right (m := ∞) (by simp)) (hfc.fderiv ℝ)
    intro y
    rw [norm_iteratedFDeriv_fderiv]
    exact hb y

/-- The boundedness part of finite-order smoothing in weighted norms.
The weight scale may differ from the kernel scale. -/
theorem smooth_weighted_bound (r : ℕ) {s t C : ℝ} (hs : 0 < s) (ht : 0 < t)
    (m : ℕ) {f : Base → E} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hb : WeightedBound Set.univ t m C f) :
    WeightedBound Set.univ t m ((∫ y, ‖kernel r y‖) * C) (smooth r s f) := by
  intro j hj x _
  rw [iteratedFDerivWithin_univ]
  have hd : ∀ y, ‖iteratedFDeriv ℝ j f y‖ ≤ C / t ^ j := by
    intro y
    simpa only [iteratedFDerivWithin_univ] using hb.deriv_le ht hj (Set.mem_univ y)
  have h := iterated_smooth_norm_le r hs j hf hfc hd x
  calc
    _ ≤ t ^ j * ((∫ y, ‖kernel r y‖) * (C / t ^ j)) :=
      mul_le_mul_of_nonneg_left h (pow_nonneg ht.le _)
    _ = _ := by field_simp

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
