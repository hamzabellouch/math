import OAI.Analysis.LipschitzHilbert.Fourier.DemodulatedVertical
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-! Demodulated line motion from the horizontal derivative and vertical
covariant derivative. The carrier frequencies do not enter the bound. -/

noncomputable section
open Set
namespace LipschitzHilbert
open PhaseCombinatorics

variable {κ : Type*} [Fintype κ]

omit [Fintype κ] in
theorem diagonalModulation_sub (frequency : κ → ℝ) (a b : EuclideanSpace ℂ κ) (t : ℝ) :
    diagonalModulation frequency (a-b) t =
      diagonalModulation frequency a t - diagonalModulation frequency b t := by
  ext k
  simp only [diagonalModulation, WithLp.ofLp_toLp, PiLp.sub_apply]
  ring

theorem modulation_difference_norm (frequency : κ → ℝ) (a b : EuclideanSpace ℂ κ)
    (s t : ℝ) :
    ‖a - diagonalModulation frequency b (t-s)‖ =
      ‖diagonalModulation (fun k => -frequency k) a t -
        diagonalModulation (fun k => -frequency k) b s‖ := by
  have hcancel (k : κ) : character (frequency k) (t-s) * character (-frequency k) t =
      character (-frequency k) s := by
    unfold character
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have heq : diagonalModulation (fun k => -frequency k)
      (a-diagonalModulation frequency b (t-s)) t =
      diagonalModulation (fun k => -frequency k) a t -
        diagonalModulation (fun k => -frequency k) b s := by
    ext k
    simp only [diagonalModulation, WithLp.ofLp_toLp, PiLp.sub_apply]
    rw [sub_mul, mul_assoc, hcancel]
  rw [← heq, norm_diagonalModulation]

/-- The two coordinate segments suffice, so no bound on a mixed
partial derivative is needed. -/
theorem covariant_line_motion (F : ℝ → ℝ → EuclideanSpace ℂ κ) (frequency : κ → ℝ)
    (x0 x1 y0 y1 Cx Cy : ℝ)
    (hx : ∀ t ∈ uIcc x0 x1, DifferentiableAt ℝ (fun x => F x y1) t)
    (hy : ∀ t ∈ uIcc y0 y1, ∀ k, DifferentiableAt ℝ (fun y => F x0 y k) t)
    (hDx : ∀ t ∈ uIcc x0 x1, ‖deriv (fun x => F x y1) t‖ ≤ Cx)
    (hDy : ∀ t ∈ uIcc y0 y1,
      ‖covariantSignal frequency (fun k y => F x0 y k) t‖ ≤ Cy) :
    ‖F x1 y1 - diagonalModulation frequency (F x0 y0) (y1-y0)‖ ≤
      Cx*|x1-x0| + Cy*|y1-y0| := by
  have hhorizontal : ‖F x1 y1 - F x0 y1‖ ≤ Cx*|x1-x0| := by
    simpa only [Real.norm_eq_abs] using
      (convex_uIcc x0 x1).norm_image_sub_le_of_norm_deriv_le hx hDx
        (left_mem_uIcc) (right_mem_uIcc)
  have hvertical :
      ‖demodulatedSignal frequency (fun k y => F x0 y k) y1 -
        demodulatedSignal frequency (fun k y => F x0 y k) y0‖ ≤ Cy*|y1-y0| := by
    apply (convex_uIcc y0 y1).norm_image_sub_le_of_norm_deriv_le
      (fun t ht => (demodulatedSignal_hasDerivAt frequency _ t (hy t ht)).differentiableAt)
      (fun t ht => ?_) (left_mem_uIcc) (right_mem_uIcc)
    rw [demodulatedSignal_deriv_norm frequency _ t (hy t ht)]
    exact hDy t ht
  rw [modulation_difference_norm frequency (F x1 y1) (F x0 y0) y0 y1]
  calc
    _ ≤ ‖diagonalModulation (fun k => -frequency k) (F x1 y1) y1 -
          diagonalModulation (fun k => -frequency k) (F x0 y1) y1‖ +
        ‖diagonalModulation (fun k => -frequency k) (F x0 y1) y1 -
          diagonalModulation (fun k => -frequency k) (F x0 y0) y0‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = ‖F x1 y1 - F x0 y1‖ +
        ‖demodulatedSignal frequency (fun k y => F x0 y k) y1 -
          demodulatedSignal frequency (fun k y => F x0 y k) y0‖ := by
      rw [← diagonalModulation_sub, norm_diagonalModulation]
      rfl
    _ ≤ _ := add_le_add hhorizontal hvertical

end LipschitzHilbert

end

end OAI
