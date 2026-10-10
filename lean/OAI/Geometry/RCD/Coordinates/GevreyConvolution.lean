import Mathlib.Analysis.Calculus.ContDiff.Convolution

namespace OAI

/-! # Uniform derivative bounds for a compactly supported convolution

The derivative is placed on the smooth compactly supported factor. The
constant is the L¹ norm of the other factor and is independent of the
derivative order. This is the estimate used to give the Gevrey bump a
plateau.
-/

open MeasureTheory
open scoped Convolution ContDiff

noncomputable section
namespace RegularPointCoordinates

/-- A uniform derivative bound passes through convolution with one fixed
integrable scalar function. All vector spaces here are in the same
universe as the finite-dimensional Euclidean application. -/
theorem norm_iteratedFDeriv_convolution_le
    (n : ℕ) {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
    [SFinite μ] [μ.IsAddLeftInvariant]
    (L : ℝ →L[ℝ] F →L[ℝ] G) {f : E → ℝ} {g : E → F}
    (hf : Integrable f μ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ M) (x : E) :
    ‖iteratedFDeriv ℝ n (f ⋆[L, μ] g) x‖ ≤
      ‖L‖ * M * ∫ y, ‖f y‖ ∂μ := by
  induction n generalizing F G with
  | zero =>
    simp only [norm_iteratedFDeriv_zero] at hb ⊢
    calc
      _ ≤ ∫ y, ‖L‖ * M * ‖f y‖ ∂μ := by
        apply norm_integral_le_of_norm_le ((hf.norm.const_mul M).const_mul ‖L‖ |>.congr
          (Filter.Eventually.of_forall fun y => by ring))
        filter_upwards with y
        exact (L.le_opNorm₂ (f y) (g (x - y))).trans (by
          have := hb (x - y)
          calc
            ‖L‖ * ‖f y‖ * ‖g (x - y)‖ ≤ ‖L‖ * ‖f y‖ * M := by gcongr
            _ = _ := by ring)
      _ = _ := integral_const_mul _ _
  | succ n ih =>
    have hd : fderiv ℝ (f ⋆[L, μ] g) = (f ⋆[L.precompR E, μ] fderiv ℝ g) := by
      funext y
      exact (hgc.hasFDerivAt_convolution_right L hf.locallyIntegrable
        (hg.of_le (by simp)) y).fderiv
    rw [← norm_iteratedFDeriv_fderiv, hd]
    have hgb : ∀ y, ‖iteratedFDeriv ℝ n (fderiv ℝ g) y‖ ≤ M := by
      intro y
      rw [norm_iteratedFDeriv_fderiv]
      exact hb y
    apply (ih (L.precompR E) (hg.fderiv_right (by simp)) (hgc.fderiv ℝ) hgb).trans
    gcongr
    exact L.norm_precompR_le E

end RegularPointCoordinates

end

end OAI
