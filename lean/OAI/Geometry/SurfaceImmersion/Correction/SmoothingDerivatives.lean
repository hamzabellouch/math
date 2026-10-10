import OAI.Geometry.SurfaceImmersion.Correction.SmoothingNormBounds

namespace OAI

/-! Exact differentiation of the constructed smoothing operator on localized
smooth inputs. This moves derivatives onto the input without scale loss. -/
noncomputable section
open scoped ContDiff Convolution

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory ContinuousLinearMap
open JetPolynomial (Base)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma fderiv_smooth (r : ℕ) {s : ℝ} (hs : 0 < s) {f : Base → E}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (x : Base) :
    fderiv ℝ (smooth r s f) x = smooth r s (fderiv ℝ f) x := by
  let L : ℝ →L[ℝ] E →L[ℝ] E := lsmul ℝ ℝ
  have hk : LocallyIntegrable (dilate (kernel r) s) volume :=
    (((smooth_dilate (kernel_smooth r) s).continuous).integrable_of_hasCompactSupport
      (compact_dilate (kernel_compact r) hs.ne')).locallyIntegrable
  have h := hfc.hasFDerivAt_convolution_right L hk (hf.of_le (by simp)) x
  have heq : ((dilate (kernel r) s) ⋆[L.precompR Base, volume] fderiv ℝ f) x =
      smooth r s (fderiv ℝ f) x := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun y => by ext v; rfl)
  exact h.fderiv.trans heq

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
