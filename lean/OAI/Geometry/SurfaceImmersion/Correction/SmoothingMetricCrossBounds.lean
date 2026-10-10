import OAI.Geometry.SurfaceImmersion.Correction.SmoothingTailBounds
import OAI.Geometry.SurfaceImmersion.Correction.CorrectionMetricBounds

namespace OAI

/-! The actual smoothing-tail contribution to the induced metric update.
The dependence on uncontrolled higher input derivatives is linear. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.ExactCorrection
open FiniteOrderSmoothing WeightedEstimates MeasureTheory
open JetPolynomial (Base)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

omit [CompleteSpace V] in
lemma fderiv_smoothing_error (r : ℕ) {s : ℝ} (hs : 0 < s)
    {G : Base → V} (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G) :
    fderiv ℝ (G - finiteSmooth r s G) =
      fderiv ℝ G - finiteSmooth r s (fderiv ℝ G) := by
  funext x
  rw [fderiv_sub (hG.differentiable (by simp) x)
    ((finiteSmooth_smooth r hs hG).differentiable (by simp) x),
    fderiv_finiteSmooth r hs hG hc]
  rfl

/-- In the mixed metric term, all higher derivatives of the true map occur
only in the small factor `(τ/t)^r` multiplying `C`. -/
theorem weighted_smoothing_metricCrossTerm (r m : ℕ) {s t τ B C D : ℝ}
    (hτ : 0 < τ) (hτs : τ ≤ s) (hst : s ≤ t)
    {G U : Base → V} (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G)
    (hU : ContDiff ℝ ∞ U)
    (hBr : WeightedBound Set.univ t r B (fderiv ℝ G))
    (hCm : WeightedBound Set.univ t m C (fderiv ℝ G))
    (hDu : WeightedBound Set.univ τ m D (fderiv ℝ U)) (v w : Base) :
    WeightedBound Set.univ τ m
      (2 * ‖v‖ * ‖w‖ * (2 ^ m *
        (tailConstant r * (B * (s / t) ^ r + C * (τ / t) ^ r)) * D))
      (fun x => metricCrossTerm (G - finiteSmooth r s G) U x v w) := by
  have hs : 0 < s := hτ.trans_le hτs
  have hdG := hG.fderiv_right (m := ∞) (by simp)
  have ht := weighted_smoothing_tail r m hτ hτs hst hdG (hc.fderiv ℝ) hBr hCm
  rw [← fderiv_smoothing_error r hs hG hc] at ht
  have ht0 : 0 ≤ tailConstant r * (B * (s / t) ^ r + C * (τ / t) ^ r) :=
    (norm_nonneg (fderiv ℝ (G - finiteSmooth r s G) 0)).trans (ht.norm_le (Set.mem_univ 0))
  have hD : 0 ≤ D := (norm_nonneg (fderiv ℝ U 0)).trans (hDu.norm_le (Set.mem_univ 0))
  exact weighted_metricCrossTerm isOpen_univ.uniqueDiffOn hτ.le ht0 hD
    ((hG.sub (finiteSmooth_smooth r hs hG)).fderiv_right (m := ∞) (by simp)).contDiffOn
    (hU.fderiv_right (m := ∞) (by simp)).contDiffOn ht hDu v w

end ClosedSurfaceR4.ExactCorrection

end

end OAI
