import OAI.Geometry.SurfaceImmersion.Correction.CorrectionMetricIdentity
import OAI.Geometry.Immersion.ClosedSurface.WeightedBounds

namespace OAI

/-! Weighted estimates for the bilinear smoothing-tail error. -/

noncomputable section

namespace ClosedSurfaceR4.ExactCorrection

open scoped ContDiff

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The symmetric mixed metric coefficient as a bounded bilinear map of
the two differentials. -/
def crossBilinear (v w : E) :
    (E →L[ℝ] V) →L[ℝ] (E →L[ℝ] V) →L[ℝ] ℝ := by
  let L : (E →L[ℝ] V) →ₗ[ℝ] (E →L[ℝ] V) →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun A B => inner ℝ (A v) (B w) + inner ℝ (A w) (B v))
      (by intros; simp only [add_apply, inner_add_left]; ring)
      (by intros; simp only [smul_apply, real_inner_smul_left]; ring)
      (by intros; simp only [add_apply, inner_add_right]; ring)
      (by intros; simp only [smul_apply, real_inner_smul_right]; ring)
  exact L.mkContinuous₂ (2 * ‖v‖ * ‖w‖) (by
    intro A B
    change ‖inner ℝ (A v) (B w) + inner ℝ (A w) (B v)‖ ≤ _
    calc
      _ ≤ ‖inner ℝ (A v) (B w)‖ + ‖inner ℝ (A w) (B v)‖ := norm_add_le _ _
      _ ≤ ‖A v‖ * ‖B w‖ + ‖A w‖ * ‖B v‖ :=
        add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
      _ ≤ (‖A‖ * ‖v‖) * (‖B‖ * ‖w‖) + (‖A‖ * ‖w‖) * (‖B‖ * ‖v‖) := by
        gcongr <;> apply ContinuousLinearMap.le_opNorm
      _ = _ := by ring)

@[simp] lemma crossBilinear_apply (v w : E) (A B : E →L[ℝ] V) :
    crossBilinear v w A B = inner ℝ (A v) (B w) + inner ℝ (A w) (B v) := rfl

/-- Higher derivatives of the metric comparison depend linearly on the
smoothing tail when the new increment has its fixed weighted bound. -/
theorem weighted_metricCrossTerm
    {O : Set E} (hO : UniqueDiffOn ℝ O) {τ C D : ℝ} {m : ℕ}
    (hτ : 0 ≤ τ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    {G U : E → V}
    (hG : ContDiffOn ℝ ∞ (fderiv ℝ G) O)
    (hU : ContDiffOn ℝ ∞ (fderiv ℝ U) O)
    (hbG : WeightedEstimates.WeightedBound O τ m C (fderiv ℝ G))
    (hbU : WeightedEstimates.WeightedBound O τ m D (fderiv ℝ U))
    (v w : E) :
    WeightedEstimates.WeightedBound O τ m
      (2 * ‖v‖ * ‖w‖ * (2 ^ m * C * D))
      (fun x => metricCrossTerm G U x v w) := by
  have hb := hbG.bilinear hO hτ hC hD hG hU hbU (crossBilinear v w)
  apply hb.mono_const
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro A
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro B
  change ‖inner ℝ (A v) (B w) + inner ℝ (A w) (B v)‖ ≤ _
  calc
    _ ≤ ‖inner ℝ (A v) (B w)‖ + ‖inner ℝ (A w) (B v)‖ := norm_add_le _ _
    _ ≤ ‖A v‖ * ‖B w‖ + ‖A w‖ * ‖B v‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ (‖A‖ * ‖v‖) * (‖B‖ * ‖w‖) + (‖A‖ * ‖w‖) * (‖B‖ * ‖v‖) := by
      gcongr <;> apply ContinuousLinearMap.le_opNorm
    _ = _ := by ring

end ClosedSurfaceR4.ExactCorrection

end

end OAI
