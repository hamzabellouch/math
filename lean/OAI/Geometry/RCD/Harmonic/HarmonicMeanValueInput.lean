import OAI.Geometry.RCD.Harmonic.HarmonicAffineImprovement

namespace OAI

/-! # The published harmonic mean-value estimate used for affine evaluation

Jiang, *Cheeger-harmonic functions in metric measure spaces revisited*,
JFA 266 (2014), Lemma 4.1 (printed pp.14–15), with lambda=0 and exponent 2.
Only the half-ball L-infinity consequence under bounded rescaled curvature
is retained. Full support and continuity give pointwise evaluation below.
-/

open Set Metric MeasureTheory

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The fixed-ratio, harmonic L²-to-L∞ specialization of Jiang Lemma 4.1. -/
def LocalHarmonicL2MeanValueInput {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X) : Prop :=
  2 ≤ n → ∀ a : ℝ, 0 ≤ a → ∃ C : ℝ, 1 ≤ C ∧
    ∀ (p : X) (r : ℝ), 0 < r → -a ≤ K * r ^ 2 →
    ∀ w : SobolevSpace (hausdorff n X) hX.quadratic,
      IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p r) w →
      ∀ᵐ x ∂(hausdorff n X).restrict (ball p (r / 2)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic w x| ≤ C * harmonicTargetNorm hX p r w

/-- The a.e. estimate applies at the center to every continuous representative. -/
theorem LocalHarmonicL2MeanValueInput.center_bound {K : ℝ} {n : ℕ}
    {hX : NoncollapsedRCD K n X} (hmean : LocalHarmonicL2MeanValueInput hX)
    (hn : 2 ≤ n) {a : ℝ} (ha : 0 ≤ a) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : X) (r : ℝ), 0 < r → -a ≤ K * r ^ 2 →
    ∀ (w : SobolevSpace (hausdorff n X) hX.quadratic) (v : X → ℝ),
      IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p r) w →
      ContinuousOn v (ball p r) →
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic w =ᵐ[
        (hausdorff n X).restrict (ball p r)] v) →
      |v p| ≤ C * harmonicTargetNorm hX p r w := by
  let _ := hX.openPos K n
  obtain ⟨C, hC, hbound⟩ := hmean hn a ha
  refine ⟨C, hC, ?_⟩
  intro p r hr hcurv w v hw hv hrep
  have hsub : ball p (r / 2) ⊆ ball p r := ball_subset_ball (by linarith)
  have hv' := (hv.mono hsub).abs
  have hval : ∀ᵐ x ∂(hausdorff n X).restrict (ball p (r / 2)),
      |v x| ≤ C * harmonicTargetNorm hX p r w := by
    filter_upwards [hbound p r hr hcurv w hw,
      ae_restrict_of_ae_restrict_of_subset hsub hrep] with x hx heq
    rwa [heq] at hx
  have heq : (fun x => min |v x| (C * harmonicTargetNorm hX p r w)) =ᵐ[
      (hausdorff n X).restrict (ball p (r / 2))] fun x => |v x| :=
    hval.mono (fun _ hx => min_eq_left hx)
  have hp := Measure.eqOn_open_of_ae_eq heq isOpen_ball (hv'.inf continuousOn_const) hv'
    (mem_ball_self (by linarith : 0 < r / 2))
  exact min_eq_left_iff.mp hp

end RegularPointCoordinates

end

end OAI
