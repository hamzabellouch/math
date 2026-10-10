import OAI.Geometry.RCD.Coordinates.InverseMetricFrames
import OAI.Geometry.RCD.Coordinates.RegularHeatNormalization

namespace OAI

/-! # Frozen frames constructed from the actual heat metrics -/

open Set Metric MeasureTheory
open scoped InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

namespace RegularBilinearData

variable {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X} [(hausdorff n X).Regular]
  {base : X} {ker : ℝ → X → X → ℝ}
  {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker} {enlargement zeta : ℝ}
  (d : RegularBilinearData hX base hk enlargement zeta)

/-- The original heat decrement is positive as an operator. -/
theorem heatAt_decrement_positive {q : X} (hq : q ∈ ball base (d.radius / 32))
    (i : ℕ) (hi : d.shift ≤ i) :
    ((d.heatAt q i).toContinuousLinearMap -
      (d.heatAt q (i + 1)).toContinuousLinearMap).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff _).mpr
  refine ⟨(d.heatAt_isPositive q i).isSymmetric.sub
    (d.heatAt_isPositive q (i + 1)).isSymmetric, ?_⟩
  intro w
  rw [real_inner_comm, sub_apply, inner_sub_right]
  exact sub_nonneg.mpr (d.heatOrder q hq i hi w).1

/-- The sum of two consecutive positive heat decrements. -/
theorem heatAt_two_step_decrement_positive {q : X} (hq : q ∈ ball base (d.radius / 32))
    (i : ℕ) (hi : d.shift ≤ i) :
    ((d.heatAt q i).toContinuousLinearMap -
      (d.heatAt q (i + 2)).toContinuousLinearMap).IsPositive := by
  have h := (d.heatAt_decrement_positive hq i hi).add
    (d.heatAt_decrement_positive hq (i + 1) (by omega))
  have he : (d.heatAt q i).toContinuousLinearMap - (d.heatAt q (i + 2)).toContinuousLinearMap =
      ((d.heatAt q i).toContinuousLinearMap - (d.heatAt q (i + 1)).toContinuousLinearMap) +
      ((d.heatAt q (i + 1)).toContinuousLinearMap - (d.heatAt q (i + 1 + 1)).toContinuousLinearMap) := by
    rw [show i + 1 + 1 = i + 2 by omega]
    abel
  rw [he]
  exact h

/-- Two successive 9/8 bounds still give a half-small total decrement. -/
theorem heatAt_two_step_bound {q : X} (hq : q ∈ ball base (d.radius / 32))
    (i : ℕ) (hi : d.shift ≤ i) (v : Euclidean n) :
    ⟪v, d.heatAt q i v⟫_ℝ ≤ 2 * ⟪v, d.heatAt q (i + 2) v⟫_ℝ := by
  have h0 := (d.heatOrder q hq i hi v).2
  have h1 := (d.heatOrder q hq (i + 1) (by omega) v).2
  rw [show i + 1 + 1 = i + 2 by omega] at h1
  have hp := (d.heatAt_isPositive q (i + 2)).inner_nonneg_right v
  change 0 ≤ ⟪v, d.heatAt q (i + 2) v⟫_ℝ at hp
  change ⟪v, d.heatAt q i v⟫_ℝ ≤ (9 / 8 : ℝ) * ⟪v, d.heatAt q (i + 1) v⟫_ℝ at h0
  change ⟪v, d.heatAt q (i + 1) v⟫_ℝ ≤ (9 / 8 : ℝ) * ⟪v, d.heatAt q (i + 2) v⟫_ℝ at h1
  linarith

/-- The two-scale inverse error costs only the corresponding inverse-energy increment. -/
theorem heatAt_two_step_inverse_error {q : X} (hq : q ∈ ball base (d.radius / 32))
    (i : ℕ) (hi : d.shift ≤ i) (xi : Euclidean n) :
    let delta := (d.heatAt q (i + 2)).symm xi - (d.heatAt q i).symm xi
    ⟪delta, d.heatAt q (i + 2) delta⟫_ℝ ≤
      ⟪xi, (d.heatAt q (i + 2)).symm xi⟫_ℝ - ⟪xi, (d.heatAt q i).symm xi⟫_ℝ :=
  inverse_difference_energy_le _ _ (d.heatAt_isPositive q i)
    (d.heatAt_isPositive q (i + 2)) (d.heatAt_two_step_decrement_positive hq i hi)
    (d.heatAt_two_step_bound hq i hi) xi

/-- Freeze at the heat scale two dyadic steps below the pinching mean radius. -/
def frozenAt (q : X) (i : ℕ) : Euclidean n ≃L[ℝ] Euclidean n :=
  inverseMetricFrame (d.heatAt q (d.shift + i + 17))
    (d.heatAt_isPositive q (d.shift + i + 17))

@[simp] theorem frozenAt_norm_sq (q : X) (i : ℕ) (v : Euclidean n) :
    ‖d.frozenAt q i v‖ ^ 2 = ⟪v, (d.heatAt q (d.shift + i + 17)).symm v⟫_ℝ :=
  inverseMetricFrame_norm_sq _ _ _

/-- The actual heat monotonicity gives monotone frozen norms at every center. -/
theorem frozenAt_mono {q : X} (hq : q ∈ ball base (d.radius / 32))
    (i : ℕ) (v : Euclidean n) :
    ‖d.frozenAt q i v‖ ≤ ‖d.frozenAt q (i + 1) v‖ := by
  have hp := d.heatAt_isPositive q (d.shift + i + 17)
  have hq' := d.heatAt_isPositive q (d.shift + i + 17 + 1)
  have hD := d.heatAt_decrement_positive hq (d.shift + i + 17) (by omega)
  have h := inverseMetricFrame_mono _ _ hp hq' hD v
  simpa only [frozenAt, show d.shift + (i + 1) + 17 = d.shift + i + 17 + 1 by omega] using h

/-- A single dyadic step changes the frozen norm by at most two. -/
theorem frozenAt_step {q : X} (hq : q ∈ ball base (d.radius / 32))
    (i : ℕ) (v : Euclidean n) :
    ‖d.frozenAt q (i + 1) v‖ ≤ 2 * ‖d.frozenAt q i v‖ := by
  have h := inverseMetricFrame_step _ _
    (d.heatAt_isPositive q (d.shift + i + 17))
    (d.heatAt_isPositive q (d.shift + i + 17 + 1))
    (fun w => (d.heatOrder q hq (d.shift + i + 17) (by omega) w).2) v
  simpa only [frozenAt, show d.shift + (i + 1) + 17 = d.shift + i + 17 + 1 by omega] using h

end RegularBilinearData
end RegularPointCoordinates

end

end OAI
