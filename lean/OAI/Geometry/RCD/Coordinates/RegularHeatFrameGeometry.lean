import OAI.Geometry.RCD.Coordinates.RegularPatchCumulative

namespace OAI

/-! # Coordinate separation measured in the actual frozen heat frames -/

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

/-- An exact coordinate frame realizes the quadratic inverse mean. -/
theorem coordinateFrame_norm_sq (q : X) (hq : q ∈ ball base (d.radius / 32))
    (i : ℕ) (v : Euclidean n) :
    ‖coordinateFrame (d.frameAt q hq i) v‖ ^ 2 = ⟪v, (d.meanAt q hq i).symm v⟫_ℝ := by
  change ‖(d.frameAt q hq i).toContinuousLinearMap.adjoint v‖ ^ 2 =
    ⟪v, (meanGramEquiv (hausdorff n X) hX.quadratic
      (sobolevColumnMap (hausdorff n X) hX.quadratic d.coordinates)
      (ball q (d.radius / 2 ^ i)) measurableSet_ball (d.frameAt q hq i)
      (d.frameAt_exact q hq i)).symm v⟫_ℝ
  rw [meanGramEquiv_symm_apply]
  change ‖(d.frameAt q hq i).toContinuousLinearMap.adjoint v‖ ^ 2 =
    ⟪v, (d.frameAt q hq i).toContinuousLinearMap ((d.frameAt q hq i).toContinuousLinearMap.adjoint v)⟫_ℝ
  rw [← ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq]

/-- Heat and mean frames at the same radius are uniformly comparable. -/
theorem mean_heat_frame_comparison (q : X) (hq : q ∈ ball base (d.radius / 32))
    (i : ℕ) (hi : d.shift ≤ i) (v : Euclidean n) :
    ‖coordinateFrame (d.frameAt q hq i) v‖ ≤
        (3 / 2 : ℝ) * ‖inverseMetricFrame (d.heatAt q i) (d.heatAt_isPositive q i) v‖ ∧
    ‖inverseMetricFrame (d.heatAt q i) (d.heatAt_isPositive q i) v‖ ≤
        (3 / 2 : ℝ) * ‖coordinateFrame (d.frameAt q hq i) v‖ := by
  let Q := d.heatAt q i
  let G := d.meanAt q hq i
  have hc (w : Euclidean n) :
      (1 / 2 : ℝ) * ⟪w, Q w⟫_ℝ ≤ ⟪w, G w⟫_ℝ ∧
      (1 / 2 : ℝ) * ⟪w, G w⟫_ℝ ≤ ⟪w, Q w⟫_ℝ := by
    have h := d.heatMeanComparison q hq i hi w
    have hp := (d.meanAt_isPositive q hq i).inner_nonneg_right w
    change 0 ≤ ⟪w, G w⟫_ℝ at hp
    change (1 - 1 / 64 : ℝ) * ⟪w, G.toContinuousLinearMap w⟫_ℝ ≤ ⟪w, Q w⟫_ℝ ∧
      ⟪w, Q w⟫_ℝ ≤ (1 + 1 / 64 : ℝ) * ⟪w, G.toContinuousLinearMap w⟫_ℝ at h
    simp only [ContinuousLinearEquiv.coe_coe] at h
    constructor <;> nlinarith [h.1, h.2]
  have h0 := (relative_inverse_bounds Q G (d.heatAt_isPositive q i)
    (d.meanAt_isPositive q hq i) (by norm_num : (0 : ℝ) < 1 / 2) (fun w => (hc w).1) v).1
  have h1 := (relative_inverse_bounds G Q (d.meanAt_isPositive q hq i)
    (d.heatAt_isPositive q i) (by norm_num : (0 : ℝ) < 1 / 2) (fun w => (hc w).2) v).1
  rw [← d.coordinateFrame_norm_sq q hq i v] at h0 h1
  rw [← inverseMetricFrame_norm_sq Q (d.heatAt_isPositive q i) v] at h0 h1
  constructor <;> nlinarith [norm_nonneg (coordinateFrame (d.frameAt q hq i) v),
    norm_nonneg (inverseMetricFrame Q (d.heatAt_isPositive q i) v)]

/-- Monotonicity holds between any two sufficiently late heat scales. -/
theorem heat_frame_mono_indices {q : X} (hq : q ∈ ball base (d.radius / 32))
    {i j : ℕ} (hi : d.shift ≤ i) (hij : i ≤ j) (v : Euclidean n) :
    ‖inverseMetricFrame (d.heatAt q i) (d.heatAt_isPositive q i) v‖ ≤
      ‖inverseMetricFrame (d.heatAt q j) (d.heatAt_isPositive q j) v‖ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  clear hij
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep := inverseMetricFrame_mono (d.heatAt q (i + k)) (d.heatAt q (i + k + 1))
        (d.heatAt_isPositive q (i + k)) (d.heatAt_isPositive q (i + k + 1))
        (d.heatAt_decrement_positive hq (i + k) (by omega)) v
      exact ih.trans hstep

/-- A coarser exact harmonic frame is bounded by the actual fine frozen
heat frame. This supplies the global separation bound for patch supports. -/
theorem coarse_frame_le_frozen {q : X} (hq : q ∈ ball base (d.radius / 32))
    (i j : ℕ) (hj : d.shift ≤ j) (hji : j ≤ d.shift + i + 17) (v : Euclidean n) :
    ‖coordinateFrame (d.frameAt q hq j) v‖ ≤ 2 * ‖d.frozenAt q i v‖ := by
  have h := (d.mean_heat_frame_comparison q hq j hj v).1.trans
    (mul_le_mul_of_nonneg_left (d.heat_frame_mono_indices hq hj hji v) (by norm_num : (0 : ℝ) ≤ 3 / 2))
  change ‖coordinateFrame (d.frameAt q hq j) v‖ ≤ 2 *
    ‖inverseMetricFrame (d.heatAt q (d.shift + i + 17)) (d.heatAt_isPositive q _) v‖
  linarith [norm_nonneg (inverseMetricFrame (d.heatAt q (d.shift + i + 17)) (d.heatAt_isPositive q _) v)]

end RegularBilinearData
end RegularPointCoordinates

end

end OAI
