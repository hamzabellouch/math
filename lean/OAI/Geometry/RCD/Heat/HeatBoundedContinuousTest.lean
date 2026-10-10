import OAI.Geometry.RCD.Heat.HeatMeasureProbability

namespace OAI

/-! # Spatial Lipschitz continuity of bounded continuous heat tests -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology CompactlySupported BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem compactHeatEval_lipschitz (t : ℝ) (ht : 0 < t) (f : C_c(X, ℝ))
    (C : ℝ≥0) (hf : ∀ y, |f y| ≤ C) :
    LipschitzWith ⟨Real.sqrt ((C : ℝ) ^ 2 / (2 * t * Real.exp (-2 * |K| * t))), Real.sqrt_nonneg _⟩
      (fun x => hX.compactHeatEval hn p t ht x f) := by
  let : ProperSpace X := hX.proper K n hn
  let : (hausdorff n X).Regular := inferInstance
  apply hX.boundedHeat_lipschitz hn p _ _ t ht C
  filter_upwards [compactTestToL2_coe (hausdorff n X) f] with y hy
  rw [hy]
  exact hf y

/-- The same quantitative smoothing applies to bounded continuous data
that need not be globally square integrable. -/
theorem heatRadonMeasure_integral_lipschitz (t : ℝ) (ht : 0 < t) (f : X →ᵇ ℝ) :
    LipschitzWith ⟨Real.sqrt (‖f‖ ^ 2 / (2 * t * Real.exp (-2 * |K| * t))), Real.sqrt_nonneg _⟩
      (fun x => ∫ y, f y ∂hX.heatRadonMeasure hn p t ht x) := by
  let F (i : ℕ) : C_c(X, ℝ) :=
    ⟨⟨fun y => f y * radialCutoff p ((i : ℝ) + 1) y,
      f.continuous.mul (radialCutoff_lipschitz p (by positivity)).continuous⟩,
      (radialCutoff_hasCompactSupport p (by positivity)).mul_left⟩
  have hb (i : ℕ) (y : X) : |F i y| ≤ ‖f‖₊ := by
    change |f y * radialCutoff p ((i : ℝ) + 1) y| ≤ ‖f‖
    rw [abs_mul, abs_of_nonneg (radialCutoff_bounds _ _ _).1]
    exact (mul_le_of_le_one_right (abs_nonneg _) (radialCutoff_bounds _ _ _).2).trans
      (f.norm_coe_le_norm y)
  have hlim (x : X) : Tendsto (fun i => hX.compactHeatEval hn p t ht x (F i)) atTop
      (𝓝 (∫ y, f y ∂hX.heatRadonMeasure hn p t ht x)) := by
    simp_rw [← hX.heatRadonMeasure_integral hn p t ht x]
    have h := integral_radialCutoff_tendsto (hX.heatRadonMeasure hn p t ht x) p f
      (f.integrable (hX.heatRadonMeasure hn p t ht x))
    have hr : Tendsto (fun i : ℕ => (i : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    simpa only [Function.comp_def, F] using! h.comp hr
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply le_of_tendsto_of_tendsto ((hlim x).dist (hlim y)) tendsto_const_nhds
  exact Eventually.of_forall fun i =>
    (hX.compactHeatEval_lipschitz hn p t ht (F i) ‖f‖₊ (hb i)).dist_le_mul x y

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
