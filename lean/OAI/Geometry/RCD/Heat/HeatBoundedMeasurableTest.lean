import OAI.Geometry.RCD.Heat.HeatKernelSemigroup

namespace OAI

/-! # Quantitative strong Feller property of the constructed heat family -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

/-- Compact exhaustion extends the quantitative smoothing bound to every
bounded measurable test, including tests outside L². -/
theorem heatRadonMeasure_integral_measurable_lipschitz (t : ℝ) (ht : 0 < t)
    (f : X → ℝ) (hf : Measurable f) (C : ℝ≥0) (hb : ∀ y, |f y| ≤ C) :
    LipschitzWith ⟨Real.sqrt ((C : ℝ) ^ 2 / (2 * t * Real.exp (-2 * |K| * t))),
      Real.sqrt_nonneg _⟩
      (fun x => ∫ y, f y ∂hX.heatRadonMeasure hn p t ht x) := by
  let μ := hausdorff n X
  let F (i : ℕ) (y : X) := f y * radialCutoff p ((i : ℝ) + 1) y
  have hFb (i : ℕ) (y : X) : |F i y| ≤ C := by
    dsimp only [F]
    rw [abs_mul, abs_of_nonneg (radialCutoff_bounds _ _ _).1]
    exact (mul_le_of_le_one_right (abs_nonneg _) (radialCutoff_bounds _ _ _).2).trans (hb y)
  have hFm (i : ℕ) : Measurable (F i) :=
    hf.mul (radialCutoff_lipschitz p (by positivity)).continuous.measurable
  have hFlp (i : ℕ) : MemLp (F i) 2 μ :=
    (radialCutoff_hasCompactSupport p (by positivity)).mul_left.memLp_of_bound
      (hFm i).aestronglyMeasurable C (Eventually.of_forall (hFb i))
  let u (i : ℕ) : Lp ℝ 2 μ := (hFlp i).toLp (F i)
  have hub (i : ℕ) : ∀ᵐ y ∂μ, |u i y| ≤ C := by
    filter_upwards [(hFlp i).coeFn_toLp] with y hy
    rw [hy]
    exact hFb i y
  have he (i : ℕ) (x : X) :
      (∫ y, F i y ∂hX.heatRadonMeasure hn p t ht x) =
        hX.boundedHeat hn p (u i) ⟨C, hub i⟩ t ht x := by
    rw [← hX.heatRadonMeasure_integral_bounded hn p t ht x (u i) C (hub i)]
    exact integral_congr_ae ((hX.heatRadonMeasure_absolutelyContinuous hn p t ht x).ae_le
      (hFlp i).coeFn_toLp.symm)
  have hl (i : ℕ) : LipschitzWith
      ⟨Real.sqrt ((C : ℝ) ^ 2 / (2 * t * Real.exp (-2 * |K| * t))), Real.sqrt_nonneg _⟩
      (fun x => ∫ y, F i y ∂hX.heatRadonMeasure hn p t ht x) := by
    simp_rw [he]
    exact hX.boundedHeat_lipschitz hn p (u i) ⟨C, hub i⟩ t ht C (hub i)
  have hlim (x : X) : Tendsto
      (fun i => ∫ y, F i y ∂hX.heatRadonMeasure hn p t ht x) atTop
      (𝓝 (∫ y, f y ∂hX.heatRadonMeasure hn p t ht x)) := by
    have hfi : Integrable f (hX.heatRadonMeasure hn p t ht x) :=
      (integrable_const (C : ℝ)).mono' hf.aestronglyMeasurable (Eventually.of_forall (hb ·))
    have hr : Tendsto (fun i : ℕ => (i : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    simpa only [Function.comp_def, F] using!
      (integral_radialCutoff_tendsto (hX.heatRadonMeasure hn p t ht x) p f hfi).comp hr
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply le_of_tendsto_of_tendsto ((hlim x).dist (hlim y)) tendsto_const_nhds
  exact Eventually.of_forall fun i => (hl i).dist_le_mul x y

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
