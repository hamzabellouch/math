import OAI.Geometry.RCD.Sobolev.LipschitzL2PointControl

namespace OAI

/-! # Uniform Lipschitz bounds turn L² convergence into pointwise convergence -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A fixed positive ball witnesses every persistent nonzero value. -/
theorem tendsto_zero_of_uniform_lipschitz_l2 (μ : Measure X) [ProperSpace X]
    [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    (u : ℕ → Lp ℝ 2 μ) (v : ℕ → X → ℝ) (L : ℝ≥0)
    (hrep : ∀ i, u i =ᵐ[μ] v i) (hLip : ∀ i, LipschitzWith L (v i))
    (hlim : Tendsto (fun i => ‖u i‖) atTop (𝓝 0)) (x : X) :
    Tendsto (fun i => v i x) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let r := ε / (2 * ((L : ℝ) + 1))
  have hr : 0 < r := by dsimp [r]; positivity
  have hLr : (L : ℝ) * r ≤ ε / 2 := by
    dsimp [r]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < 2 * ((L : ℝ) + 1))).mpr
    nlinarith
  have hm : 0 < μ.real (ball x r) :=
    ENNReal.toReal_pos (measure_ball_pos μ x hr).ne' measure_ball_lt_top.ne
  have hq : 0 < (ε / 2) ^ 2 * μ.real (ball x r) := by positivity
  have hlim2 : Tendsto (fun i => ‖u i‖ ^ 2) atTop (𝓝 0) := by
    simpa using hlim.pow 2
  filter_upwards [hlim2.eventually (gt_mem_nhds hq)] with i hi
  rw [Real.dist_eq, sub_zero]
  by_contra hnot
  have hvalue : ε / 2 + (L : ℝ) * r ≤ |v i x| := by
    have hh : ε ≤ |v i x| := le_of_not_gt hnot
    linarith
  have hlower := lipschitz_value_sq_mass μ (u i) (v i) (hrep i) L (hLip i)
    x measure_ball_lt_top.ne (by positivity : 0 ≤ ε / 2) hvalue
  exact (not_le_of_gt hi) hlower

namespace NoncollapsedRCD

variable {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (p : X)
  [ProperSpace X] [SeparableSpace X] [IsLocallyFiniteMeasure (hausdorff n X)]
  [(hausdorff n X).Regular]

/-- Uniformly bounded L² data tending to zero have heat values tending to
zero at every point. The proof uses no kernel estimate. -/
theorem boundedHeat_tendsto_zero (f : ℕ → Lp ℝ 2 (hausdorff n X)) (C : ℝ≥0)
    (hf : ∀ i, ∀ᵐ x ∂hausdorff n X, |f i x| ≤ C)
    (hlim : Tendsto f atTop (𝓝 0)) (t : ℝ) (ht : 0 < t) (x : X) :
    Tendsto (fun i => hX.boundedHeat hn p (f i) ⟨C, hf i⟩ t ht x) atTop (𝓝 0) := by
  let := hX.openPos K n
  apply tendsto_zero_of_uniform_lipschitz_l2 (hausdorff n X)
    (fun i => heatAt (hausdorff n X) hX.quadratic t (f i))
    (fun i => hX.boundedHeat hn p (f i) ⟨C, hf i⟩ t ht)
    ⟨Real.sqrt ((C : ℝ) ^ 2 / (2 * t * Real.exp (-2 * |K| * t))), Real.sqrt_nonneg _⟩
    (fun i => hX.boundedHeat_represents hn p (f i) ⟨C, hf i⟩ t ht)
    (fun i => hX.boundedHeat_lipschitz hn p (f i) ⟨C, hf i⟩ t ht C (hf i))
  have hh := ((heatAt (hausdorff n X) hX.quadratic t).continuous.tendsto 0).comp hlim
  simpa only [Function.comp_apply, map_zero, norm_zero] using hh.norm

end NoncollapsedRCD
end RegularPointCoordinates

end

end OAI
