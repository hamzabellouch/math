import OAI.Geometry.RCD.Heat.HeatMeasureMass

namespace OAI

/-! # Continuity of the total mass of the constructed heat measures -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology CompactlySupported

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The standard radial plateau, viewed as a compact continuous test. -/
def radialCompactTest (p : X) (R : ℝ) (hR : 0 < R) : C_c(X, ℝ) :=
  ⟨⟨radialCutoff p R, (radialCutoff_lipschitz p hR).continuous⟩,
    radialCutoff_hasCompactSupport p hR⟩

namespace NoncollapsedRCD

variable {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (p : X)
  [SeparableSpace X] [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

omit [SeparableSpace X] [IsLocallyFiniteMeasure (hausdorff n X)] in
/-- Radial compact tests recover the whole mass by dominated convergence. -/
theorem heatRadonMeasure_mass_limit (t : ℝ) (ht : 0 < t) (x : X) :
    Tendsto (fun i : ℕ => hX.compactHeatEval hn p t ht x
      (radialCompactTest p ((i : ℝ) + 1) (by positivity))) atTop
      (𝓝 ((hX.heatRadonMeasure hn p t ht x).real univ)) := by
  simp_rw [← hX.heatRadonMeasure_integral hn p t ht x]
  have h := integral_radialCutoff_tendsto (hX.heatRadonMeasure hn p t ht x) p
    (fun _ => (1 : ℝ)) (integrable_const 1)
  have hr : Tendsto (fun i : ℕ => (i : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  simpa only [Function.comp_def, radialCompactTest, one_mul, integral_const, smul_eq_mul, mul_one]
    using! h.comp hr

/-- Uniform bounded-data smoothing persists in the limit of compact
cutoffs, so total mass is a Lipschitz function of the initial center. -/
theorem heatRadonMeasure_mass_lipschitz (t : ℝ) (ht : 0 < t) :
    LipschitzWith ⟨Real.sqrt (1 / (2 * t * Real.exp (-2 * |K| * t))), Real.sqrt_nonneg _⟩
      (fun x => (hX.heatRadonMeasure hn p t ht x).real univ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply le_of_tendsto_of_tendsto
    ((hX.heatRadonMeasure_mass_limit hn p t ht x).dist
      (hX.heatRadonMeasure_mass_limit hn p t ht y)) tendsto_const_nhds
  filter_upwards with i
  let f := radialCompactTest p ((i : ℝ) + 1) (by positivity)
  have hb : ∀ᵐ z ∂hausdorff n X, |compactTestToL2 (hausdorff n X) f z| ≤ (1 : ℝ≥0) := by
    filter_upwards [compactTestToL2_coe (hausdorff n X) f] with z hz
    rw [hz]
    change |radialCutoff p ((i : ℝ) + 1) z| ≤ 1
    rw [abs_of_nonneg (radialCutoff_bounds _ _ _).1]
    exact (radialCutoff_bounds _ _ _).2
  have hl := hX.boundedHeat_lipschitz hn p (compactTestToL2 (hausdorff n X) f)
    (compactTestToL2_bounded f) t ht 1 hb
  simpa only [NNReal.coe_one, one_pow] using! hl.dist_le_mul x y

end NoncollapsedRCD
end RegularPointCoordinates

end

end OAI
