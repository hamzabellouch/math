import OAI.Analysis.FiniteFactor.BiasedPairs.Measures
import OAI.Analysis.FiniteFactor.L2UniformAbsoluteContinuity
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section

/-- At prefix n, use y in the first n source blocks and x in the tail. -/
def sourceBiasedPrefixMask (n : ℕ) (i : SourceCoordinate) : Bool := decide (i.1 < n)

theorem sourceBiasedPrefixPair_tendsto (ω : SourceBiasedSample) :
    Tendsto (fun n => sourceBiasedPair (sourceBiasedPrefixMask n) ω) atTop
      (𝓝 (sourceBiasedPair (fun _ => true) ω)) := by
  apply Tendsto.prodMk_nhds tendsto_const_nhds
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop i.1] with n hn
  simp [sourceBiasedEndpoint,CouplingParameters.blockProductEndpoint,
    sourceBiasedPrefixMask,hn]

/-- The actual beta_n converge weakly to the actual full biased law nu_j. -/
theorem sourceBiasedPrefix_weak (j : ℕ) :
    Tendsto (fun n => sourceBiasedTorusMeasure j (sourceBiasedPrefixMask n)) atTop
      (𝓝 (sourceBiasedTorusMeasure j (fun _ => true))) := by
  apply FiniteMeasure.tendsto_of_forall_integral_tendsto
  intro f
  have hmap (r : SourceCoordinate → Bool) :
      (∫ z, f z ∂(sourceBiasedTorusMeasure j r : Measure SourceSamplingTorus)) =
        ∫ ω, f (sourceSamplingTorusMap (sourceBiasedPair r ω)) ∂sourceBiasedLaw j := by
    change (∫ z, f z ∂((sourceBiasedLaw j).map (sourceBiasedPair r)).map sourceSamplingTorusMap) = _
    rw [integral_map sourceSamplingTorusMap_continuous.measurable.aemeasurable f.continuous.aestronglyMeasurable]
    exact integral_map (sourceBiasedPair_measurable r).aemeasurable
        (f.continuous.comp sourceSamplingTorusMap_continuous).aestronglyMeasurable
  simp_rw [hmap]
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
  · intro n
    exact ((f.continuous.comp sourceSamplingTorusMap_continuous).measurable.comp
      (sourceBiasedPair_measurable _)).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact Eventually.of_forall fun ω => f.norm_coe_le_norm _
  · apply Eventually.of_forall
    intro ω
    exact (f.continuous.comp sourceSamplingTorusMap_continuous).continuousAt.tendsto.comp
      (sourceBiasedPrefixPair_tendsto ω)

/-- Uniform absolute continuity covers every prefix and both endpoint choices. -/
theorem sourceBiasedPrefix_uniformAC (j : ℕ) (b : Bool) (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ A, MeasurableSet A → sourceTorusHaar A < δ → ∀ n,
      ((sourceBiasedTorusMeasure j (sourceBiasedPrefixMask n) : Measure SourceSamplingTorus).map
        (sourceTorusEndpoint b)) A ≤ ε := by
  apply uniformAC_of_L2_densities sourceTorusHaar _
    (Real.exp (20*(2*(∑' s,sourceKappa s^2)+1))) _ ε hε
  intro n
  obtain ⟨g,_hg,hg0,hglp,hm,hC⟩ := sourceBiasedTorusMeasure_density j (sourceBiasedPrefixMask n) b
  exact ⟨g,hglp,hg0,hm,hC⟩

end
end FiniteFactor

end OAI
