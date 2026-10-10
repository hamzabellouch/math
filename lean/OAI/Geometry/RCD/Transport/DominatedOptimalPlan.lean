import OAI.Geometry.RCD.Metric.WeightedProbabilityRecovery

namespace OAI

/-! # Bounded reweightings of an optimal plan remain optimal -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace

omit [SeparableSpace X] in
theorem dominated_optimal_plan
    (π τ : Measure C(Time,X)) [IsFiniteMeasure π]
    (hp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))))
    (hc : transportCost (π.map (fun γ => (γ 0,γ 1)))≠∞)
    (hτ : τ≤(2 : ℝ≥0∞) • π) :
    IsOptimalCoupling (τ.map (fun γ => γ 0)) (τ.map (fun γ => γ 1))
      (τ.map (fun γ => (γ 0,γ 1))) := by
  have hm := (measurable_path_eval (X:=X) 0).prodMk (measurable_path_eval 1)
  have h2 := hp.smul (by norm_num : (2 : ℝ≥0∞)≠0) (by norm_num : (2 : ℝ≥0∞)≠∞)
  let : IsFiniteMeasure ((2 : ℝ≥0∞) • π.map (fun γ => (γ 0,γ 1))) := ⟨by
    change (2 : ℝ≥0∞)*(π.map (fun γ => (γ 0,γ 1))) univ<∞
    exact ENNReal.mul_lt_top (by norm_num) (measure_lt_top _ _)⟩
  have hc2 : transportCost ((2 : ℝ≥0∞) • π.map (fun γ => (γ 0,γ 1)))≠∞ := by
    rw [transportCost_smul]
    exact ENNReal.mul_ne_top (by norm_num) hc
  have hle : τ.map (fun γ => (γ 0,γ 1))≤(2 : ℝ≥0∞) • π.map (fun γ => (γ 0,γ 1)) := by
    rw [← Measure.map_smul _ hm.aemeasurable]
    exact Measure.map_mono hτ hm
  simpa only [Measure.map_map measurable_fst hm,Measure.map_map measurable_snd hm,Function.comp_def]
    using h2.subcoupling hc2 hle

end RegularPointCoordinates

end

end OAI
