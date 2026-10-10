import OAI.Geometry.RCD.Coordinates.NormalizedOptimalSubplan

namespace OAI

/-! # Endpoint domination preserves optimality of a path law

This permits a measurable splice to change the paths while keeping its
endpoint coupling inside a finite multiple of an existing optimal coupling.
-/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem optimal_of_endpoint_domination (π τ : Measure C(Time,X)) [IsFiniteMeasure π]
    (hp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))))
    (hfin : transportCost (π.map (fun γ => (γ 0,γ 1)))≠∞)
    {c : ℝ≥0∞} (hc0 : c≠0) (hct : c≠∞)
    (hle : τ.map (fun γ => (γ 0,γ 1))≤c • π.map (fun γ => (γ 0,γ 1))) :
    IsOptimalCoupling (τ.map (fun γ => γ 0)) (τ.map (fun γ => γ 1))
      (τ.map (fun γ => (γ 0,γ 1))) := by
  have hm := (measurable_path_eval (X:=X) 0).prodMk (measurable_path_eval 1)
  let : IsFiniteMeasure (c • π.map (fun γ => (γ 0,γ 1))) :=
    (π.map (fun γ => (γ 0,γ 1))).smul_finite hct
  have hcost : transportCost (c • π.map (fun γ => (γ 0,γ 1)))≠∞ := by
    rw [transportCost_smul]
    exact ENNReal.mul_ne_top hct hfin
  have hs := (hp.smul hc0 hct).subcoupling hcost hle
  simpa only [Measure.map_map measurable_fst hm,Measure.map_map measurable_snd hm,
    Function.comp_def] using hs

end RegularPointCoordinates

end

end OAI
