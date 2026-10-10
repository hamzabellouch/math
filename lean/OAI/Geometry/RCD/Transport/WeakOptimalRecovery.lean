import OAI.Geometry.RCD.Transport.WeakPlanCost

namespace OAI

/-! # An optimal limit from a recovery sequence with exact limiting cost -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem weak_optimal_of_recovery
    (πs : ℕ → ProbabilityMeasure C(Time,X)) (π ρ : ProbabilityMeasure C(Time,X))
    (hlim : Tendsto πs atTop (𝓝 π))
    (he0 : Tendsto (fun j => (πs j).map (fun γ => γ 0)) atTop (𝓝 (ρ.map (fun γ => γ 0))))
    (he1 : Tendsto (fun j => (πs j).map (fun γ => γ 1)) atTop (𝓝 (ρ.map (fun γ => γ 1))))
    (hcost : Tendsto (fun j => transportCost ((πs j : Measure C(Time,X)).map (fun γ => (γ 0,γ 1))))
      atTop (𝓝 (transportCost ((ρ : Measure C(Time,X)).map (fun γ => (γ 0,γ 1))))))
    (hp : IsOptimalCoupling ((ρ : Measure C(Time,X)).map (fun γ => γ 0))
      ((ρ : Measure C(Time,X)).map (fun γ => γ 1))
      ((ρ : Measure C(Time,X)).map (fun γ => (γ 0,γ 1)))) :
    IsOptimalCoupling ((ρ : Measure C(Time,X)).map (fun γ => γ 0))
      ((ρ : Measure C(Time,X)).map (fun γ => γ 1))
      ((π : Measure C(Time,X)).map (fun γ => (γ 0,γ 1))) := by
  have h0 := congrArg ProbabilityMeasure.toMeasure
    (weak_limit_endpoint πs π _ (ρ.map (fun γ => γ 0)) 0 hlim he0 (fun _ => rfl))
  have h1 := congrArg ProbabilityMeasure.toMeasure
    (weak_limit_endpoint πs π _ (ρ.map (fun γ => γ 1)) 1 hlim he1 (fun _ => rfl))
  have hpair := (measurable_path_eval (X:=X) 0).prodMk (measurable_path_eval 1)
  refine ⟨?_,?_,fun σ hσ0 hσ1 => ?_⟩
  · simpa only [Measure.map_map measurable_fst hpair,Function.comp_def,
      ProbabilityMeasure.toMeasure_map] using h0
  · simpa only [Measure.map_map measurable_snd hpair,Function.comp_def,
      ProbabilityMeasure.toMeasure_map] using h1
  · exact ((weak_transportCost_le_liminf πs π hlim).trans_eq hcost.liminf_eq).trans
      (hp.2.2 σ hσ0 hσ1)

end RegularPointCoordinates

end

end OAI
