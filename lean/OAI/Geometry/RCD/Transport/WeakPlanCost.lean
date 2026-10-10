import OAI.Geometry.RCD.Transport.WeakGeodesicPlan

namespace OAI

/-! # Lower semicontinuity of the full transport cost

The cost is not truncated and no common bounded support is needed.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem path_transportCost (π : Measure C(Time,X)) :
    transportCost (π.map (fun γ => (γ 0,γ 1)))=
      ∫⁻γ,ENNReal.ofReal (dist (γ 0) (γ 1)^2) ∂π := by
  rw [transportCost,lintegral_map
    ((measurable_fst.dist measurable_snd).ennreal_ofReal.pow_const 2)
    ((measurable_path_eval 0).prodMk (measurable_path_eval 1))]
  exact lintegral_congr fun γ => (ENNReal.ofReal_pow dist_nonneg 2).symm

theorem weak_transportCost_le_liminf
    (πs : ℕ → ProbabilityMeasure C(Time,X)) (π : ProbabilityMeasure C(Time,X))
    (hlim : Tendsto πs atTop (𝓝 π)) :
    transportCost ((π : Measure C(Time,X)).map (fun γ => (γ 0,γ 1)))≤
      liminf (fun j => transportCost ((πs j : Measure C(Time,X)).map (fun γ => (γ 0,γ 1)))) atTop := by
  simp_rw [path_transportCost]
  exact lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
    (((continuous_eval_const 0).dist (continuous_eval_const 1)).pow 2)
    (fun _ => sq_nonneg _)
    (fun _ hU => ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hU)

end RegularPointCoordinates

end

end OAI
