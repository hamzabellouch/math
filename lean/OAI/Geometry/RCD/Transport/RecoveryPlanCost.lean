import OAI.Geometry.RCD.Transport.BoundedOptimalRecovery
import OAI.Geometry.RCD.Transport.WeakPlanCost

namespace OAI

/-! # Full cost convergence from the integrable recovery moment -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem path_cost_integrable (ρ : Measure C(Time,X))
    (hc : transportCost (ρ.map (fun γ => (γ 0,γ 1)))≠∞) :
    Integrable (fun γ : C(Time,X) => dist (γ 0) (γ 1)^2) ρ := by
  refine ⟨(((continuous_eval_const 0).dist (continuous_eval_const 1)).pow 2).measurable.aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => sq_nonneg _)]
  rw [←path_transportCost]
  exact lt_top_iff_ne_top.mpr hc

theorem recovery_cost_tendsto
    (ρs : ℕ → ProbabilityMeasure C(Time,X)) (ρ : ProbabilityMeasure C(Time,X))
    (hdom : ∀ j, (ρs j : Measure C(Time,X))≤(2 : ℝ≥0∞) • (ρ : Measure C(Time,X)))
    (hc : transportCost ((ρ : Measure C(Time,X)).map (fun γ => (γ 0,γ 1)))≠∞)
    (hm : Tendsto (fun j => ∫γ,dist (γ 0) (γ 1)^2 ∂(ρs j : Measure C(Time,X)))
      atTop (𝓝 (∫γ,dist (γ 0) (γ 1)^2 ∂(ρ : Measure C(Time,X))))) :
    Tendsto (fun j => transportCost ((ρs j : Measure C(Time,X)).map (fun γ => (γ 0,γ 1))))
      atTop (𝓝 (transportCost ((ρ : Measure C(Time,X)).map (fun γ => (γ 0,γ 1))))) := by
  have hi := path_cost_integrable (ρ : Measure C(Time,X)) hc
  have hij (j) : Integrable (fun γ : C(Time,X) => dist (γ 0) (γ 1)^2) (ρs j : Measure C(Time,X)) := by
    apply (hi.smul_measure (by norm_num : (2 : ℝ≥0∞)≠∞)).mono_measure
    exact hdom j
  simp_rw [transportCost_plan_eq_integral _ (hij _)]
  rw [transportCost_plan_eq_integral _ hi]
  exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp hm

end RegularPointCoordinates

end

end OAI
