import OAI.Probability.ContinuumTransition.KacLimit

namespace OAI

section
open scoped Topology
open Set Filter
namespace ContinuumTemperature

 theorem core_pressure_locally_uniform :
    TendstoLocallyUniformlyOn (fun t : ℝ => physicalPressure (coreProfile t) t)
      (fun x : Parameter => idealCorePressure x.2) atTop pressureDomain := by
  apply convex_pointwise_locally_uniform isOpen_pressureDomain
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    exact convexOn_physicalPressure (measurable_radialPotential (measurable_coreProfile t)) ht
      (coreProfile_stable_zero t) (fun _ _ => le_refl _)
  · intro x hx
    exact core_pressure_tendsto hx x.2

end ContinuumTemperature
end

end OAI
