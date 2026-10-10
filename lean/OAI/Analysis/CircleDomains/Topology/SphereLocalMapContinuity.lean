import OAI.Analysis.CircleDomains.Sobolev.SmoothSphereCharts

namespace OAI

/-! Continuity of the concrete sphere-chart representative follows from
continuity of the map at the chart center. -/
open Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma continuousAt_sphereLocalMap {f : Sphere → Sphere} {p : Sphere}
    (hf : ContinuousAt f p) :
    ContinuousAt (sphereLocalMap f p) (chart p p) := by
  have hfc : ContinuousAt f (chartSymm p (chart p p)) := by
    rwa [chartSymm_chart_self]
  have hc : ContinuousAt (fun z => chartTransform (f p) (f (chartSymm p z)))
      (chart p p) :=
    (chartTransform (f p)).continuous.continuousAt.comp
      (hfc.comp (continuous_chartSymm p).continuousAt)
  have hn : chartTransform (f p) (f (chartSymm p (chart p p))) ≠ OnePoint.infty := by
    rw [chartSymm_chart_self]
    exact chartTransform_center_ne_infty _
  have hh := (CannonMobius.continuousAt_coordinate hn).comp_of_eq hc rfl
  change ContinuousAt (fun z => chart (f p) (f (chartSymm p z))) (chart p p)
  simp_rw [chart_eq_coordinate_transform]
  simpa only [Function.comp_def, chart_eq_coordinate_transform] using hh

end CircleDomainRigidity

end

end OAI
