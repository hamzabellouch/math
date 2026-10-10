import OAI.Analysis.CircleDomains.Uniformization.ConformalComposition

namespace OAI

/-! Conformality is unchanged by equality on an open source set. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem IsConformalAt.congr_of_eventuallyEq {f g : Sphere → Sphere} {p : Sphere}
    (hf : IsConformalAt f p) (he : g =ᶠ[𝓝 p] f) : IsConformalAt g p := by
  have hp : g p = f p := he.eq_of_nhds
  refine ⟨hf.1.congr_of_eventuallyEq he, hf.2.choose, hf.2.choose_spec.1, ?_⟩
  apply hf.2.choose_spec.2.congr_of_eventuallyEq
  have hc : Tendsto (chartSymm p) (𝓝 (chart p p)) (𝓝 p) := by
    simpa only [chartSymm_chart_self] using
      (continuous_chartSymm p).tendsto (chart p p)
  filter_upwards [hc.eventually he] with z hz
  rw [hp,hz]

 theorem IsConformalOn.congr_eqOn {G : Set Sphere} {f g : Sphere → Sphere}
    (hf : IsConformalOn f G) (hG : IsOpen G) (he : EqOn g f G) : IsConformalOn g G := by
  intro p hp
  apply (hf p hp).congr_of_eventuallyEq
  filter_upwards [hG.mem_nhds hp] with x hx
  exact he hx

end CircleDomainRigidity

end

end OAI
