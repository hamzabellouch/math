import OAI.Analysis.CircleDomains.Topology.SphereLocalMapContinuity
import OAI.Analysis.CircleDomains.Sobolev.HolomorphicInjOnDerivative

namespace OAI

/-! An analytic local chart of a sphere homeomorphism has nonzero
complex derivative, obtained from genuine local injectivity. -/
open Set Filter Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

def sphereLocalMapRegion (e : Sphere ≃ₜ Sphere) (p : Sphere) : Set ℂ :=
  {z | chartTransform (e p) (e (chartSymm p z)) ≠ OnePoint.infty}

lemma isOpen_sphereLocalMapRegion (e : Sphere ≃ₜ Sphere) (p : Sphere) :
    IsOpen (sphereLocalMapRegion e p) := by
  exact isOpen_compl_singleton.preimage
    ((chartTransform (e p)).continuous.comp (e.continuous.comp (continuous_chartSymm p)))

lemma center_mem_sphereLocalMapRegion (e : Sphere ≃ₜ Sphere) (p : Sphere) :
    chart p p ∈ sphereLocalMapRegion e p := by
  change chartTransform (e p) (e (chartSymm p (chart p p))) ≠ OnePoint.infty
  rw [chartSymm_chart_self]
  exact chartTransform_center_ne_infty _

lemma sphereLocalMap_injOn (e : Sphere ≃ₜ Sphere) (p : Sphere) :
    InjOn (sphereLocalMap e p) (sphereLocalMapRegion e p) := by
  intro z hz w hw heq
  have hz' := chartSymm_chart_of_ne (e p) (e (chartSymm p z)) hz
  have hw' := chartSymm_chart_of_ne (e p) (e (chartSymm p w)) hw
  have hh := congrArg (chartSymm (e p)) heq
  change chartSymm (e p) (chart (e p) (e (chartSymm p z))) =
    chartSymm (e p) (chart (e p) (e (chartSymm p w))) at hh
  rw [hz', hw'] at hh
  have hc := congrArg (chart p) (e.injective hh)
  simpa only [chart_chartSymm] using hc

lemma sphereLocalMap_deriv_ne_zero (e : Sphere ≃ₜ Sphere) (p : Sphere)
    (ha : AnalyticAt ℂ (sphereLocalMap e p) (chart p p)) :
    deriv (sphereLocalMap e p) (chart p p) ≠ 0 := by
  have hd := Complex.analyticAt_iff_eventually_differentiableAt.mp ha
  obtain ⟨V, hV, hVo, hpV⟩ := mem_nhds_iff.mp hd
  apply holomorphicInjOn_deriv_ne_zero
    (hVo.inter (isOpen_sphereLocalMapRegion e p))
    (fun z hz => (hV hz.1).differentiableWithinAt)
    ((sphereLocalMap_injOn e p).mono inter_subset_right)
    ⟨hpV, center_mem_sphereLocalMapRegion e p⟩

end CircleDomainRigidity

end

end OAI
