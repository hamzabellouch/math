import OAI.Analysis.CircleDomains.Sobolev.SmoothSphereCharts

namespace OAI

/-!
# Local inverses in sphere charts

On an open set the chart expressions of a conformal sphere map are
analytic. The ordinary complex inverse function theorem therefore
identifies its neighborhood filters. An injective conformal map then
has a conformal inverse on its image, with no global extension assumed.
-/

open Set Filter Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem IsConformalOn.analyticAt_sphereLocalMap
    {f : Sphere → Sphere} {U : Set Sphere} (hf : IsConformalOn f U)
    (hU : IsOpen U) {p : Sphere} (hp : p ∈ U) :
    AnalyticAt ℂ (sphereLocalMap f p) (chart p p) := by
  let g : Sphere → Sphere := chartTransform (f p) ∘ f ∘ chartTransform p
  let V : Set Sphere := (chartTransform p) ⁻¹' U
  have hV : IsOpen V := hU.preimage (chartTransform p).continuous
  have hg : IsConformalOn g V := by
    intro q hq
    exact (isConformalAt_chartTransform _ _).comp
      ((hf _ hq).comp (isConformalAt_chartTransform _ q))
  have hcenter : chartTransform p ((chart p p : ℂ) : Sphere) = p := by
    rw [← chartSymm_eq_transform]
    exact chartSymm_chart_self p
  have hzV : ((chart p p : ℂ) : Sphere) ∈ V := by
    change chartTransform p ((chart p p : ℂ) : Sphere) ∈ U
    rwa [hcenter]
  have hfin : g ((chart p p : ℂ) : Sphere) ≠ OnePoint.infty := by
    change chartTransform (f p) (f (chartTransform p ((chart p p : ℂ) : Sphere))) ≠ _
    rw [hcenter]
    exact chartTransform_center_ne_infty _
  have ha := analyticAt_finite_map_of_conformal hV hg hzV hfin
  have heq : (fun w : ℂ => finiteCoord (g (w : Sphere))) = sphereLocalMap f p := by
    funext w
    rw [sphereLocalMap, chart_eq_coordinate_transform, chartSymm_eq_transform]
    rfl
  rwa [heq] at ha

theorem map_chartSymm_nhds (p : Sphere) :
    map (chartSymm p) (𝓝 (chart p p)) = 𝓝 p := by
  have he : chartSymm p = fun z : ℂ => chartTransform p (z : Sphere) :=
    funext (chartSymm_eq_transform p)
  rw [he]
  change map (chartTransform p ∘ ((↑) : ℂ → Sphere)) (𝓝 (chart p p)) = _
  rw [← map_map, ← OnePoint.nhds_coe_eq, (chartTransform p).map_nhds_eq]
  congr 1
  rw [← chartSymm_eq_transform, chartSymm_chart_self]

theorem IsConformalOn.map_nhds_eq
    {f : Sphere → Sphere} {U : Set Sphere} (hf : IsConformalOn f U)
    (hU : IsOpen U) {p : Sphere} (hp : p ∈ U) : map f (𝓝 p) = 𝓝 (f p) := by
  obtain ⟨hc, d, hd, hder⟩ := hf p hp
  have ha : ContDiffAt ℂ 1 (sphereLocalMap f p) (chart p p) :=
    (hf.analyticAt_sphereLocalMap hU hp).contDiffAt
  have hstrict : HasStrictDerivAt (sphereLocalMap f p) d (chart p p) :=
    ha.hasStrictDerivAt' hder (by norm_num)
  have hcenter : sphereLocalMap f p (chart p p) = chart (f p) (f p) := by
    simp only [sphereLocalMap, chartSymm_chart_self]
  have heq : (f ∘ chartSymm p) =ᶠ[𝓝 (chart p p)]
      (chartSymm (f p) ∘ sphereLocalMap f p) := by
    have ht : Tendsto (f ∘ chartSymm p) (𝓝 (chart p p)) (𝓝 (f p)) := by
      have hc' : ContinuousAt f (chartSymm p (chart p p)) := by
        rwa [chartSymm_chart_self]
      simpa only [Function.comp_apply, chartSymm_chart_self] using
        (hc'.comp (continuous_chartSymm p).continuousAt).tendsto
    filter_upwards [ht.eventually (eventually_chartSymm_chart (f p))] with z hz
    exact hz.symm
  calc
    map f (𝓝 p) = map (f ∘ chartSymm p) (𝓝 (chart p p)) := by
      rw [← map_map, map_chartSymm_nhds]
    _ = map (chartSymm (f p) ∘ sphereLocalMap f p) (𝓝 (chart p p)) := map_congr heq
    _ = map (chartSymm (f p)) (𝓝 (chart (f p) (f p))) := by
      rw [← map_map, hstrict.map_nhds_eq hd, hcenter]
    _ = 𝓝 (f p) := map_chartSymm_nhds (f p)

theorem IsConformalOn.isOpen_image
    {f : Sphere → Sphere} {U O : Set Sphere} (hf : IsConformalOn f U)
    (hU : IsOpen U) (hO : IsOpen O) (hOU : O ⊆ U) : IsOpen (f '' O) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro _ ⟨p, hp, rfl⟩
  rw [← hf.map_nhds_eq hU (hOU hp)]
  exact image_mem_map (hO.mem_nhds hp)

end CircleDomainRigidity

end

end OAI
