import OAI.Analysis.CircleDomains.Uniformization.MetricConformality
import OAI.Analysis.CircleDomains.Uniformization.MobiusConformal

namespace OAI

/-!
# Smooth maps in the concrete sphere charts

This regularity predicate records ordinary real smoothness. For a
holomorphic sphere map it follows from complex analyticity in a
neighborhood; composition follows from the local chart inverse law.
-/

open Set Filter Function
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity

/-- Real smoothness in the same source and target charts as metric conformality. -/
def IsSmoothSphereAt (f : Sphere → Sphere) (p : Sphere) : Prop :=
  ContinuousAt f p ∧ ContDiffAt ℝ ∞ (sphereLocalMap f p) (chart p p)

def IsSmoothSphereOn (f : Sphere → Sphere) (U : Set Sphere) : Prop :=
  ∀ p ∈ U, IsSmoothSphereAt f p

theorem IsSmoothSphereAt.comp {f g : Sphere → Sphere} {p : Sphere}
    (hg : IsSmoothSphereAt g (f p)) (hf : IsSmoothSphereAt f p) :
    IsSmoothSphereAt (g ∘ f) p := by
  refine ⟨hg.1.comp hf.1, ?_⟩
  have hx : sphereLocalMap f p (chart p p) = chart (f p) (f p) := by
    simp only [sphereLocalMap, chartSymm_chart_self]
  have hd := (hx.symm ▸ hg.2).comp (chart p p) hf.2
  have hcont : Tendsto (fun z => f (chartSymm p z)) (𝓝 (chart p p)) (𝓝 (f p)) := by
    have hfc : ContinuousAt f (chartSymm p (chart p p)) := by
      rw [chartSymm_chart_self]
      exact hf.1
    simpa only [Function.comp_def, chartSymm_chart_self] using
      (hfc.comp (continuous_chartSymm p).continuousAt).tendsto
  apply hd.congr_of_eventuallyEq
  filter_upwards [hcont.eventually (eventually_chartSymm_chart (f p))] with z hz
  change chart (g (f p)) (g (f (chartSymm p z))) =
    chart (g (f p)) (g (chartSymm (f p) (chart (f p) (f (chartSymm p z)))))
  rw [hz]

theorem isConformalAt_chartTransform (p q : Sphere) : IsConformalAt (chartTransform p) q := by
  by_cases hp : p = OnePoint.infty
  · rw [chartTransform, ite_eq_left hp]
    exact isConformalAt_inversion q
  · rw [chartTransform, ite_eq_right hp]
    exact isConformalAt_id q

theorem analyticAt_finite_map_of_conformal
    {f : Sphere → Sphere} {U : Set Sphere} (hU : IsOpen U)
    (hf : IsConformalOn f U) {z : ℂ} (hz : (z : Sphere) ∈ U)
    (hfinite : f (z : Sphere) ≠ OnePoint.infty) :
    AnalyticAt ℂ (fun w : ℂ => finiteCoord (f (w : Sphere))) z := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  have hmem : ∀ᶠ w : ℂ in 𝓝 z, (w : Sphere) ∈ U :=
    OnePoint.continuous_coe.continuousAt.eventually (hU.mem_nhds hz)
  have hfin : ∀ᶠ w : ℂ in 𝓝 z, f (w : Sphere) ≠ OnePoint.infty :=
    ((hf _ hz).1.comp OnePoint.continuous_coe.continuousAt).eventually
      (isOpen_compl_singleton.mem_nhds hfinite)
  filter_upwards [hmem, hfin] with w hw hfw
  obtain ⟨_, d, _, hd⟩ := hf _ hw
  have heq : (fun y => chart (f (w : Sphere)) (f (chartSymm (w : Sphere) y))) =
      (fun y : ℂ => finiteCoord (f (y : Sphere))) := by
    funext y
    simp only [chart, hfw, ite_false, chartSymm_coe_apply]
  rw [heq, chart_coe_self] at hd
  exact hd.differentiableAt

theorem IsConformalOn.isSmoothSphereAt
    {f : Sphere → Sphere} {U : Set Sphere} (hf : IsConformalOn f U)
    (hU : IsOpen U) {p : Sphere} (hp : p ∈ U) : IsSmoothSphereAt f p := by
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
  refine ⟨(hf p hp).1, ?_⟩
  rw [heq] at ha
  exact ha.contDiffAt.restrict_scalars ℝ

end CircleDomainRigidity

end

end OAI
