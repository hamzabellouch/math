import OAI.Analysis.CircleDomains.Uniformization.Conformal
import OAI.Geometry.Cannon.Conformal.Sphere

namespace OAI

/-!
# Composition in the concrete sphere charts

The finite and infinite charts are locally inverse at their centers.
The ordinary complex chain rule therefore proves composition of the
actual conformal-equivalence predicate used by the main statements.
-/

open Set Filter Classical
open scoped Topology OnePoint

noncomputable section

namespace CircleDomainRigidity

def chartTransform (p : Sphere) : Sphere ≃ₜ Sphere :=
  if p = ∞ then CannonMobius.inversion else Homeomorph.refl _

theorem chartTransform_involutive (p : Sphere) : Function.Involutive (chartTransform p) := by
  by_cases hp : p = ∞
  · rw [chartTransform, ite_eq_left hp]
    change Function.Involutive CannonMobius.inv
    exact CannonMobius.inv_involutive
  · simp only [chartTransform, ite_eq_right hp, Homeomorph.refl_apply]
    exact fun _ => rfl

theorem chart_eq_coordinate_transform (p q : Sphere) :
    chart p q = CannonMobius.coordinate (chartTransform p q) := by
  unfold chart chartTransform
  split_ifs <;> rfl

theorem chartSymm_eq_transform (p : Sphere) (z : ℂ) :
    chartSymm p z = chartTransform p (z : Sphere) := by
  unfold chartSymm chartTransform
  split_ifs <;> rfl

theorem chartTransform_center_ne_infty (p : Sphere) : chartTransform p p ≠ ∞ := by
  by_cases hp : p = ∞
  · subst p
    rw [chartTransform, ite_eq_left rfl]
    change CannonMobius.inv ∞ ≠ ∞
    exact OnePoint.coe_ne_infty 0
  · rw [chartTransform, ite_eq_right hp]
    exact hp

theorem chartSymm_chart_of_ne (p q : Sphere) (hq : chartTransform p q ≠ ∞) :
    chartSymm p (chart p q) = q := by
  rw [chartSymm_eq_transform, chart_eq_coordinate_transform, CannonMobius.coe_coordinate hq]
  exact chartTransform_involutive p q

theorem chartSymm_chart_self (p : Sphere) : chartSymm p (chart p p) = p :=
  chartSymm_chart_of_ne p p (chartTransform_center_ne_infty p)

theorem continuous_chartSymm (p : Sphere) : Continuous (chartSymm p) := by
  have heq : chartSymm p = fun z : ℂ => chartTransform p (z : Sphere) :=
    funext (chartSymm_eq_transform p)
  rw [heq]
  exact (chartTransform p).continuous.comp OnePoint.continuous_coe

theorem eventually_chartSymm_chart (p : Sphere) :
    ∀ᶠ q in 𝓝 p, chartSymm p (chart p q) = q := by
  have hn : ∀ᶠ q in 𝓝 p, chartTransform p q ≠ ∞ :=
    ((chartTransform p).continuous.continuousAt).eventually
      (isOpen_compl_singleton.mem_nhds (chartTransform_center_ne_infty p))
  exact hn.mono (fun q hq => chartSymm_chart_of_ne p q hq)

theorem IsConformalAt.comp {f g : Sphere → Sphere} {p : Sphere}
    (hg : IsConformalAt g (f p)) (hf : IsConformalAt f p) : IsConformalAt (g ∘ f) p := by
  obtain ⟨hfc, df, hdf, hfder⟩ := hf
  obtain ⟨hgc, dg, hdg, hgder⟩ := hg
  refine ⟨hgc.comp hfc, dg * df, mul_ne_zero hdg hdf, ?_⟩
  have hx : chart (f p) (f (chartSymm p (chart p p))) = chart (f p) (f p) := by
    rw [chartSymm_chart_self]
  have hgder' : HasDerivAt
      (fun z => chart (g (f p)) (g (chartSymm (f p) z))) dg
      (chart (f p) (f (chartSymm p (chart p p)))) := hx.symm ▸ hgder
  have hd := hgder'.comp (chart p p) hfder
  have hcont : Tendsto (fun z => f (chartSymm p z)) (𝓝 (chart p p)) (𝓝 (f p)) := by
    have hfc' : ContinuousAt f (chartSymm p (chart p p)) := by
      rw [chartSymm_chart_self]
      exact hfc
    have hc := hfc'.comp (continuous_chartSymm p).continuousAt
    simpa only [Function.comp_def, chartSymm_chart_self] using hc.tendsto
  have he := hcont.eventually (eventually_chartSymm_chart (f p))
  apply hd.congr_of_eventuallyEq
  filter_upwards [he] with z hz
  change chart (g (f p)) (g (f (chartSymm p z))) =
    chart (g (f p)) (g (chartSymm (f p) (chart (f p) (f (chartSymm p z)))))
  rw [hz]

theorem IsConformalOn.comp {f g : Sphere → Sphere} {U V : Set Sphere}
    (hg : IsConformalOn g V) (hf : IsConformalOn f U) (hUV : MapsTo f U V) :
    IsConformalOn (g ∘ f) U :=
  fun p hp => (hg (f p) (hUV hp)).comp (hf p hp)

theorem IsConformalEquivalence.trans
    {f g : Sphere → Sphere} {U V W : Set Sphere}
    (hf : IsConformalEquivalence f U V) (hg : IsConformalEquivalence g V W) :
    IsConformalEquivalence (g ∘ f) U W := by
  obtain ⟨hfc, hfUV, fi, hfic, hfiVU, hfleft, hfright⟩ := hf
  obtain ⟨hgc, hgVW, gi, hgic, hgiWV, hgleft, hgright⟩ := hg
  refine ⟨hgc.comp hfc hfUV, hgVW.comp hfUV, fi ∘ gi,
    hfic.comp hgic hgiWV, hfiVU.comp hgiWV, ?_, ?_⟩
  · intro z hz
    simp only [Function.comp_apply, hgleft (f z) (hfUV hz), hfleft z hz]
  · intro w hw
    simp only [Function.comp_apply, hfright (gi w) (hgiWV hw), hgright w hw]

theorem IsConformalEquivalence.symm_exists
    {f : Sphere → Sphere} {U V : Set Sphere} (hf : IsConformalEquivalence f U V) :
    ∃ g : Sphere → Sphere, IsConformalEquivalence g V U := by
  obtain ⟨hfc, hfUV, g, hgc, hgVU, hleft, hright⟩ := hf
  exact ⟨g, hgc, hgVU, f, hfc, hfUV, hright, hleft⟩

theorem IsConformalEquivalence.bijOn
    {f : Sphere → Sphere} {U V : Set Sphere} (hf : IsConformalEquivalence f U V) :
    BijOn f U V := by
  obtain ⟨_, hmap, g, _, hgmap, hleft, hright⟩ := hf
  refine ⟨hmap, ?_, ?_⟩
  · intro x hx y hy hxy
    calc
      x = g (f x) := (hleft x hx).symm
      _ = g (f y) := congrArg g hxy
      _ = y := hleft y hy
  · intro y hy
    exact ⟨g y, hgmap hy, hright y hy⟩

end CircleDomainRigidity

end

end OAI
