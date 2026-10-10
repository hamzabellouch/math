import OAI.Analysis.CircleDomains.Uniformization.ConformalLocalInverse

namespace OAI

/-!
# The actual inverse of an injective conformal sphere map

Local analytic inverse functions agree with the set-theoretic inverse
on an open source domain. Thus an injective conformal map has a genuine
two-sided conformal equivalence with its image.
-/

open Set Filter Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem continuousAt_conformal_invFunOn
    {f : Sphere → Sphere} {U : Set Sphere} (hf : IsConformalOn f U)
    (hU : IsOpen U) (hinj : InjOn f U) {p : Sphere} (hp : p ∈ U) :
    ContinuousAt (invFunOn f U) (f p) := by
  have hleft : (invFunOn f U ∘ f) =ᶠ[𝓝 p] id := by
    filter_upwards [hU.mem_nhds hp] with x hx
    exact hinj.leftInvOn_invFunOn hx
  change map (invFunOn f U) (𝓝 (f p)) ≤ 𝓝 (invFunOn f U (f p))
  rw [hinj.leftInvOn_invFunOn hp, ← hf.map_nhds_eq hU hp, map_map, map_congr hleft, map_id]

theorem isConformalAt_invFunOn
    {f : Sphere → Sphere} {U : Set Sphere} (hf : IsConformalOn f U)
    (hU : IsOpen U) (hinj : InjOn f U) {p : Sphere} (hp : p ∈ U) :
    IsConformalAt (invFunOn f U) (f p) := by
  obtain ⟨hfc, d, hd, hder⟩ := hf p hp
  have ha : ContDiffAt ℂ 1 (sphereLocalMap f p) (chart p p) :=
    (hf.analyticAt_sphereLocalMap hU hp).contDiffAt
  have hstrict : HasStrictDerivAt (sphereLocalMap f p) d (chart p p) :=
    ha.hasStrictDerivAt' hder (by norm_num)
  let g := invFunOn f U
  have hgp : g (f p) = p := hinj.leftInvOn_invFunOn hp
  let G : ℂ → ℂ := fun z => chart p (g (chartSymm (f p) z))
  have hsource : ∀ᶠ z in 𝓝 (chart p p), chartSymm p z ∈ U := by
    have ht : Tendsto (chartSymm p) (𝓝 (chart p p)) (𝓝 p) := by
      simpa only [chartSymm_chart_self] using
        (continuous_chartSymm p).continuousAt.tendsto (x := chart p p)
    exact ht.eventually (hU.mem_nhds hp)
  have htarget : ∀ᶠ z in 𝓝 (chart p p),
      chartSymm (f p) (chart (f p) (f (chartSymm p z))) = f (chartSymm p z) := by
    have ht : Tendsto (f ∘ chartSymm p) (𝓝 (chart p p)) (𝓝 (f p)) := by
      have hc' : ContinuousAt f (chartSymm p (chart p p)) := by
        rwa [chartSymm_chart_self]
      simpa only [Function.comp_apply, chartSymm_chart_self] using
        (hc'.comp (continuous_chartSymm p).continuousAt).tendsto
    exact ht.eventually (eventually_chartSymm_chart (f p))
  have hleft : ∀ᶠ z in 𝓝 (chart p p), G (sphereLocalMap f p z) = z := by
    filter_upwards [hsource, htarget] with z hz hs
    change chart p (g (chartSymm (f p) (chart (f p) (f (chartSymm p z))))) = z
    rw [hs]
    change chart p (invFunOn f U (f (chartSymm p z))) = z
    rw [hinj.leftInvOn_invFunOn hz, chart_chartSymm]
  have hgd := (hstrict.to_local_left_inverse hd hleft).hasDerivAt
  have hcenter : sphereLocalMap f p (chart p p) = chart (f p) (f p) := by
    simp only [sphereLocalMap, chartSymm_chart_self]
  rw [hcenter] at hgd
  refine ⟨continuousAt_conformal_invFunOn hf hU hinj hp, d⁻¹, inv_ne_zero hd, ?_⟩
  simpa only [G, g, hinj.leftInvOn_invFunOn hp] using hgd

theorem isConformalEquivalence_of_injOn
    {f : Sphere → Sphere} {U : Set Sphere} (hf : IsConformalOn f U)
    (hU : IsOpen U) (hinj : InjOn f U) : IsConformalEquivalence f U (f '' U) := by
  refine ⟨hf, mapsTo_image _ _, invFunOn f U, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact isConformalAt_invFunOn hf hU hinj hp
  · rintro _ ⟨p, hp, rfl⟩
    exact invFunOn_apply_mem hp
  · exact hinj.leftInvOn_invFunOn
  · rintro _ ⟨p, hp, rfl⟩
    exact invFunOn_apply_eq hp

end CircleDomainRigidity

end

end OAI
