import OAI.Analysis.CircleDomains.Sobolev.SmoothSphereCharts
import OAI.Analysis.CircleDomains.Modulus.ConformalNormalization

namespace OAI

/-!
# Smooth equivalences on sphere regions

Both directions and their actual inverse identities are retained, so a
coordinate can be transported by composing with the constructed inverse.
-/

open Set Function

noncomputable section

namespace CircleDomainRigidity

structure IsSmoothSphereEquivalence (f fi : Sphere → Sphere) (U V : Set Sphere) : Prop where
  smooth : IsSmoothSphereOn f U
  mapsTo : MapsTo f U V
  smooth_inv : IsSmoothSphereOn fi V
  mapsTo_inv : MapsTo fi V U
  left_inv : ∀ p ∈ U, fi (f p) = p
  right_inv : ∀ p ∈ V, f (fi p) = p

theorem IsSmoothSphereEquivalence.bijOn
    {f fi : Sphere → Sphere} {U V : Set Sphere} (h : IsSmoothSphereEquivalence f fi U V) :
    BijOn f U V := by
  refine ⟨h.mapsTo, ?_, ?_⟩
  · intro x hx y hy heq
    simpa only [h.left_inv x hx, h.left_inv y hy] using congrArg fi heq
  · intro y hy
    exact ⟨fi y, h.mapsTo_inv hy, h.right_inv y hy⟩

theorem IsSmoothSphereEquivalence.symm
    {f fi : Sphere → Sphere} {U V : Set Sphere} (h : IsSmoothSphereEquivalence f fi U V) :
    IsSmoothSphereEquivalence fi f V U :=
  ⟨h.smooth_inv, h.mapsTo_inv, h.smooth, h.mapsTo, h.right_inv, h.left_inv⟩

theorem IsSmoothSphereEquivalence.trans
    {f fi g gi : Sphere → Sphere} {U V W : Set Sphere}
    (hf : IsSmoothSphereEquivalence f fi U V) (hg : IsSmoothSphereEquivalence g gi V W) :
    IsSmoothSphereEquivalence (g ∘ f) (fi ∘ gi) U W := by
  refine ⟨fun p hp => (hg.smooth _ (hf.mapsTo hp)).comp (hf.smooth p hp),
    hg.mapsTo.comp hf.mapsTo,
    fun p hp => (hf.smooth_inv _ (hg.mapsTo_inv hp)).comp (hg.smooth_inv p hp),
    hf.mapsTo_inv.comp hg.mapsTo_inv, ?_, ?_⟩
  · intro p hp
    simp only [Function.comp_apply, hg.left_inv _ (hf.mapsTo hp), hf.left_inv p hp]
  · intro p hp
    simp only [Function.comp_apply, hf.right_inv _ (hg.mapsTo_inv hp), hg.right_inv p hp]

theorem IsConformalEquivalence.exists_smooth_inverse
    {f : Sphere → Sphere} {U V : Set Sphere} (hf : IsConformalEquivalence f U V)
    (hU : IsOpen U) (hV : IsOpen V) :
    ∃ fi, IsSmoothSphereEquivalence f fi U V := by
  obtain ⟨hfc, hmap, fi, hfic, himap, hl, hr⟩ := hf
  exact ⟨fi, fun p hp => hfc.isSmoothSphereAt hU hp, hmap,
    fun p hp => hfic.isSmoothSphereAt hV hp, himap, hl, hr⟩

theorem smoothSphereEquivalence_pointToInfinity (p : Sphere) (U : Set Sphere) :
    IsSmoothSphereEquivalence (pointToInfinity p) (pointToInfinity p).symm U
      (pointToInfinity p '' U) := by
  refine ⟨fun q _ => (show IsConformalOn (pointToInfinity p) univ from
    fun r _ => isConformalAt_pointToInfinity p r).isSmoothSphereAt isOpen_univ (mem_univ q),
    mapsTo_image _ _, fun q _ => ?_, ?_, fun q _ => (pointToInfinity p).symm_apply_apply q,
    fun q _ => (pointToInfinity p).apply_symm_apply q⟩
  · exact (show IsConformalOn (pointToInfinity p).symm univ from
      fun r _ => isConformalAt_pointToInfinity_symm p r).isSmoothSphereAt isOpen_univ (mem_univ q)
  · rintro _ ⟨q, hq, rfl⟩
    simpa only [(pointToInfinity p).symm_apply_apply] using hq

end CircleDomainRigidity

end

end OAI
