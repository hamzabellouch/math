import OAI.Analysis.CircleDomains.Topology.ImageCoreJordan
import OAI.Analysis.CircleDomains.Sobolev.SmoothRealSphereMaps
import OAI.Analysis.CircleDomains.Topology.ExteriorSeparation

namespace OAI

/-! Openness, injectivity and continuity of the actual finite-plane maps induced by the
normalized smooth sphere equivalences. -/

open Set Function
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity

theorem IsSmoothSphereAt.continuousAt_finite_map
    {f : Sphere → Sphere} {z : ℂ} (hf : IsSmoothSphereAt f (z : Sphere))
    (hfinite : f (z : Sphere) ≠ OnePoint.infty) :
    ContinuousAt (fun w : ℂ => finiteCoord (f (w : Sphere))) z := by
  have he : sphereLocalMap f (z : Sphere) =
      fun w : ℂ => finiteCoord (f (w : Sphere)) := by
    funext w
    simp only [sphereLocalMap, chart, hfinite, ite_false, chartSymm_coe_apply]
  have hd := hf.2
  rw [he, chart_coe_self] at hd
  exact hd.continuousAt

theorem finite_part_image_eq {f : Sphere → Sphere} {S : Set ℂ}
    (hfinite : ∀ z ∈ S, f (z : Sphere) ≠ OnePoint.infty) :
    (fun z : ℂ => finiteCoord (f (z : Sphere))) '' S =
      ((↑) : ℂ → Sphere) ⁻¹' (f '' (((↑) : ℂ → Sphere) '' S)) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, ⟨x, hx, rfl⟩, (coe_finiteCoord (hfinite x hx)).symm⟩
  · rintro ⟨p, ⟨x, hx, rfl⟩, he⟩
    exact ⟨x, hx, by change finiteCoord (f (x : Sphere)) = z; rw [he, finiteCoord_coe]⟩

theorem IsSmoothSphereEquivalence.finite_open_embedding
    {f fi : Sphere → Sphere} {U V : Set Sphere} (h : IsSmoothSphereEquivalence f fi U V)
    (hinf : OnePoint.infty ∈ U) (hfix : f OnePoint.infty = OnePoint.infty) (hV : IsOpen V) :
    ContinuousOn (fun z : ℂ => finiteCoord (f (z : Sphere))) (((↑) : ℂ → Sphere) ⁻¹' U) ∧
      (∀ S : Set ℂ, IsOpen S → S ⊆ ((↑) : ℂ → Sphere) ⁻¹' U →
        IsOpen ((fun z : ℂ => finiteCoord (f (z : Sphere))) '' S)) ∧
      InjOn (fun z : ℂ => finiteCoord (f (z : Sphere))) (((↑) : ℂ → Sphere) ⁻¹' U) := by
  refine ⟨fun z hz => ((h.smooth _ hz).continuousAt_finite_map
    (h.finite_forward hinf hfix hz)).continuousWithinAt, ?_, ?_⟩
  · intro S hS hSU
    rw [finite_part_image_eq (fun z hz => h.finite_forward hinf hfix (hSU hz))]
    apply IsOpen.preimage OnePoint.continuous_coe
    apply h.isOpen_image hV (OnePoint.isOpen_image_coe.mpr hS)
    rintro _ ⟨z, hz, rfl⟩
    exact hSU hz
  · intro x hx y hy he
    apply OnePoint.coe_injective
    apply h.bijOn.injOn hx hy
    exact (coe_finiteCoord (h.finite_forward hinf hfix hx)).symm.trans
      ((congrArg ((↑) : ℂ → Sphere) he).trans (coe_finiteCoord (h.finite_forward hinf hfix hy)))

end CircleDomainRigidity

end

end OAI
