import OAI.Analysis.CircleDomains.Topology.FinitePlaneEmbedding
import OAI.Analysis.CircleDomains.Uniformization.ConformalLocalInverse

namespace OAI

/-! The finite part of an injective conformal sphere map fixing infinity is
an actual holomorphic open embedding on its finite domain. -/
open Set Function
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity

lemma IsConformalOn.finite_open_embedding
    {f : Sphere → Sphere} {U : Set Sphere} (hf : IsConformalOn f U)
    (hU : IsOpen U) (hi : InjOn f U) (hinf : ∞ ∈ U) (hfix : f ∞=∞) :
    DifferentiableOn ℂ (fun z : ℂ => finiteCoord (f (z : Sphere)))
        (((↑) : ℂ → Sphere) ⁻¹' U) ∧
    (∀ S : Set ℂ, IsOpen S → S ⊆ ((↑) : ℂ → Sphere) ⁻¹' U →
      IsOpen ((fun z : ℂ => finiteCoord (f (z : Sphere))) '' S)) ∧
    InjOn (fun z : ℂ => finiteCoord (f (z : Sphere)))
        (((↑) : ℂ → Sphere) ⁻¹' U) := by
  have hfin (z : ℂ) (hz : (z : Sphere) ∈ U) : f (z : Sphere) ≠ ∞ :=
    finite_image_of_fixes_infty hi hinf hfix hz
  refine ⟨fun z hz => (analyticAt_finite_map_of_conformal hU hf hz
    (hfin z hz)).differentiableAt.differentiableWithinAt, ?_, ?_⟩
  · intro S hS hSU
    rw [finite_part_image_eq (fun z hz => hfin z (hSU hz))]
    apply IsOpen.preimage OnePoint.continuous_coe
    exact hf.isOpen_image hU (OnePoint.isOpen_image_coe.mpr hS)
      (by rintro _ ⟨z,hz,rfl⟩; exact hSU hz)
  · intro x hx y hy he
    apply OnePoint.coe_injective
    apply hi hx hy
    exact (coe_finiteCoord (hfin x hx)).symm.trans
      ((congrArg ((↑) : ℂ → Sphere) he).trans (coe_finiteCoord (hfin y hy)))

lemma finite_part_sphere_image {f : Sphere → Sphere} {S : Set ℂ}
    (hfin : ∀ z ∈ S, f (z : Sphere) ≠ ∞) :
    ((↑) : ℂ → Sphere) '' ((fun z : ℂ => finiteCoord (f (z : Sphere))) '' S) =
      f '' (((↑) : ℂ → Sphere) '' S) := by
  rw [image_image, image_image]
  exact image_congr (fun z hz => coe_finiteCoord (hfin z hz))

end CircleDomainRigidity

end

end OAI
