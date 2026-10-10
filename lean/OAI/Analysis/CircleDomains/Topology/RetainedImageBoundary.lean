import OAI.Analysis.CircleDomains.Topology.RetainedJordanSides

namespace OAI

/-! The actual image boundary of a retained source collar, and its bounded
side. Schoenflies supplies only a chart for the embedded image circle. -/

open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem exists_jordan_image_retained_boundary
    (hsch : PlanarSchoenflies) {G : Set Sphere}
    {f : Sphere → Sphere} (hf : ContinuousOn f G) (hi : InjOn f G)
    (hinf : OnePoint.infty ∈ G) (hfix : f OnePoint.infty = OnePoint.infty)
    (H : ℂ ≃ₜ ℂ)
    (hbd : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G) :
    ∃ J : ℂ ≃ₜ ℂ,
      f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)) =
        ((↑) : ℂ → Sphere) '' frontier (jordanInterior J) := by
  let γ : Circle → Sphere := fun t => (H (t : ℂ) : ℂ)
  have hγ : Continuous γ := OnePoint.continuous_coe.comp
    (H.continuous.comp continuous_subtype_val)
  have hγG (t : Circle) : γ t ∈ G :=
    hbd ⟨H t, by rw [frontier_jordanInterior]; exact ⟨t, t.property, rfl⟩, rfl⟩
  have hfinite (t : Circle) : f (γ t) ≠ OnePoint.infty :=
    finite_image_of_fixes_infty hi hinf hfix (hγG t)
  let δ : Circle → ℂ := fun t => finiteCoord (f (γ t))
  have hδc (t : Circle) : (δ t : Sphere) = f (γ t) :=
    CannonMobius.coe_coordinate (hfinite t)
  have hδ : Continuous δ := by
    apply OnePoint.isOpenEmbedding_coe.isInducing.continuous_iff.mpr
    have he : ((↑) : ℂ → Sphere) ∘ δ = f ∘ γ := funext hδc
    rw [he]
    exact hf.comp_continuous hγ hγG
  have hδi : Injective δ := by
    intro x y hxy
    apply Subtype.ext
    apply H.injective
    apply OnePoint.coe_injective
    apply hi (hγG x) (hγG y)
    exact (hδc x).symm.trans ((congrArg ((↑) : ℂ → Sphere) hxy).trans (hδc y))
  obtain ⟨J, hJ⟩ := hsch δ hδ hδi
  refine ⟨J, ?_⟩
  rw [frontier_jordanInterior_eq_circle_range J δ hJ, frontier_jordanInterior]
  ext p
  constructor
  · rintro ⟨_, ⟨_, ⟨z, hz, rfl⟩, rfl⟩, rfl⟩
    exact ⟨δ ⟨z, hz⟩, ⟨⟨z, hz⟩, rfl⟩, hδc ⟨z, hz⟩⟩
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨γ t, ⟨H t, ⟨t, t.property, rfl⟩, rfl⟩, (hδc t).symm⟩

 theorem target_closed_collar_subset_image
    {G S V : Set Sphere} {f : Sphere → Sphere} (H J : ℂ ≃ₜ ℂ)
    (hbd : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G)
    (hboundary : f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior J))
    (hside : f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior H)) =
      V ∩ (((↑) : ℂ → Sphere) '' jordanInterior J))
    (hsource : G ∩ closedTerminalCap H ⊆ S) :
    V ∩ closedTerminalCap J ⊆ f '' S := by
  rintro _ ⟨hyV, z, hz, rfl⟩
  by_cases hzi : z ∈ jordanInterior J
  · have hyt : (z : Sphere) ∈ f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior H)) :=
      hside.symm ▸ ⟨hyV, z, hzi, rfl⟩
    obtain ⟨x, hx, he⟩ := hyt
    refine ⟨x, hsource ⟨hx.1, ?_⟩, he⟩
    obtain ⟨w, hw, rfl⟩ := hx.2
    exact ⟨w, subset_closure hw, rfl⟩
  · have hzfront : z ∈ frontier (jordanInterior J) :=
      ⟨hz, (jordanInterior_isOpen J).interior_eq.symm ▸ hzi⟩
    obtain ⟨x, hx, he⟩ := hboundary.symm ▸
      (show (z : Sphere) ∈ ((↑) : ℂ → Sphere) '' frontier (jordanInterior J) from
        ⟨z, hzfront, rfl⟩)
    refine ⟨x, hsource ⟨hbd hx, ?_⟩, he⟩
    obtain ⟨w, hw, rfl⟩ := hx
    exact ⟨w, frontier_subset_closure hw, rfl⟩

end CircleDomainRigidity

end

end OAI
