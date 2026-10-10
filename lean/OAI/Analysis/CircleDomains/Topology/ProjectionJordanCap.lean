import OAI.Analysis.CircleDomains.Transfer.SourceTargetEnds

namespace OAI

/-! A continuous extension of the inverse carries a matched closed Jordan
cap into its source cap. The boundary identity prevents crossing the source
curve, and a domain point identifies the correct side. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem inverse_projection_fiber_on_domain
    {G : Set Sphere} {f P : Sphere → Sphere}
    (hInv : ∀ x ∈ G, P (f x) = x)
    (hOut : ∀ y ∉ f '' G, P y ∈ Gᶜ)
    {x y : Sphere} (hx : x ∈ G) : P y = x ↔ y = f x := by
  constructor
  · intro h
    by_cases hy : y ∈ f '' G
    · obtain ⟨z, hz, rfl⟩ := hy
      have he : z = x := (hInv z hz).symm.trans h
      exact congrArg f he
    · exact ((hOut y hy) (h ▸ hx)).elim
  · rintro rfl
    exact hInv x hx

 theorem inverse_projection_matched_cap
    {G : Set Sphere} (hG : IsOpen G) {f P : Sphere → Sphere}
    (hP : Continuous P)
    (hInv : ∀ x ∈ G, P (f x) = x)
    (hOut : ∀ y ∉ f '' G, P y ∈ Gᶜ)
    (H J : ℂ ≃ₜ ℂ)
    (hFront : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G)
    (hBoundary : f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior J))
    (hSide : f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior H)) =
      f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior J)) :
    P '' closedTerminalCap J ⊆ closedTerminalCap H := by
  let U : Set Sphere := ((↑) : ℂ → Sphere) '' jordanInterior H
  let V : Set Sphere := ((↑) : ℂ → Sphere) '' jordanInterior J
  have hU : IsOpen U := OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen H)
  have hV : IsOpen V := OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen J)
  have hUF : frontier U = ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) :=
    frontier_sphere_image_jordanInterior H
  have hVF : frontier V = ((↑) : ℂ → Sphere) '' frontier (jordanInterior J) :=
    frontier_sphere_image_jordanInterior J
  have hAvoid : Disjoint (P '' V) (frontier U) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨y, hy, rfl⟩ hpy
    have hpyG : P y ∈ G := hFront (hUF ▸ hpy)
    have hyf : y = f (P y) :=
      (inverse_projection_fiber_on_domain hInv hOut hpyG).mp rfl
    have hyFront : y ∈ frontier V := by
      rw [hVF, ← hBoundary, hyf]
      exact mem_image_of_mem _ (hUF ▸ hpy)
    exact hyFront.2 (hV.interior_eq.symm ▸ hy)
  have hMeet : (P '' V ∩ U).Nonempty := by
    obtain ⟨z, hz⟩ := (isConnected_frontier_jordanInterior H).nonempty
    have hzF : (z : Sphere) ∈ frontier U := hUF.symm ▸ ⟨z, hz, rfl⟩
    obtain ⟨x, hxG, hxU⟩ := mem_closure_iff_nhds.mp (frontier_subset_closure hzF)
      G (hG.mem_nhds (hFront ⟨z, hz, rfl⟩))
    have hfx : f x ∈ V := by
      have hh : f x ∈ f '' G ∩ V := hSide ▸ mem_image_of_mem f ⟨hxG, hxU⟩
      exact hh.2
    exact ⟨P (f x), ⟨f x, hfx, rfl⟩, by simpa only [hInv x hxG] using hxU⟩
  have hCover : P '' V ⊆ U ∪ (closure U)ᶜ := by
    intro y hy
    by_cases hyU : y ∈ U
    · exact Or.inl hyU
    · exact Or.inr fun hycl => Set.disjoint_left.mp hAvoid hy
        ⟨hycl, by simpa only [hU.interior_eq] using hyU⟩
  have hconn : IsPreconnected V :=
    (isConnected_jordanInterior J).isPreconnected.image _ OnePoint.continuous_coe.continuousOn
  have hsub : P '' V ⊆ U := (hconn.image P hP.continuousOn).subset_left_of_subset_union
    hU isClosed_closure.isOpen_compl
    (Set.disjoint_left.mpr fun _ h₁ h₂ => h₂ (subset_closure h₁)) hCover hMeet
  have hcl : P '' closure V ⊆ closure U :=
    hP.continuousOn.image_closure.trans (closure_mono hsub)
  simpa only [U, V, closedTerminalCap, closure_sphere_image_jordanInterior] using hcl

end CircleDomainRigidity

end

end OAI
