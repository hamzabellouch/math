import OAI.Analysis.CircleDomains.Reflection.ClosedExteriorExtension

namespace OAI

/-! Boundary images under an actual open embedding, and the selected
boundary of the closed-exterior extension. -/
open Set Function Filter Metric
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma sphere_interior_image_of_open_embedding {f:Sphere→Sphere} {G K:Set Sphere}
    (hc:ContinuousOn f G) (ho:∀S,IsOpen S→S⊆G→IsOpen (f '' S))
    (hG:IsOpen G) (hi:InjOn f G) (hKG:K⊆G) :
    interior (f '' K)=f '' interior K := by
  apply Subset.antisymm
  · intro y hy
    obtain ⟨x,hx,rfl⟩ := interior_subset hy
    have hO : IsOpen (G∩f ⁻¹' interior (f '' K)) :=
      hc.isOpen_inter_preimage hG isOpen_interior
    have hsub : G∩f ⁻¹' interior (f '' K)⊆K := by
      rintro z ⟨hzG,hz⟩
      obtain ⟨w,hw,he⟩ := interior_subset hz
      exact hi (hKG hw) hzG he ▸ hw
    exact ⟨x,interior_maximal hsub hO ⟨hKG hx,hy⟩,rfl⟩
  · exact interior_maximal (image_mono interior_subset)
      (ho _ isOpen_interior (interior_subset.trans hKG))

lemma sphere_frontier_image_of_open_embedding {f:Sphere→Sphere} {G K:Set Sphere}
    (hc:ContinuousOn f G) (ho:∀S,IsOpen S→S⊆G→IsOpen (f '' S))
    (hG:IsOpen G) (hi:InjOn f G) (hK:IsCompact K) (hKG:K⊆G) :
    f '' frontier K=frontier (f '' K) := by
  have hfc : IsClosed (f '' K) := (hK.image_of_continuousOn (hc.mono hKG)).isClosed
  rw [frontier,hK.isClosed.closure_eq,frontier,hfc.closure_eq,
    sphere_interior_image_of_open_embedding hc ho hG hi hKG]
  exact (hi.mono hKG).image_sdiff_subset interior_subset

lemma frontier_closedTerminalCap (H:ℂ≃ₜℂ) :
    frontier (closedTerminalCap H)=((↑):ℂ→Sphere) '' frontier (jordanInterior H) := by
  rw [frontier,(isCompact_closedTerminalCap H).isClosed.closure_eq,
    interior_closedTerminalCap,(jordanInterior_isOpen H).frontier_eq,
    image_sdiff OnePoint.coe_injective]
  rfl

lemma frontier_image_of_closed_extension {f:Sphere→Sphere} {U V:Set Sphere}
    (hU:IsOpen U) (hV:IsOpen V) (hi:InjOn f (closure U))
    (he:f '' closure U=closure V) (hu:f '' U=V) :
    f '' frontier U=frontier V := by
  rw [hU.frontier_eq,hV.frontier_eq,hi.image_sdiff_subset subset_closure,he,hu]

end CircleDomainRigidity

end

end OAI
