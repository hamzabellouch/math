import OAI.Analysis.CircleDomains.Topology.ComponentControl
import OAI.Analysis.CircleDomains.Modulus.BarrierCollapse

namespace OAI

/-!
# From analytic barriers to circle-domain component control

The complementary components are the components of the sphere's closed
complement. Components admitting vanishing absolutely continuous barriers
are points. If all remaining components are round disks, the domain is
a circle domain.
-/

open Set Topology
open scoped OnePoint

namespace CircleDomainRigidity

/-- The finite-coordinate part of a sphere set. -/
def planarPart (K : Set Sphere) : Set ℂ := (fun z : ℂ => (z : Sphere)) ⁻¹' K

private theorem image_planarPart {K : Set Sphere} (hinfty : ∞ ∉ K) :
    (fun z : ℂ => (z : Sphere)) '' planarPart K = K := by
  apply image_preimage_eq_of_subset
  intro p hp
  exact OnePoint.ne_infty_iff_exists.mp (fun h => hinfty (h ▸ hp))

/-- A compact connected sphere set missing infinity is a compact connected
plane set in the standard chart. -/
theorem planarPart_isCompact_isConnected {K : Set Sphere}
    (hcompact : IsCompact K) (hconn : IsConnected K) (hinfty : ∞ ∉ K) :
    IsCompact (planarPart K) ∧ IsConnected (planarPart K) := by
  have heq := image_planarPart hinfty
  have hcomp : IsCompact (planarPart K) :=
    OnePoint.isOpenEmbedding_coe.isEmbedding.isCompact_iff.mpr (heq.symm ▸ hcompact)
  have hpre : IsPreconnected (planarPart K) :=
    OnePoint.isOpenEmbedding_coe.isEmbedding.isInducing.isPreconnected_image.mp
      (heq.symm ▸ hconn.isPreconnected)
  have hne : (planarPart K).Nonempty := by
    obtain ⟨p, hp⟩ := hconn.nonempty
    obtain ⟨z, rfl⟩ := OnePoint.ne_infty_iff_exists.mp (fun h => hinfty (h ▸ hp))
    exact ⟨z, hp⟩
  exact ⟨hcomp, hne, hpre⟩

/-- A genuine complementary component is compact and connected. -/
theorem IsComplementaryComponent.isCompact_isConnected {G K : Set Sphere}
    (hK : IsComplementaryComponent G K) (hG : IsOpen G) :
    IsCompact K ∧ IsConnected K := by
  obtain ⟨p, hp, rfl⟩ := hK
  have hclosed : IsClosed (connectedComponentIn Gᶜ p) := by
    rw [connectedComponentIn_eq_image hp]
    exact hG.isClosed_compl.isClosedMap_subtype_val _ isClosed_connectedComponent
  exact ⟨hclosed.isCompact, isConnected_connectedComponentIn_iff.mpr hp⟩

/-- Vanishing projection barriers force an actual complementary component
to be a singleton, including components with no interior. -/
theorem IsComplementaryComponent.eq_singleton_of_barriers
    {G K : Set Sphere} (hK : IsComplementaryComponent G K)
    (hG : IsOpen G) (hinfty : ∞ ∈ G)
    (hre : HasVanishingRectangleBarriers
      (sInf (Complex.re '' planarPart K)) (sSup (Complex.re '' planarPart K)))
    (him : HasVanishingRectangleBarriers
      (sInf (Complex.im '' planarPart K)) (sSup (Complex.im '' planarPart K))) :
    ∃ p : Sphere, K = {p} := by
  have hKsub : K ⊆ Gᶜ := by
    obtain ⟨p, _, rfl⟩ := hK
    exact connectedComponentIn_subset _ _
  have hinftyK : ∞ ∉ K := fun h => hKsub h hinfty
  obtain ⟨hcompact, hconn⟩ := hK.isCompact_isConnected hG
  obtain ⟨hcompactP, hconnP⟩ := planarPart_isCompact_isConnected hcompact hconn hinftyK
  have hss := subsingleton_of_vanishing_projection_barriers hcompactP hconnP hre him
  obtain ⟨z, hz⟩ := hconnP.nonempty
  have hsingleton : planarPart K = {z} := hss.eq_singleton_of_mem hz
  refine ⟨(z : Sphere), ?_⟩
  rw [← image_planarPart hinftyK, hsingleton]
  simp

/-- The final component-recognition implication with explicit analytic
barrier data. This remains a reduction: barrier existence and round
filling have not been assumed to be published results. -/
theorem isCircleDomain_of_component_barriers
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G) (hinfty : ∞ ∈ G)
    (hcontrol : ∀ K, IsComplementaryComponent G K →
      IsRoundClosedDisk K ∨
        (HasVanishingRectangleBarriers
          (sInf (Complex.re '' planarPart K)) (sSup (Complex.re '' planarPart K)) ∧
         HasVanishingRectangleBarriers
          (sInf (Complex.im '' planarPart K)) (sSup (Complex.im '' planarPart K)))) :
    IsCircleDomain G := by
  refine ⟨hG, hconn, ?_⟩
  intro p hp
  have hK : IsComplementaryComponent G (connectedComponentIn Gᶜ p) := ⟨p, hp, rfl⟩
  rcases hcontrol _ hK with hdisk | ⟨hre, him⟩
  · exact Or.inr hdisk
  · exact Or.inl (hK.eq_singleton_of_barriers hG hinfty hre him)

end CircleDomainRigidity

end OAI
