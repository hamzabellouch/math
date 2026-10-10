import OAI.Analysis.CircleDomains.Topology.RoundPhaseBoundary
import OAI.Analysis.CircleDomains.Topology.IsolatedDiskComponent

namespace OAI

/-! The selected limiting circle bounds an actual whole complementary
component, rather than merely an omitted subdisk. -/
open Set Function Filter Metric Complex
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace FiniteJordanConfiguration
variable {m:ℕ} {C:FiniteJordanConfiguration (Fin (m+1))} {i:Fin (m+1)}
variable {P:PhaseCollar C i} (L:RegularPhaseLimit P)

lemma RegularPhaseLimit.collar_image_open :
    IsOpen (L.boundaryMap '' symmetricCircleAnnulus P.radius) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro _ ⟨z,hz,rfl⟩
  rw [←holomorphicInjOn_map_nhds (isOpen_symmetricCircleAnnulus P.radius)
    L.holomorphic L.injective hz]
  exact image_mem_map ((isOpen_symmetricCircleAnnulus P.radius).mem_nhds hz)

lemma RegularPhaseLimit.exterior_collar_in_domain :
    (L.boundaryMap '' symmetricCircleAnnulus P.radius)\closedBall L.center L.radius ⊆
      L.map '' C.planeRegion := by
  rintro _ ⟨⟨z,hz,rfl⟩,hn⟩
  have ho : 1<‖z‖ := by
    by_contra hh
    have hle : ‖z‖≤1 := le_of_not_gt hh
    rcases lt_or_eq_of_le hle with hlt|he
    · exact hn (mem_closedBall_iff_norm.mpr (L.inner_strict hz hlt).le)
    · exact hn (mem_closedBall_iff_norm.mpr (L.circle z hz he).le)
  exact ⟨P.coordinate z,P.exterior_source z hz ho,(L.agrees z hz ho).symm⟩

lemma RegularPhaseLimit.disk_component {x:ℂ} (hx:x∈closedBall L.center L.radius) :
    connectedComponentIn (L.map '' C.planeRegion)ᶜ x=closedBall L.center L.radius := by
  apply closedBall_complementary_component L.collar_image_open ?_ L.omitted_disk
    L.exterior_collar_in_domain hx
  rw [←L.circle_image]
  exact image_mono (unit_circle_subset_symmetricCircleAnnulus P.radius_gt)

end FiniteJordanConfiguration
end CircleDomainRigidity

end

end OAI
