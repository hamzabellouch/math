import OAI.Analysis.CircleDomains.Topology.RoundPhaseComponent
import OAI.Analysis.CircleDomains.Topology.EmbeddingComponent

namespace OAI

/-! The selected round component in the actual normalized sphere image. -/
open Set Function Filter Metric Complex
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace FiniteJordanConfiguration
variable {m:ℕ} {C:FiniteJordanConfiguration (Fin (m+1))} {i:Fin (m+1)}
variable {P:PhaseCollar C i} (L:RegularPhaseLimit P)

lemma RegularPhaseLimit.sphere_complement :
    (extendAtInfinity L.map '' C.region)ᶜ=((↑):ℂ→Sphere) '' (L.map '' C.planeRegion)ᶜ := by
  rw [C.region_eq_plane_with_infty,image_union,image_singleton]
  simp only [extendAtInfinity_infty]
  have he : extendAtInfinity L.map '' (((↑):ℂ→Sphere) '' C.planeRegion)=
      ((↑):ℂ→Sphere) '' (L.map '' C.planeRegion) := by
    rw [image_image,image_image]
    rfl
  rw [he]
  ext p
  cases p using OnePoint.rec <;> simp only [mem_compl_iff,mem_union,mem_image,
    OnePoint.coe_ne_infty,not_false_eq_true,mem_singleton_iff,not_true_eq_false,
    exists_false,and_false,or_true,not_or,and_true,OnePoint.coe_injective.eq_iff]
  simp

lemma RegularPhaseLimit.sphere_disk_component {x:ℂ} (hx:x∈closedBall L.center L.radius) :
    connectedComponentIn (extendAtInfinity L.map '' C.region)ᶜ (x:Sphere)=
      ((↑):ℂ→Sphere) '' closedBall L.center L.radius := by
  rw [L.sphere_complement,←embedding_image_connectedComponentIn
    OnePoint.isOpenEmbedding_coe.isEmbedding (L.omitted_disk hx),L.disk_component hx]

end FiniteJordanConfiguration
end CircleDomainRigidity

end

end OAI
