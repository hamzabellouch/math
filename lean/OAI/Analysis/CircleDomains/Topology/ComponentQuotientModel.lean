import OAI.Analysis.CircleDomains.Topology.QuotientTopology
import OAI.Analysis.CircleDomains.Topology.ClosedRelationQuotient
import OAI.Analysis.CircleDomains.Topology.ClosedMapSecondCountable
import Mathlib.Topology.Metrizable.Urysohn

namespace OAI

/-! The topological quotient by complementary components has a compatible
metric, an open domain chart, and a totally disconnected remainder.
Moore's decomposition theorem realizes this quotient as a sphere. -/
open Set Topology TopologicalSpace
noncomputable section
namespace CircleDomainRigidity

abbrev ComponentQuotient (G : Set Sphere) := Quotient (componentSetoid G)

def componentProjection (G : Set Sphere) : Sphere → ComponentQuotient G := @Quotient.mk' Sphere (componentSetoid G)

lemma componentProjection_continuous (G : Set Sphere) : Continuous (componentProjection G) :=
  continuous_quotient_mk' (s := componentSetoid G)

lemma componentProjection_surjective (G : Set Sphere) : Function.Surjective (componentProjection G) :=
  @Quotient.mk'_surjective Sphere (componentSetoid G)

lemma componentProjection_eq (G : Set Sphere) (x y : Sphere) :
    componentProjection G x = componentProjection G y ↔
      x=y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x) := Quotient.eq'

lemma componentProjection_closed {G : Set Sphere} (hG : IsOpen G) :
    IsClosedMap (componentProjection G) :=
  quotientMk_isClosedMap_of_closed_relation (componentSetoid G)
    (isClosed_componentCollapseRelation hG.isClosed_compl)

lemma componentQuotient_t2 {G : Set Sphere} (hG : IsOpen G) : T2Space (ComponentQuotient G) :=
  quotient_t2Space_of_closed_relation (componentSetoid G)
    (isClosed_componentCollapseRelation hG.isClosed_compl)

lemma componentQuotient_secondCountable {G : Set Sphere} (hG : IsOpen G) :
    SecondCountableTopology (ComponentQuotient G) := by
  let S := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
  let e : Sphere ≃ₜ S := onePointEquivSphereOfFinrankEq (V := ℂ) (ι := Fin 3) (by simp)
  let : SecondCountableTopology Sphere := e.isEmbedding.secondCountableTopology
  apply secondCountable_of_closed_surjection_compact_fibers (componentProjection G)
    (componentProjection_continuous G) (componentProjection_closed hG) (componentProjection_surjective G)
  intro y
  exact (quotientMk_fiber_isClosed_of_closed_relation (componentSetoid G)
    (isClosed_componentCollapseRelation hG.isClosed_compl) y).isCompact

lemma componentQuotient_metrizable {G : Set Sphere} (hG : IsOpen G) :
    MetrizableSpace (ComponentQuotient G) := by
  let := componentQuotient_t2 hG
  let := componentQuotient_secondCountable hG
  infer_instance

lemma componentQuotient_locallyConnected (G : Set Sphere) :
    LocallyConnectedSpace (ComponentQuotient G) := by
  let S := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
  let : LocallyConnectedSpace S :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 2)) S
  let e : Sphere ≃ₜ S := onePointEquivSphereOfFinrankEq (V := ℂ) (ι := Fin 3) (by simp)
  let : LocallyConnectedSpace Sphere := e.locallyConnectedSpace
  exact isQuotientMap_quotient_mk'.isCoinducing.locallyConnectedSpace

lemma componentQuotient_domain_model {G : Set Sphere} (hG : IsOpen G) :
    IsOpen (componentProjection G '' G) ∧
    (∃ e : G ≃ₜ (componentProjection G '' G),
      ∀ x, (e x).val=componentProjection G x.val) ∧
    IsTotallyDisconnected (componentProjection G '' G)ᶜ := by
  obtain ⟨ho,he⟩ := homeomorph_of_component_collapse G hG (componentProjection G)
    (componentProjection_continuous G) (componentProjection_closed hG)
    (componentProjection_surjective G) (componentProjection_eq G)
  exact ⟨ho, he, totallyDisconnected_of_component_collapse G hG (componentProjection G)
    (componentProjection_continuous G) (componentProjection_closed hG)
    (componentProjection_surjective G) (componentProjection_eq G)⟩

lemma componentQuotient_connected_fibers (G : Set Sphere) :
    ∀ y, IsConnected (componentProjection G ⁻¹' {y}) :=
  connected_fibers_of_component_collapse G (componentProjection G)
    (componentProjection_surjective G) (componentProjection_eq G)

end CircleDomainRigidity

end

end OAI
