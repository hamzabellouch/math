import OAI.Analysis.CircleDomains.Topology.QuotientTopology
import OAI.Analysis.CircleDomains.Modulus.ConformalNormalization

namespace OAI

/-! Normalize the component quotient at the source point at infinity.
The dust then has no point at infinity, so every marked endpoint admits
the physical collars used in the local-exclusion construction. -/
open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem normalized_component_quotient_of_moore
    (hmoore : MooreSphereDecomposition) {G : Set Sphere}
    (hG : IsOpen G) (hconn : IsConnected G) (hinf : OnePoint.infty ∈ G) :
    ∃ π : Sphere → Sphere, Continuous π ∧ IsClosedMap π ∧ Surjective π ∧
      (∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x)) ∧
      π OnePoint.infty = OnePoint.infty ∧
      OnePoint.infty ∈ π '' G ∧ IsOpen (π '' G) ∧
      (∃ e : G ≃ₜ (π '' G), ∀ x, (e x).val = π x.val) ∧
      IsTotallyDisconnected (π '' G)ᶜ := by
  obtain ⟨q, hq, hqclosed, hqsurj, hqr, _⟩ := componentSphereQuotient_of_moore hmoore hG hconn
  let N := pointToInfinity (q OnePoint.infty)
  let π := N ∘ q
  have hπ : Continuous π := N.continuous.comp hq
  have hclosed : IsClosedMap π := N.isClosedMap.comp hqclosed
  have hsurj : Surjective π := N.surjective.comp hqsurj
  have hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x) := by
    intro x y
    change N (q x) = N (q y) ↔ _
    rw [N.injective.eq_iff, hqr]
  have hfix : π OnePoint.infty = OnePoint.infty := pointToInfinity_apply_self _
  obtain ⟨hopen, he⟩ := homeomorph_of_component_collapse G hG π hπ hclosed hsurj hr
  exact ⟨π, hπ, hclosed, hsurj, hr, hfix, ⟨_, hinf, hfix⟩, hopen, he,
    totallyDisconnected_of_component_collapse G hG π hπ hclosed hsurj hr⟩

end CircleDomainRigidity

end

end OAI
