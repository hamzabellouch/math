import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPermittedRouteSeparation

namespace OAI

/-! An interior point of a permitted path cannot be an endpoint of any other
permitted path, including catalog paths not present in the Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

theorem permitted_avoids_source
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    (R S : QMACellRoute) (hR : P.RoutingAllowed R.body) (hS : P.RoutingAllowed S.body)
    (hvR : R.Valid) (hvS : S.Valid) : S.source ∉ (R.path.drop 1).dropLast := by
  intro hz
  have hne : R.endpointPair ≠ S.endpointPair := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨ha,_⟩ | ⟨_,ha⟩
    · exact qmaListInterior_ne_head (R.simple hvR) R.endpoints.1 hz ha.symm
    · exact qmaListInterior_ne_last (R.simple hvR) R.endpoints.2 hz ha.symm
  have hSpath : S.source ∈ S.path := by
    obtain ⟨t,ht⟩ := List.head?_eq_some_iff.mp S.endpoints.1
    rw [ht]
    exact List.mem_cons_self
  exact Finset.disjoint_left.mp (P.permitted_routes_disjoint havoid R S hR hS hvR hvS hne)
    (List.mem_toFinset.mpr hz) (List.mem_toFinset.mpr hSpath)

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
