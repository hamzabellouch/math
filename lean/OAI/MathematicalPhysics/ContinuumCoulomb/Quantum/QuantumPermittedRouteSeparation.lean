import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCorridorSeparation
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumMergedEndpointPairs

namespace OAI

/-! The complete permitted catalog is planar: different unordered physical
endpoint pairs have disjoint path interiors. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaCellBody_cases (R : QMACellRouteBody) :
    (∃ p e, R = qmaInternalBody p e) ∨ ∃ p a b c, R = .corridor p a b c := by
  cases R with
  | ray p a => exact Or.inl ⟨p,.inl a,rfl⟩
  | pair p e => exact Or.inl ⟨p,.inr (.inl e),rfl⟩
  | patch p e => exact Or.inl ⟨p,.inr (.inr e),rfl⟩
  | corridor p a b c => exact Or.inr ⟨p,a,b,c,rfl⟩

namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

theorem permitted_bodies_disjoint
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    (R S : QMACellRouteBody) (hR : P.RoutingAllowed R) (hS : P.RoutingAllowed S)
    (hvR : R.Valid) (hvS : S.Valid)
    (hne : s(R.source,R.target) ≠ s(S.source,S.target)) :
    Disjoint ((R.path.drop 1).dropLast).toFinset S.path.toFinset := by
  rcases qmaCellBody_cases R with ⟨p,e,rfl⟩ | ⟨p,a,b,c,rfl⟩
  · rcases qmaCellBody_cases S with ⟨q,f,rfl⟩ | ⟨q,d,f,g,rfl⟩
    · have hneq : p ≠ q ∨ e ≠ f := by
        by_cases hp : p = q
        · right
          intro he
          apply hne
          rw [hp,he]
        · exact Or.inl hp
      exact P.internal_bodies_disjoint havoid p q e f hneq hR hS
    · exact P.internal_corridor_disjoint p q e d f g hR hS
  · rcases qmaCellBody_cases S with ⟨q,e,rfl⟩ | ⟨q,d,f,g,rfl⟩
    · exact P.corridor_internal_disjoint p q a b c e hvR hR hS
    · have hd := P.corridors_disjoint p q a d b c f g hvR hvS hR hS hne
      apply Finset.disjoint_left.mpr
      intro z hz hw
      apply Finset.disjoint_left.mp hd _ hw
      exact List.mem_toFinset.mpr
        (List.mem_of_mem_drop (List.mem_of_mem_dropLast (List.mem_toFinset.mp hz)))

theorem permitted_routes_disjoint
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    (R S : QMACellRoute) (hR : P.RoutingAllowed R.body) (hS : P.RoutingAllowed S.body)
    (hvR : R.Valid) (hvS : S.Valid) (hne : R.endpointPair ≠ S.endpointPair) :
    Disjoint ((R.path.drop 1).dropLast).toFinset S.path.toFinset := by
  rw [qmaRoute_interior_finset,qmaRoute_path_finset]
  apply P.permitted_bodies_disjoint havoid R.body S.body hR hS hvR hvS
  simpa only [QMACellRoute.endpointPair_body] using hne

theorem mergedOutputRoute_disjoint (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    (e f : (P.crossingOutput N hD).merge.Edge) (hef : e ≠ f) :
    Disjoint (((P.mergedOutputRoute N hD havoid e).path.drop 1).dropLast).toFinset
      (P.mergedOutputRoute N hD havoid f).path.toFinset := by
  have he := P.mergedOutputRoute_spec N hD havoid e
  have hf := P.mergedOutputRoute_spec N hD havoid f
  exact P.permitted_routes_disjoint havoid _ _ he.1 hf.1 he.2.1 hf.2.1
    ((P.mergedOutputRoute_pairs_injective N hD havoid).ne hef)

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
