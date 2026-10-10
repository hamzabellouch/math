import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSelectedRoute
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingPlanarRoutes

namespace OAI

/-! The actual finite selector gives a planar family after arbitrary vertex
and edge permutations, including independent edge orientation changes. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

namespace QMAPlanarListData

theorem range_toRoute_point {G : QMARationalExchangeGraph} (L : QMAPlanarListData G)
    (e : G.Edge) :
    (List.range (L.toRoute.length e+1)).map (L.toRoute.point e) = L.path e := by
  have hn : L.toRoute.length e+1 = (L.path e).length := by
    change (L.path e).length-1+1 = (L.path e).length
    have h := L.length e
    omega
  rw [hn]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range]
  · intro i hi hj
    rw [List.getElem_map,List.getElem_range]
    exact L.point_get e hj

end QMAPlanarListData

namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

theorem crossing_hasAllowedRoute (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    (x y : Fin (P.crossingOutput N hD).merge.n)
    (e : (P.crossingOutput N hD).merge.Edge)
    (he : s(x,y) = s((P.crossingOutput N hD).merge.left e,
      (P.crossingOutput N hD).merge.right e)) :
    P.HasAllowedRoute (P.crossingPosition N D x) (P.crossingPosition N D y) := by
  have h : P.HasAllowedRoute
      (P.crossingPosition N D ((P.crossingOutput N hD).merge.left e))
      (P.crossingPosition N D ((P.crossingOutput N hD).merge.right e)) :=
    P.mergedOutput_route_exists N hD havoid e
  rcases Sym2.eq_iff.mp he with ⟨hl,hr⟩ | ⟨hl,hr⟩
  · simpa only [hl,hr] using h
  · simpa only [hl,hr] using P.hasAllowedRoute_reverse h

section Transport
variable (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    {H : QMARationalExchangeGraph}
    (vertex : Fin H.n ≃ Fin (P.crossingOutput N hD).merge.n)
    (edge : H.Edge ≃ (P.crossingOutput N hD).merge.Edge)
    (ends : ∀ e, s(vertex (H.left e),vertex (H.right e)) =
      s((P.crossingOutput N hD).merge.left (edge e),
        (P.crossingOutput N hD).merge.right (edge e)))

def selectorTransportRoute (e : H.Edge) : QMACellRoute :=
  P.selectedAllowedRoute (P.crossingPosition N D (vertex (H.left e)))
    (P.crossingPosition N D (vertex (H.right e)))
    (P.crossing_hasAllowedRoute N hD havoid _ _ (edge e) (ends e))

theorem selectorTransportRoute_spec (e : H.Edge) :
    P.RoutingAllowed (P.selectorTransportRoute N hD havoid vertex edge ends e).body ∧
      (P.selectorTransportRoute N hD havoid vertex edge ends e).Valid ∧
      (P.selectorTransportRoute N hD havoid vertex edge ends e).source =
        P.crossingPosition N D (vertex (H.left e)) ∧
      (P.selectorTransportRoute N hD havoid vertex edge ends e).target =
        P.crossingPosition N D (vertex (H.right e)) :=
  P.selectedAllowedRoute_spec _ _ _

theorem selectorTransportRoute_path (e : H.Edge) :
    (P.selectorTransportRoute N hD havoid vertex edge ends e).path =
      QuantumRouteSelectorProgram.value (P.routingTable,
        P.crossingPosition N D (vertex (H.left e)),
        P.crossingPosition N D (vertex (H.right e))) :=
  (P.selectedAllowedRoute_path _ _ _).symm

theorem selectorTransportRoute_endpointPair (e : H.Edge) :
    (P.selectorTransportRoute N hD havoid vertex edge ends e).endpointPair =
      s(P.crossingPosition N D ((P.crossingOutput N hD).merge.left (edge e)),
        P.crossingPosition N D ((P.crossingOutput N hD).merge.right (edge e))) := by
  have hs := P.selectorTransportRoute_spec N hD havoid vertex edge ends e
  rw [QMACellRoute.endpointPair,hs.2.2.1,hs.2.2.2]
  rcases Sym2.eq_iff.mp (ends e) with ⟨hl,hr⟩ | ⟨hl,hr⟩
  · rw [hl,hr]
  · rw [hl,hr]
    exact Sym2.eq_swap

theorem selectorTransportRoute_pairs_injective :
    Function.Injective (fun e =>
      (P.selectorTransportRoute N hD havoid vertex edge ends e).endpointPair) := by
  intro e f hef
  apply edge.injective
  apply qmaMergedEndpointPairs_injective (P.crossingOutput N hD)
    (P.crossingPosition N D) (P.crossingPosition_injective N D)
  exact (P.selectorTransportRoute_endpointPair N hD havoid vertex edge ends e).symm.trans
    (hef.trans (P.selectorTransportRoute_endpointPair N hD havoid vertex edge ends f))

def selectorPlanarList
    (hpositive : ∀ v, 0 < (P.position v).1 ∧ 0 < (P.position v).2) :
    QMAPlanarListData H where
  position v := P.crossingPosition N D (vertex v)
  position_injective := (P.crossingPosition_injective N D).comp vertex.injective
  path e := (P.selectorTransportRoute N hD havoid vertex edge ends e).path
  length e := (P.selectorTransportRoute N hD havoid vertex edge ends e).length_bounds.1
  first e := (P.selectorTransportRoute N hD havoid vertex edge ends e).endpoints.1.trans
    (congrArg some (P.selectorTransportRoute_spec N hD havoid vertex edge ends e).2.2.1)
  last e := (P.selectorTransportRoute N hD havoid vertex edge ends e).endpoints.2.trans
    (congrArg some (P.selectorTransportRoute_spec N hD havoid vertex edge ends e).2.2.2)
  simple e := (P.selectorTransportRoute N hD havoid vertex edge ends e).simple
    (P.selectorTransportRoute_spec N hD havoid vertex edge ends e).2.1
  step e := (P.selectorTransportRoute N hD havoid vertex edge ends e).chain
    (P.selectorTransportRoute_spec N hD havoid vertex edge ends e).2.1
  positive e z hz := by
    have hs := P.selectorTransportRoute_spec N hD havoid vertex edge ends e
    apply (P.selectorTransportRoute N hD havoid vertex edge ends e).path_positive ?_ ?_ hz
    · rw [hs.2.2.1]
      exact P.crossingPosition_positive hpositive N D _
    · rw [hs.2.2.2]
      exact P.crossingPosition_positive hpositive N D _
  avoids e v := by
    obtain ⟨R,ha,hv,hs⟩ := P.physical_endpoint_cover N D havoid (vertex v)
    rw [← hs]
    have he := P.selectorTransportRoute_spec N hD havoid vertex edge ends e
    exact P.permitted_avoids_source havoid _ R he.1 ha he.2.1 hv
  disjoint e f hef := by
    have he := P.selectorTransportRoute_spec N hD havoid vertex edge ends e
    have hf := P.selectorTransportRoute_spec N hD havoid vertex edge ends f
    exact P.permitted_routes_disjoint havoid _ _ he.1 hf.1 he.2.1 hf.2.1
      ((P.selectorTransportRoute_pairs_injective N hD havoid vertex edge ends).ne hef)

theorem selectorPlanarList_path
    (hpositive : ∀ v, 0 < (P.position v).1 ∧ 0 < (P.position v).2) (e : H.Edge) :
    (P.selectorPlanarList N hD havoid vertex edge ends hpositive).path e =
      QuantumRouteSelectorProgram.value (P.routingTable,
        P.crossingPosition N D (vertex (H.left e)),
        P.crossingPosition N D (vertex (H.right e))) :=
  P.selectorTransportRoute_path N hD havoid vertex edge ends e

def selectorPlanarRoute
    (hpositive : ∀ v, 0 < (P.position v).1 ∧ 0 < (P.position v).2) :
    QMAPlanarRouteData H :=
  (P.selectorPlanarList N hD havoid vertex edge ends hpositive).toRoute

theorem selectorPlanarRoute_path
    (hpositive : ∀ v, 0 < (P.position v).1 ∧ 0 < (P.position v).2) (e : H.Edge) :
    (List.range ((P.selectorPlanarRoute N hD havoid vertex edge ends hpositive).length e+1)).map
      ((P.selectorPlanarRoute N hD havoid vertex edge ends hpositive).point e) =
      QuantumRouteSelectorProgram.value (P.routingTable,
        P.crossingPosition N D (vertex (H.left e)),
        P.crossingPosition N D (vertex (H.right e))) :=
  ((P.selectorPlanarList N hD havoid vertex edge ends hpositive).range_toRoute_point e).trans
    (P.selectorPlanarList_path N hD havoid vertex edge ends hpositive e)

theorem selectorPlanarRoute_length
    (hpositive : ∀ v, 0 < (P.position v).1 ∧ 0 < (P.position v).2) (e : H.Edge) :
    (P.selectorPlanarRoute N hD havoid vertex edge ends hpositive).length e ≤ 20 := by
  change (P.selectorTransportRoute N hD havoid vertex edge ends e).path.length-1 ≤ 20
  have h := (P.selectorTransportRoute N hD havoid vertex edge ends e).length_bounds.2
  omega

theorem selectorTransportRoute_path_bounded {X Y : ℕ}
    (hsource : ∀ v, (P.position v).1 < X ∧ (P.position v).2 < Y)
    (hpath : ∀ e k, k ≤ P.length e → (P.point e k).1 < X ∧ (P.point e k).2 < Y)
    (e : H.Edge) {z : ℕ × ℕ}
    (hz : z ∈ (P.selectorTransportRoute N hD havoid vertex edge ends e).path) :
    z.1 < 32*X ∧ z.2 < 32*Y := by
  have hs := P.selectorTransportRoute_spec N hD havoid vertex edge ends e
  apply (P.selectorTransportRoute N hD havoid vertex edge ends e).path_bounded ?_ ?_ hz
  · rw [hs.2.2.1]
    exact P.crossingPosition_bounded hsource hpath N D _
  · rw [hs.2.2.2]
    exact P.crossingPosition_bounded hsource hpath N D _

theorem selectorPlanarRoute_bounded {X Y : ℕ}
    (hpositive : ∀ v, 0 < (P.position v).1 ∧ 0 < (P.position v).2)
    (hsource : ∀ v, (P.position v).1 < X ∧ (P.position v).2 < Y)
    (hpath : ∀ e k, k ≤ P.length e → (P.point e k).1 < X ∧ (P.point e k).2 < Y) :
    (P.selectorPlanarRoute N hD havoid vertex edge ends hpositive).Bounded (32*X) (32*Y) := by
  refine ⟨fun v => P.crossingPosition_bounded hsource hpath N D (vertex v),?_⟩
  intro e k hk
  let L := P.selectorPlanarList N hD havoid vertex edge ends hpositive
  change (L.point e k).1 < 32*X ∧ (L.point e k).2 < 32*Y
  apply P.selectorTransportRoute_path_bounded N hD havoid vertex edge ends hsource hpath e
  exact L.point_mem e (by
    have hlen := L.length e
    change k ≤ (L.path e).length-1 at hk
    omega)

end Transport
end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
