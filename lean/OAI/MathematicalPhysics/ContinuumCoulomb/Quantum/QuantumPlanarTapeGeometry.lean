import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPlanarTapeSupport
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPlanarSelectorTransport
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumEvenTapeGeometry

namespace OAI

/-! The emitted planar tape is the exact coordinate and path array of a
bounded planar family, in its literal merged-edge order. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

namespace QuantumRouteSelectorProgram

theorem value_eq_of_allowed (t u : QuantumRoutingTable.Table)
    (h : ∀ B, QuantumRoutingTable.allowed t B = QuantumRoutingTable.allowed u B)
    (ends : Ends) : value (t,ends) = value (u,ends) := by
  have ht : QuantumTaggedRouteProgram.tagged t = QuantumTaggedRouteProgram.tagged u := by
    funext R
    simp only [QuantumTaggedRouteProgram.tagged,QuantumTaggedRouteProgram.bodyPermitted,h]
  simp only [value,candidates,ht]

end QuantumRouteSelectorProgram

namespace QuantumPlanarTapeGeometry
open QuantumPlanarTapeProgram QuantumRouteCode

private theorem map_eq_ofFn {α β : Type*} (xs : List α) (f : α → β) :
    xs.map f = List.ofFn (fun i => f (xs.get i)) := by
  have h := congrArg (List.map f) (List.ofFn_get xs)
  rw [List.map_ofFn] at h
  exact h.symm

theorem graph_packed (x : Input) (hn : ∀ e ∈ x.1.1.2.1, e.1 ≠ e.2.1) :
    QuantumListGraph.packed (graph x hn) (Equiv.refl _) = merged x := by
  change List.ofFn (fun i : Fin (merged x).length => (merged x).get i) = merged x
  exact List.ofFn_get _

section Geometry
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)
    (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D) (x : Input)
    (hb : SourceBondLists.bounded x.1.1.1 x.1.1.2.1)
    (hn : ∀ e ∈ x.1.1.2.1, e.1 ≠ e.2.1)
    (vertex : Fin x.1.1.1 ≃ Fin (P.crossingOutput N hD).n)
    (forward : ∀ e : (rawGraph x hb hn).Edge, ∃ f : (P.crossingOutput N hD).Edge,
      s(vertex ((rawGraph x hb hn).left e),vertex ((rawGraph x hb hn).right e)) =
        s((P.crossingOutput N hD).left f,(P.crossingOutput N hD).right f))
    (backward : ∀ f : (P.crossingOutput N hD).Edge, ∃ e : (rawGraph x hb hn).Edge,
      s(vertex ((rawGraph x hb hn).left e),vertex ((rawGraph x hb hn).right e)) =
        s((P.crossingOutput N hD).left f,(P.crossingOutput N hD).right f))
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    (hpositive : ∀ v, 0 < (P.position v).1 ∧ 0 < (P.position v).2)

def route : QMAPlanarRouteData (graph x hn) :=
  P.selectorPlanarRoute (H := graph x hn) N hD havoid vertex (edge P N hD x hb hn vertex forward backward)
    (edge_endpoints P N hD x hb hn vertex forward backward) hpositive

theorem route_length (e : (graph x hn).Edge) :
    (route P N hD x hb hn vertex forward backward havoid hpositive).length e ≤ 20 :=
  P.selectorPlanarRoute_length (H := graph x hn) N hD havoid vertex (edge P N hD x hb hn vertex forward backward)
    (edge_endpoints P N hD x hb hn vertex forward backward) hpositive e

theorem route_bounded {X Y : ℕ}
    (hsource : ∀ v, (P.position v).1 < X ∧ (P.position v).2 < Y)
    (hpath : ∀ e k, k ≤ P.length e → (P.point e k).1 < X ∧ (P.point e k).2 < Y) :
    (route P N hD x hb hn vertex forward backward havoid hpositive).Bounded (32*X) (32*Y) :=
  P.selectorPlanarRoute_bounded (H := graph x hn) N hD havoid vertex (edge P N hD x hb hn vertex forward backward)
    (edge_endpoints P N hD x hb hn vertex forward backward) hpositive hsource hpath

variable
    (hpositions : x.1.2 = List.ofFn (fun v => P.crossingPosition N D (vertex v)))
    (hallowed : ∀ B, QuantumRoutingTable.allowed x.2 B =
      QuantumRoutingTable.allowed P.routingTable B)

include hpositions in
theorem lookup_position (v : Fin x.1.1.1) :
    QuantumForkGridProgram.lookup x.1.2 v.val = P.crossingPosition N D (vertex v) := by
  rw [hpositions]
  unfold QuantumForkGridProgram.lookup
  rw [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_ofFn]
  simp only [dite_eq_left v.isLt,Option.getD_some]

include hpositions hallowed in
theorem selected_path (e : (graph x hn).Edge) :
    QuantumRouteSelectorProgram.value (routeInput x ((merged x).get e)) =
      QuantumRouteSelectorProgram.value (P.routingTable,
        P.crossingPosition N D (vertex ((graph x hn).left e)),
        P.crossingPosition N D (vertex ((graph x hn).right e))) := by
  let a : Fin x.1.1.1 := (graph x hn).left e
  let b : Fin x.1.1.1 := (graph x hn).right e
  change QuantumRouteSelectorProgram.value (x.2,
    QuantumForkGridProgram.lookup x.1.2 a.val,
    QuantumForkGridProgram.lookup x.1.2 b.val) =
      QuantumRouteSelectorProgram.value (P.routingTable,
        P.crossingPosition N D (vertex a),P.crossingPosition N D (vertex b))
  rw [lookup_position P N hD x vertex hpositions a,lookup_position P N hD x vertex hpositions b]
  exact QuantumRouteSelectorProgram.value_eq_of_allowed x.2 P.routingTable hallowed _

include hpositions hallowed in
theorem path_eq (e : (graph x hn).Edge) :
    QuantumRouteSelectorProgram.value (routeInput x ((merged x).get e)) =
      (List.range ((route P N hD x hb hn vertex forward backward havoid hpositive).length e+1)).map
        ((route P N hD x hb hn vertex forward backward havoid hpositive).point e) := by
  exact (selected_path P N hD x hn vertex hpositions hallowed e).trans
    (P.selectorPlanarRoute_path (H := graph x hn) N hD havoid vertex (edge P N hD x hb hn vertex forward backward)
      (edge_endpoints P N hD x hb hn vertex forward backward) hpositive e).symm

include hpositions in
theorem positions_eq : (value x).2.1 =
    List.ofFn (route P N hD x hb hn vertex forward backward havoid hpositive).position :=
  hpositions

include hpositions hallowed in
theorem paths_eq : (value x).2.2 =
    List.ofFn (fun e =>
      (List.range ((route P N hD x hb hn vertex forward backward havoid hpositive).length e+1)).map
        ((route P N hD x hb hn vertex forward backward havoid hpositive).point e)) := by
  change (merged x).map (fun e => QuantumRouteSelectorProgram.value (routeInput x e)) = _
  rw [map_eq_ofFn]
  apply congrArg List.ofFn
  funext e
  exact path_eq P N hD x hb hn vertex forward backward havoid hpositive hpositions hallowed e

include hpositions hallowed in
theorem value_eq : value x =
    (((graph x hn).n,QuantumListGraph.packed (graph x hn) (Equiv.refl _),(graph x hn).constant),
      List.ofFn (route P N hD x hb hn vertex forward backward havoid hpositive).position,
      List.ofFn (fun e =>
        (List.range ((route P N hD x hb hn vertex forward backward havoid hpositive).length e+1)).map
          ((route P N hD x hb hn vertex forward backward havoid hpositive).point e))) := by
  apply Prod.ext
  · rw [graph_packed]
    rfl
  · exact Prod.ext
      (positions_eq P N hD x hb hn vertex forward backward havoid hpositive hpositions)
      (paths_eq P N hD x hb hn vertex forward backward havoid hpositive hpositions hallowed)

include hpositions hallowed in
theorem even_input_eq (M : ℚ) :
    (M,value x) = QuantumEvenTapeGeometry.input
      (route P N hD x hb hn vertex forward backward havoid hpositive) (Equiv.refl _) M := by
  exact congrArg (fun t : Output => (M,t))
    (value_eq P N hD x hb hn vertex forward backward havoid hpositive hpositions hallowed)

end Geometry
end QuantumPlanarTapeGeometry
end ContinuumCoulomb

end

end OAI
