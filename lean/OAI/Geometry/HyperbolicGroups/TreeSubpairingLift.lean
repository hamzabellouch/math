import Mathlib
import OAI.Geometry.HyperbolicGroups.PlanarSubpairing
import OAI.Geometry.HyperbolicGroups.PairingForest
import OAI.Geometry.HyperbolicGroups.SubpairingGraph
import OAI.Geometry.HyperbolicGroups.SubpairingTree
import OAI.Geometry.HyperbolicGroups.GraphSubpairing

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.PictureMap
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D] [Nonempty D]
variable (M : PictureMap D)

/-- Every spanning tree of the actual underlying graph lifts to a genuine
one-boundary dart subpairing. Kruskal is applied ONLY to actual copies of
its own edges; connectedness then forces equality with the selected tree.
This permits a shortest-path tree, rather than an arbitrary-radius tree. -/
theorem lift_spanning_tree (T : SimpleGraph M.GraphVertex)
    (hle : T ≤ M.underlyingGraph) (hT : T.IsTree) :
    ∃ q : Perm D, ∃ hq : ∀ x, q x = x ∨ q x = M.edge x,
      SameCycle.setoid M.vertex ⊔ SameCycle.setoid q = ⊤ ∧
      cycles (M.vertex*q) = 1 ∧
      M.subpairingGraph q (M.subpairing_sq q hq) = T := by
  let p := M.graphPairing T
  have hp := M.graphPairing_sub T
  have hpg := M.graphPairing_graph T hle
  have hspan := M.subpairing_span_of_connected p (M.subpairing_sq p hp)
    (hpg ▸ hT.connected)
  obtain ⟨l,hl,hn,hpairs⟩ := involution_pairs p (M.subpairing_sq p hp)
  let t := forestEdges (SameCycle.setoid M.vertex) l
  let q := swaps t
  have hmem : ∀ ab ∈ l, M.edge ab.1 = ab.2 := by
    intro ab hab
    rcases hp ab.1 with he | he
    · exact ((hpairs ab hab).1 (he.symm.trans (hpairs ab hab).2)).elim
    · exact he.symm.trans (hpairs ab hab).2
  have hq := M.swaps_subpairing t (fun ab hab => hmem ab ((forestEdges_sublist _ l).subset hab))
  have hjoin : joins (SameCycle.setoid M.vertex) l = ⊤ :=
    (joins_pairing M.vertex p l hl (fun ab hab => (hpairs ab hab).2)).trans hspan
  have hb : cycles (M.vertex*q) = 1 := by
    have hc := forestEdges_cycles M.vertex (SameCycle.setoid M.vertex) le_rfl l
    have hd := forestEdges_card (SameCycle.setoid M.vertex) l
    rw [hjoin,card_quotient_top_one,← cycles_eq_card_classes] at hd
    change cycles (M.vertex*q) = _ at hc
    omega
  have hqs : SameCycle.setoid M.vertex ⊔ SameCycle.setoid q = ⊤ := by
    have hs : SameCycle.setoid (M.vertex*q) = ⊤ := by
      apply setoid_eq_of_card_eq le_top
      rw [cycles_eq_card_classes] at hb
      have hc : Nat.card (Quotient (SameCycle.setoid (M.vertex*q))) = 1 := by exact_mod_cast hb
      exact hc.trans card_quotient_top_one.symm
    exact top_unique (hs ▸ sameCycle_mul_le (p := M.vertex) (q := q) le_sup_left le_sup_right)
  let Q := M.subpairingGraph q (M.subpairing_sq q hq)
  have hQT : Q ≤ T := by
    rintro v w ⟨hne,x,rfl,rfl⟩
    have hx : q x ≠ x := fun he => hne (congrArg M.vertexClass he.symm)
    have hqx : q x = M.edge x := (hq x).resolve_left hx
    rw [hqx]
    have hex : ∃ ab ∈ t, x = ab.1 ∨ x = ab.2 := by
      by_contra hh
      push Not at hh
      exact hx (swaps_fix_of_outside t x hh)
    obtain ⟨ab,hab,ha | ha⟩ := hex
    all_goals
      have habl := (forestEdges_sublist _ l).subset hab
      have hpab := (hpairs ab habl).2
      have ht : T.Adj (M.vertexClass ab.1) (M.vertexClass ab.2) := by
        rw [show p ab.1 = if T.Adj (M.vertexClass ab.1) (M.vertexClass (M.edge ab.1))
          then M.edge ab.1 else ab.1 from rfl] at hpab
        split_ifs at hpab with hadj
        · rwa [hpab] at hadj
        · exact ((hpairs ab habl).1 hpab).elim
    · simpa only [ha,hmem ab habl] using ht
    · have haedge : M.edge ab.2 = ab.1 := by rw [← hmem ab habl,M.edge_edge]
      simpa only [ha,haedge] using ht.symm
  have hQc : Q.Connected := M.subpairing_connected q (M.subpairing_sq q hq) hqs
  have hmin := SimpleGraph.isTree_iff_minimal_connected.mp hT
  have hEQ : Q = T := le_antisymm hQT (hmin.2 hQc hQT)
  exact ⟨q,hq,hqs,hb,hEQ⟩

end HyperbolicObstruction.PictureSwitch.PictureMap
end
end

section

end
end

end OAI
