import OAI.Combinatorics.Hamiltonian.ExactDual

namespace OAI

/-! Hamiltonian cycles in cubic bipartite three-vertex-connected plane graphs. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
    [DecidableEq V] (N : Network V E) (D : Network F E)

theorem Duality.hamiltonian (h : N.Duality D) (hN : N.Simple)
    (hc : N.graph.IsRegularOfDegree 3) (h3 : N.ThreeEdgeConnected)
    (black : V → Prop) (hb : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) :
    HasHamiltonianCycle N.graph := by
  obtain ⟨v⟩ := h.connected.nonempty
  have hs : (N.star v).Nonempty := by
    apply Finset.card_pos.mp
    rw [N.card_star hN,hc v]
    decide
  obtain ⟨e,_⟩ := hs
  obtain ⟨P,_,hP,hPc⟩ := h.connected_complement_matching N D hN hc h3 black hb e
  let H := (N.restrict (Subtype.val : ↥Pᶜ → E)).graph
  have hdeg : H.IsRegularOfDegree 2 := N.matching_complement_two hN hc P hP
  obtain ⟨p,hp⟩ := Barnette.SimpleCycle.cycle_at_of_connected_two H hPc hdeg v
  let f : H →g N.graph := {
    toFun := id
    map_rel' := by
      rintro a b ⟨hne,k,hk⟩
      exact ⟨hne,k.val,hk⟩ }
  exact ⟨v,p.map f,hp.map Function.bijective_id⟩
end
end Barnette.Network

namespace Barnette
universe u
noncomputable section
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V}

lemma ThreeVertexConnected.connected (h : ThreeVertexConnected G) : G.Connected := by
  let H := G.induce {v | v ∉ (∅ : Finset V)}
  let f : H →g G := { toFun := Subtype.val, map_rel' := fun h => h }
  exact (h.2 ∅ (by simp)).map f (fun v => ⟨⟨v,by simp⟩,rfl⟩)

theorem main : MainStatement.{u} := by
  intro V hV dV G dG hc hb hp h3
  have hdeq : dV = Classical.decEq V := Subsingleton.elim _ _
  subst dV
  have hdrel : dG = fun a b => Classical.propDecidable (G.Adj a b) := Subsingleton.elim _ _
  subst dG
  obtain ⟨E⟩ := hp
  have hconn := h3.connected
  let : Nonempty V := hconn.nonempty
  have horder := cubic_bipartite_order hc hb
  obtain ⟨N,F,f,D,hr,hd⟩ := E.exists_exact_dual hconn
  let : Fintype F := f
  have hN : N.Simple := by
    refine ⟨hr.loopless,?_⟩
    intro e f hef
    apply Subtype.ext
    rw [← hr e,← hr f]
    exact hef
  have hc' : N.graph.IsRegularOfDegree 3 := by rw [hr.graph_eq]; exact hc
  have h3' : ThreeVertexConnected N.graph := hr.graph_eq.symm ▸ h3
  have hec : N.ThreeEdgeConnected := by
    intro A ha ho
    obtain ⟨w,hw⟩ := ho
    exact N.cut_card_three h3' (by omega) A ha ⟨w,Finset.mem_compl.mp hw⟩
  obtain ⟨color⟩ := hb
  let black : V → Prop := fun v => color v = 0
  have hcolor (e : G.edgeSet) : black (N.tail e) ↔ ¬black (N.head e) := by
    have hne := color.valid (G.mem_edgeSet.mp ((hr e).symm ▸ e.property))
    have ht := (color (N.tail e)).isLt
    have hh := (color (N.head e)).isLt
    have hne' : (color (N.tail e)).val ≠ (color (N.head e)).val := fun h => hne (Fin.ext h)
    change color (N.tail e) = 0 ↔ ¬color (N.head e) = 0
    simp only [Fin.ext_iff,Fin.val_zero]
    omega
  have hh := hd.hamiltonian N D hN hc' hec black hcolor
  rwa [hr.graph_eq] at hh
end
end Barnette

end OAI
