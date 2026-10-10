import OAI.Combinatorics.Hamiltonian.Rectangle

namespace OAI

/-! Graph realization and exact finite duality for topological plane embeddings. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V W E : Type*} [Fintype V] [Fintype W] [Fintype E]

def Realizes (G : SimpleGraph V) (M : Network V G.edgeSet) : Prop :=
  ∀ e, s(M.tail e, M.head e) = e.val

omit [Fintype V] in
lemma Realizes.graph_eq {G : SimpleGraph V} {M : Network V G.edgeSet}
    (h : M.Realizes G) : M.graph = G := by
  ext v w
  constructor
  · rintro ⟨_, e, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact G.mem_edgeSet.mp ((h e).symm ▸ e.property)
    · exact (G.mem_edgeSet.mp ((h e).symm ▸ e.property)).symm
  · intro hvw
    let e : G.edgeSet := ⟨s(v,w), hvw⟩
    refine ⟨hvw.ne, e, ?_⟩
    have he := h e
    change s(M.tail e, M.head e) = s(v,w) at he
    exact Sym2.eq_iff.mp he

omit [Fintype V] in
lemma Realizes.loopless {G : SimpleGraph V} {M : Network V G.edgeSet}
    (h : M.Realizes G) (e : G.edgeSet) : M.tail e ≠ M.head e := by
  have he : G.Adj (M.tail e) (M.head e) := G.mem_edgeSet.mp ((h e).symm ▸ e.property)
  exact he.ne

omit [Fintype V] in
lemma exists_dart_for_edge (G : SimpleGraph V) (e : G.edgeSet) :
    ∃ d : G.Dart, d.edge = e.val := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.inductionOn with
  | hf x y => exact ⟨⟨(x,y), he⟩, rfl⟩

omit [Fintype V] [Fintype W] [Fintype E] in
lemma connectedFibers_of_partition (N : Network W E) (q : W → V)
    (B : V → Set W) (hB : ∀ v, (N.graph.induce (B v)).Connected)
    (hmem : ∀ w v, q w = v ↔ w ∈ B v) : N.ConnectedFibers q := by
  intro x y hxy
  let T := N.restrict (Subtype.val : N.internal q → E)
  let f : N.graph.induce (B (q x)) →g T.graph := {
    toFun := Subtype.val
    map_rel' := by
      intro a b hab
      rcases hab with ⟨hne, e, he⟩
      have ha : q a.val = q x := (hmem _ _).mpr a.property
      have hb : q b.val = q x := (hmem _ _).mpr b.property
      have hei : e ∈ N.internal q := by
        rcases he with ⟨ht, hh⟩ | ⟨ht, hh⟩
        · change q (N.tail e) = q (N.head e)
          rw [ht, hh]; exact ha.trans hb.symm
        · change q (N.tail e) = q (N.head e)
          rw [ht, hh]; exact hb.trans ha.symm
      exact ⟨hne, ⟨e, hei⟩, he⟩ }
  have hx : x ∈ B (q x) := (hmem x (q x)).mp rfl
  have hy : y ∈ B (q x) := (hmem y (q x)).mp hxy.symm
  exact ((hB (q x)) ⟨x,hx⟩ ⟨y,hy⟩).map f

omit [Fintype E] in

theorem minor_quotient {G : SimpleGraph V} (hG : G.Connected)
    (N : Network W E) (hN : N.graph.Connected) (M : MinorModel G N.graph) :
    ∃ (q : W → V) (j : G.edgeSet → E), Function.Surjective q ∧
      N.ConnectedFibers q ∧ Function.Injective j ∧
      ((N.mapVertices q).restrict j).Realizes G := by
  have : Nonempty V := hG.nonempty
  obtain ⟨B, hsub, hconn, hdisj, hcover⟩ := BranchPartition.extend N.graph hN
    M.branch M.branch_connected M.branches_disjoint
  obtain ⟨q, hq, hmem⟩ := BranchPartition.quotient N.graph B hconn hdisj hcover
  choose d hd using exists_dart_for_edge G
  have hex (e : G.edgeSet) : ∃ k : E, s(q (N.tail k), q (N.head k)) = e.val := by
    obtain ⟨a, ha, b, hb, _, k, hk⟩ := M.adjacency (d e).fst (d e).snd (d e).adj
    have ha' : q a = (d e).fst := (hmem _ _).mpr (hsub _ ha)
    have hb' : q b = (d e).snd := (hmem _ _).mpr (hsub _ hb)
    refine ⟨k, ?_⟩
    rcases hk with ⟨ht, hh⟩ | ⟨ht, hh⟩
    · rw [ht, hh, ha', hb']; exact hd e
    · rw [ht, hh, ha', hb', Sym2.eq_swap]; exact hd e
  choose j hj using hex
  refine ⟨q, j, hq, N.connectedFibers_of_partition q B hconn hmem, ?_, hj⟩
  intro e f hef
  apply Subtype.ext
  exact (hj e).symm.trans ((congrArg (fun k => s(q (N.tail k), q (N.head k))) hef).trans (hj f))

universe uF
variable {F : Type uF} [Fintype F]

theorem Duality.graphMinor {G : SimpleGraph V} (hG : G.Connected)
    (N : Network W E) (D : Network F E) (h : N.Duality D)
    (M : MinorModel G N.graph) :
    ∃ (P : Network V G.edgeSet) (L : Type uF) (_ : Fintype L) (Q : Network L G.edgeSet),
      P.Realizes G ∧ P.Duality Q := by
  obtain ⟨q,j,hq,hc,hj,hreal⟩ := minor_quotient hG N h.connected M
  have he (e : G.edgeSet) : q (N.tail (j e)) ≠ q (N.head (j e)) := hreal.loopless e
  have hPc : ((N.mapVertices q).restrict j).graph.Connected := by
    rw [hreal.graph_eq]; exact hG
  obtain ⟨L, hL, Q, hQ⟩ := h.minor N D q hq hc j hj he hPc
  exact ⟨_, L, hL, Q, hreal, hQ⟩

end
end Barnette.Network

namespace Barnette.PlaneEmbedding
noncomputable section
open scoped Classical
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem exists_exact_dual (E : PlaneEmbedding G) (hG : G.Connected) :
    ∃ (P : Network V G.edgeSet) (F : Type) (_ : Fintype F) (D : Network F G.edgeSet),
      P.Realizes G ∧ P.Duality D := by
  obtain ⟨M⟩ := E.exists_lattice_minor_model
  obtain ⟨r, ⟨M'⟩⟩ := RectangularDual.lattice_minor_in_rectangle M
  exact (RectangularDual.grid_duality (2*r) (2*r)).graphMinor hG _ _ M'
end
end Barnette.PlaneEmbedding

end OAI
