import OAI.NumberTheory.Ostmann.Tree.CycleSelection

namespace OAI

namespace Ostmann.Tree

theorem graph_cycle_of_edges_ge_vertices {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (hcard : Fintype.card V ≤ Fintype.card G.edgeSet) :
    ∃ v : V, ∃ p : G.Walk v v, p.IsCycle := by
  classical
  by_contra! hn
  have hacyclic : G.IsAcyclic := fun v p => hn v p
  obtain ⟨T,hGT,_,hT⟩ := SimpleGraph.connected_top.exists_isTree_le_of_le_of_isAcyclic
    (G := (⊤ : SimpleGraph V)) (H := G) le_top hacyclic
  have htcard := hT.card_edgeFinset
  have hle := Finset.card_le_card (SimpleGraph.edgeFinset_mono hGT)
  rw [SimpleGraph.edgeFinset_card] at hle
  omega

def incidenceGraph {E V W : Type*} (left : E → V) (right : E → W) : SimpleGraph (V ⊕ W) where
  Adj x y := match x,y with
    | .inl v, .inr w => ∃ e, left e=v ∧ right e=w
    | .inr w, .inl v => ∃ e, left e=v ∧ right e=w
    | _,_ => False
  symm := ⟨by rintro (v|w) (v'|w') h <;> exact h⟩
  loopless := ⟨by rintro (v|w) h <;> exact h⟩

noncomputable def incidenceEdgeEmbedding {E V W : Type*} (left : E → V) (right : E → W)
    (hinj : Function.Injective (fun e => (left e,right e))) :
    E ↪ (incidenceGraph left right).edgeSet where
  toFun e := ⟨s(Sum.inl (left e),Sum.inr (right e)), ⟨e,rfl,rfl⟩⟩
  inj' := by
    intro e f h
    have he : s(Sum.inl (left e),Sum.inr (right e)) =
        s(Sum.inl (left f),Sum.inr (right f)) := congrArg Subtype.val h
    apply hinj
    rcases Sym2.eq_iff.mp he with he | he
    · exact Prod.ext (Sum.inl.inj he.1) (Sum.inr.inj he.2)
    · cases he.1

theorem incidence_cycle_or_parallel {E V W : Type*}
    [Fintype E] [Fintype V] [Fintype W] [Nonempty E]
    (left : E → V) (right : E → W)
    (hcard : Fintype.card V+Fintype.card W ≤ Fintype.card E) :
    (∃ e f : E, e ≠ f ∧ left e=left f ∧ right e=right f) ∨
      ∃ v : V ⊕ W, ∃ p : (incidenceGraph left right).Walk v v, p.IsCycle := by
  classical
  by_cases hinj : Function.Injective (fun e => (left e,right e))
  · right
    let : Nonempty (V ⊕ W) := ⟨Sum.inl (left (Classical.choice (inferInstance : Nonempty E)))⟩
    apply graph_cycle_of_edges_ge_vertices
    have hle := Fintype.card_le_of_injective _ (incidenceEdgeEmbedding left right hinj).injective
    rw [Fintype.card_sum]
    exact hcard.trans hle
  · left
    unfold Function.Injective at hinj
    push Not at hinj
    obtain ⟨e,f,he,hef⟩ := hinj
    exact ⟨e,f,hef,congrArg Prod.fst he,congrArg Prod.snd he⟩

end Ostmann.Tree

end OAI
