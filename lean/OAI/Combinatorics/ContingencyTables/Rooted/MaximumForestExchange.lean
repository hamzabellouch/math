import OAI.Combinatorics.ContingencyTables.Rooted.MaximumForest

namespace OAI

/-! # The safe-edge invariant for the executed maximum-forest algorithm

At every step, choose a largest-capacity edge whose endpoints lie in
different current components. It extends the current forest inside a
maximum-weight forest. This is the exchange proof behind the binary
component-search implementation; no forest is enumerated by that program.
-/

namespace ContingencyTables.MaximumForestExchange

open SimpleGraph MaximumForest
open scoped BigOperators Classical

variable {V : Type*} [Fintype V]

omit [Fintype V] in
/-- In an acyclic supergraph, an edge between vertices already joined by
the subgraph must itself belong to that subgraph. -/
lemma adj_of_reachable_of_acyclic {T F : SimpleGraph V} (hTF : T≤F)
    (hF : F.IsAcyclic) {u v : V} (hr : T.Reachable u v) (hf : F.Adj u v) : T.Adj u v := by
  have hc : (T⊔edge u v).IsAcyclic :=
    hF.anti (sup_le hTF ((F.edge_le_iff).mpr (Or.inr hf)))
  have h := (isAcyclic_sup_fromEdgeSet_iff.mp hc).2 hr
  exact h.resolve_left hf.ne

omit [Fintype V] in
/-- Every path between different current components contains an edge
between different current components. -/
lemma path_crosses {T F : SimpleGraph V} {u v : V} (p : F.Walk u v)
    (hn : ¬T.Reachable u v) :
    ∃ a b,F.Adj a b ∧ s(a,b)∈p.edges ∧ ¬T.Reachable a b := by
  induction p with
  | nil => exact (hn (Reachable.refl _)).elim
  | @cons u w v h p ih =>
    by_cases hu : T.Reachable u w
    · obtain ⟨a,b,hab,he,hnab⟩ := ih (fun hw=>hn (hu.trans hw))
      exact ⟨a,b,hab,by simp only [Walk.edges_cons,List.mem_cons]; exact Or.inr he,hnab⟩
    · exact ⟨u,w,h,by simp only [Walk.edges_cons,List.mem_cons,true_or],hu⟩

lemma weight_delete {F : SimpleGraph V} (b : Sym2 V→ℕ)
    {e : Sym2 V} (he : e∈F.edgeSet) :
    weight (F.deleteEdges {e}) b+b e=weight F b := by
  have hs : (F.deleteEdges {e}).edgeFinset=F.edgeFinset.erase e := by
    ext a
    simp [edgeSet_deleteEdges,and_comm]
  rw [weight_eq (F.deleteEdges {e}),weight_eq F,hs]
  exact Finset.sum_erase_add (s:=F.edgeFinset) (a:=e) b (by simpa using he)

/-- The current forest is contained in some globally optimal forest. -/
def Extendible (G T : SimpleGraph V) (b : Sym2 V→ℕ) : Prop :=
  ∃ F : SimpleGraph V,T≤F ∧ F≤G ∧ F.IsAcyclic ∧
    ∀ H : SimpleGraph V,H≤G → H.IsAcyclic → weight H b≤weight F b

lemma bottom_extendible (G : SimpleGraph V) (b : Sym2 V→ℕ) : Extendible G ⊥ b := by
  obtain ⟨F,hFG,hF,hmax⟩ := exists_maximum G b
  exact ⟨F,bot_le,hFG,hF,hmax⟩

/-- A greatest edge joining two current components is safe. The argument
uses a maximum forest only as a witness for the invariant. -/
theorem safe_edge (G T : SimpleGraph V) (b : Sym2 V→ℕ)
    (hb : ∀ e∈G.edgeSet,0<b e) (hT : Extendible G T b)
    {u v : V} (he : G.Adj u v) (hn : ¬T.Reachable u v)
    (hbest : ∀ a d,G.Adj a d → ¬T.Reachable a d → b s(a,d)≤b s(u,v)) :
    Extendible G (T⊔edge u v) b := by
  obtain ⟨F,hTF,hFG,hF,hmax⟩ := hT
  by_cases hef : F.Adj u v
  · exact ⟨F,sup_le hTF ((F.edge_le_iff).mpr (Or.inr hef)),hFG,hF,hmax⟩
  have hspan := maximum_spans G F b hFG hF hmax hb
  have hreach : F.Reachable u v := by rw [hspan]; exact he.reachable
  obtain ⟨p,hp⟩ := hreach.exists_isPath
  obtain ⟨a,d,had,ht,hnad⟩ := path_crosses p hn
  let t := s(a,d)
  let D := F.deleteEdges {t}
  have htF : t∈F.edgeSet := by simpa only [t,mem_edgeSet] using had
  have htT : ¬T.Adj a d := fun h=>hnad h.reachable
  have hTD : T≤D := by
    intro x y hxy
    have hne : s(x,y)≠t := by
      intro hxyad
      have ha : T.Adj a d := by
        have hmem : t∈T.edgeSet := by rw [←hxyad]; simpa using hxy
        simpa only [t,mem_edgeSet] using hmem
      exact htT ha
    exact (deleteEdges_adj).mpr ⟨hTF hxy,by simpa only [Set.mem_singleton_iff] using hne⟩
  have hDF : D≤F := F.deleteEdges_le {t}
  have hDuv : ¬D.Reachable u v :=
    not_reachable_delete_path_edge F hF p hp t ht
  have hDacyc : (D⊔edge u v).IsAcyclic :=
    (hF.anti hDF).sup_edge_of_not_reachable hDuv
  have hDfree : ¬D.Adj u v := fun h=>hef (hDF h)
  have hDG : D⊔edge u v≤G :=
    sup_le (hDF.trans hFG) ((G.edge_le_iff).mpr (Or.inr he))
  have hweight := weight_sup_edge D b u v hDfree he.ne
  have hdelete := weight_delete b htF
  have hbetter := hbest a d (hFG had) hnad
  have hmono : weight F b≤weight (D⊔edge u v) b := by
    dsimp only [D,t] at hweight hdelete hbetter ⊢
    omega
  refine ⟨D⊔edge u v,sup_le_sup_right hTD _,hDG,hDacyc,?_⟩
  intro H hHG hH
  exact (hmax H hHG hH).trans hmono

/-- Once no edge joins different current components, the invariant
certifies global optimality of the current forest. -/
theorem finished (G T : SimpleGraph V) (b : Sym2 V→ℕ)
    (hT : Extendible G T b)
    (hn : ∀ u v,G.Adj u v → T.Reachable u v) :
    T≤G ∧ T.IsAcyclic ∧
      ∀ H : SimpleGraph V,H≤G → H.IsAcyclic → weight H b≤weight T b := by
  obtain ⟨F,hTF,hFG,hF,hmax⟩ := hT
  have hFT : F≤T := by
    intro u v hf
    exact adj_of_reachable_of_acyclic hTF hF (hn u v (hFG hf)) hf
  have heq : F=T := le_antisymm hFT hTF
  exact heq ▸ ⟨hFG,hF,hmax⟩

end ContingencyTables.MaximumForestExchange

end OAI
