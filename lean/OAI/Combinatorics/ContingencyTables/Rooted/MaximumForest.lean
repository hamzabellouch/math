import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Data.Finset.Max
import Lean.Elab.Tactic.Omega

namespace OAI

/-!
# The companion's maximum-capacity forest

Among finite acyclic subgraphs choose one of maximum total capacity.
Positive capacities make it spanning in each large-cell component. A
free edge can replace every tree edge on its path; optimality therefore
gives the exact path-capacity inequality used in the forest estimates.
-/

namespace ContingencyTables.MaximumForest

open scoped BigOperators Classical
open SimpleGraph

variable {V : Type*} [Fintype V]

noncomputable def weight (G : SimpleGraph V) (b : Sym2 V → ℕ) : ℕ :=
  ∑ e ∈ G.edgeFinset, b e

lemma weight_eq (G : SimpleGraph V) (b : Sym2 V → ℕ) [Fintype G.edgeSet] :
    weight G b=∑ e∈G.edgeFinset,b e := by
  unfold weight
  apply Finset.sum_congr
  · ext e
    simp only [mem_edgeFinset]
  · intro e _
    rfl

theorem exists_maximum (G : SimpleGraph V) (b : Sym2 V → ℕ) :
    ∃ T : SimpleGraph V, T ≤ G ∧ T.IsAcyclic ∧
      ∀ F : SimpleGraph V, F ≤ G → F.IsAcyclic → weight F b ≤ weight T b := by
  let S : Finset (SimpleGraph V) := Finset.univ.filter (fun F => F ≤ G ∧ F.IsAcyclic)
  have hS : S.Nonempty := ⟨⊥,by simp [S]⟩
  obtain ⟨T,hT,hmax⟩ := Finset.exists_max_image S (fun F => weight F b) hS
  have hp := (Finset.mem_filter.mp hT).2
  refine ⟨T,hp.1,hp.2,?_⟩
  intro F hFG hacyc
  exact hmax F (by simp [S,hFG,hacyc])

lemma weight_sup_edge (T : SimpleGraph V) (b : Sym2 V → ℕ) (u v : V)
    (hn : ¬T.Adj u v) (hne : u≠v) :
    weight (T ⊔ edge u v) b=b s(u,v)+weight T b := by
  rw [weight_eq (T ⊔ edge u v),weight_eq T,T.edgeFinset_sup_edge hn hne,Finset.sum_cons]

omit [Fintype V] in
/-- Deleting an edge of the unique tree path separates its endpoints. -/
lemma not_reachable_delete_path_edge (T : SimpleGraph V) (hT : T.IsAcyclic)
    {u v : V} (p : T.Walk u v) (hp : p.IsPath) (t : Sym2 V) (ht : t∈p.edges) :
    ¬(T.deleteEdges {t}).Reachable u v := by
  intro hreach
  obtain ⟨q,hq⟩ := hreach.exists_isPath
  have he : p=q.mapLe (T.deleteEdges_le {t}) := congrArg Subtype.val
    ((hT.subsingleton_path u v).elim ⟨p,hp⟩ ⟨q.mapLe (T.deleteEdges_le {t}),hq.mapLe _⟩)
  rw [he] at ht
  simp only [Walk.edges_map,Hom.coe_ofLE,Sym2.map_id,List.map_id_fun,id_eq] at ht
  have hmem := q.edges_subset_edgeSet ht
  rw [edgeSet_deleteEdges] at hmem
  exact hmem.2 (by simp)

/-- This is the source's actual maximum-forest path inequality. -/
theorem free_edge_le_path_edge (G T : SimpleGraph V) (b : Sym2 V → ℕ)
    (hTG : T ≤ G) (hT : T.IsAcyclic)
    (hmax : ∀ F : SimpleGraph V, F ≤ G → F.IsAcyclic → weight F b ≤ weight T b)
    {u v : V} (hG : G.Adj u v) (hfree : ¬T.Adj u v)
    (p : T.Walk u v) (hp : p.IsPath) (t : Sym2 V) (ht : t∈p.edges) :
    b s(u,v) ≤ b t := by
  let D := T.deleteEdges {t}
  have hDT : D ≤ T := T.deleteEdges_le {t}
  have hDfree : ¬D.Adj u v := fun h => hfree (hDT h)
  have hcut : ¬D.Reachable u v := not_reachable_delete_path_edge T hT p hp t ht
  have hnew : (D ⊔ edge u v).IsAcyclic := (hT.anti hDT).sup_edge_of_not_reachable hcut
  have hnewG : D ⊔ edge u v ≤ G := sup_le (hDT.trans hTG) ((G.edge_le_iff).mpr (Or.inr hG))
  have hopt := hmax (D ⊔ edge u v) hnewG hnew
  have hsum := weight_sup_edge D b u v hDfree hG.ne
  have hmem : t∈T.edgeFinset := by simpa using p.edges_subset_edgeSet ht
  have hdelete : D.edgeFinset=T.edgeFinset.erase t := by
    ext e
    simp [D,edgeSet_deleteEdges,and_comm]
  have hsumDelete : weight D b+b t=weight T b := by
    rw [weight_eq D,weight_eq T,hdelete]
    exact Finset.sum_erase_add (s := T.edgeFinset) (a := t) b hmem
  omega

/-- The same exchange argument applies directly to a separating cut;
this avoids choosing a path when using the forest's component cuts. -/
theorem free_edge_le_separating_edge (G T : SimpleGraph V) (b : Sym2 V → ℕ)
    (hTG : T ≤ G) (hT : T.IsAcyclic)
    (hmax : ∀ F : SimpleGraph V, F ≤ G → F.IsAcyclic → weight F b ≤ weight T b)
    (t : Sym2 V) (ht : t∈T.edgeSet) {u v : V}
    (hG : G.Adj u v) (hfree : ¬T.Adj u v)
    (hcut : ¬(T.deleteEdges {t}).Reachable u v) : b s(u,v) ≤ b t := by
  let D := T.deleteEdges {t}
  have hDT : D ≤ T := T.deleteEdges_le {t}
  have hDfree : ¬D.Adj u v := fun h => hfree (hDT h)
  have hnew : (D ⊔ edge u v).IsAcyclic := (hT.anti hDT).sup_edge_of_not_reachable hcut
  have hnewG : D ⊔ edge u v ≤ G := sup_le (hDT.trans hTG) ((G.edge_le_iff).mpr (Or.inr hG))
  have hopt := hmax (D ⊔ edge u v) hnewG hnew
  have hsum := weight_sup_edge D b u v hDfree hG.ne
  have hmem : t∈T.edgeFinset := by simpa using ht
  have hdelete : D.edgeFinset=T.edgeFinset.erase t := by
    ext e
    simp [D,edgeSet_deleteEdges,and_comm]
  have hsumDelete : weight D b+b t=weight T b := by
    rw [weight_eq D,weight_eq T,hdelete]
    exact Finset.sum_erase_add (s := T.edgeFinset) (a := t) b hmem
  omega

omit [Fintype V] in
noncomputable def side (D : SimpleGraph V) (u v : V) : Bool := decide (D.Reachable u v)

omit [Fintype V] in
lemma side_self (D : SimpleGraph V) (u : V) : side D u u=true := by
  simp [side]

omit [Fintype V] in
lemma side_eq_of_reachable (D : SimpleGraph V) (u : V) {v w : V}
    (h : D.Reachable v w) : side D u v=side D u w := by
  apply Bool.eq_iff_iff.mpr
  simp only [side,decide_eq_true_eq]
  exact ⟨fun hv => hv.trans h,fun hw => hw.trans h.symm⟩

omit [Fintype V] in
lemma not_reachable_of_side_ne (D : SimpleGraph V) (u : V) {v w : V}
    (h : side D u v≠side D u w) : ¬D.Reachable v w := by
  exact fun hr => h (side_eq_of_reachable D u hr)

omit [Fintype V] in
/-- Every other tree edge is internal to a deletion component. -/
lemma side_eq_of_tree_edge (T : SimpleGraph V) (t : Sym2 V) (u : V) {v w : V}
    (h : T.Adj v w) (hne : s(v,w)≠t) :
    side (T.deleteEdges {t}) u v=side (T.deleteEdges {t}) u w := by
  apply side_eq_of_reachable
  exact (show (T.deleteEdges {t}).Adj v w by simp [h,hne]).reachable

omit [Fintype V] in
/-- One deletion component contains an endpoint of the removed edge
and avoids the chosen root. This also works for isolated components. -/
lemma exists_root_avoiding_side (T : SimpleGraph V) (hT : T.IsAcyclic)
    {u v : V} (ht : T.Adj u v) (root : V) (hroot : T.Reachable root u) :
    ∃ r : V, T.Reachable root r ∧ side (T.deleteEdges {s(u,v)}) r root=false ∧
      side (T.deleteEdges {s(u,v)}) r u≠side (T.deleteEdges {s(u,v)}) r v := by
  let D := T.deleteEdges {s(u,v)}
  have hsep : ¬D.Reachable u v :=
    isBridge_iff.mp (isAcyclic_iff_forall_adj_isBridge.mp hT ht)
  by_cases hru : D.Reachable u root
  · refine ⟨v,hroot.trans ht.reachable,?_,?_⟩
    · have hn : ¬D.Reachable v root := fun h => hsep (hru.trans h.symm)
      simpa only [side,decide_eq_false_iff_not] using hn
    · have hn : ¬D.Reachable v u := fun h => hsep h.symm
      change side D v u≠side D v v
      simp [side,hn]
  · refine ⟨u,hroot,?_,?_⟩
    · simpa only [side,decide_eq_false_iff_not] using hru
    · change side D u u≠side D u v
      simp [side,hsep]

/-- Capacities of actual free edges crossing a deletion component are
bounded by the capacity of its unique deleted tree edge. -/
theorem crossing_free_edge_le (G T : SimpleGraph V) (b : Sym2 V → ℕ)
    (hTG : T ≤ G) (hT : T.IsAcyclic)
    (hmax : ∀ F : SimpleGraph V, F ≤ G → F.IsAcyclic → weight F b ≤ weight T b)
    (t : Sym2 V) (ht : t∈T.edgeSet) (r : V) {u v : V}
    (hG : G.Adj u v) (hfree : ¬T.Adj u v)
    (hcross : side (T.deleteEdges {t}) r u≠side (T.deleteEdges {t}) r v) :
    b s(u,v) ≤ b t :=
  free_edge_le_separating_edge G T b hTG hT hmax t ht hG hfree
    (not_reachable_of_side_ne _ r hcross)

/-- Positive capacities force the maximizing acyclic subgraph to span
every original connected component, including isolated vertices. -/
theorem maximum_spans (G T : SimpleGraph V) (b : Sym2 V → ℕ)
    (hTG : T ≤ G) (hT : T.IsAcyclic)
    (hmax : ∀ F : SimpleGraph V, F ≤ G → F.IsAcyclic → weight F b ≤ weight T b)
    (hb : ∀ e∈G.edgeSet, 0 < b e) : T.Reachable=G.Reachable := by
  have hadj : ∀ u v, G.Adj u v → T.Reachable u v := by
    intro u v hG
    by_contra hnreach
    have hn : ¬T.Adj u v := fun h => hnreach h.reachable
    have hnew := hT.sup_edge_of_not_reachable hnreach
    have hle : T ⊔ edge u v ≤ G := sup_le hTG ((G.edge_le_iff).mpr (Or.inr hG))
    have hopt := hmax (T ⊔ edge u v) hle hnew
    have hsum := weight_sup_edge T b u v hn hG.ne
    have hpos := hb s(u,v) (by simpa using hG)
    omega
  funext u v
  apply propext
  constructor
  · intro h; exact h.mono hTG
  · rintro ⟨p⟩
    induction p with
    | nil => exact ⟨Walk.nil⟩
    | cons h p ih => exact (hadj _ _ h).trans ih

end ContingencyTables.MaximumForest

end OAI
