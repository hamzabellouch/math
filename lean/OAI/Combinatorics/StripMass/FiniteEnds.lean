import Mathlib
import OAI.Combinatorics.StripMass.SewnAssignment

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram.PathGraph
noncomputable section
open scoped Classical

 

lemma reachable_of_odd_terminals {V : Type*} [Fintype V] (G : SimpleGraph V)
    {a b : V} (ha : Odd (G.degree a))
    (he : ∀ v, Odd (G.degree v) → v=a ∨ v=b) : G.Reachable a b := by
  let S : Set V := {v | G.Reachable a v}
  let H := G.induce S
  have hd (v : S) : H.degree v=G.degree v := by
    apply G.degree_induce_of_neighborSet_subset
    intro w hw
    exact v.property.trans hw.reachable
  let a' : S := ⟨a,SimpleGraph.Reachable.refl a⟩
  have ha' : Odd (H.degree a') := by simpa only [hd] using ha
  obtain ⟨w,hw,ho⟩ := H.exists_ne_odd_degree_of_exists_odd_degree a' ha'
  rw [hd] at ho
  rcases he w ho with hwa | hwb
  · exact (hw (Subtype.ext hwa)).elim
  · exact hwb ▸ w.property

lemma degree_eq_one_of_single {V : Type*} [Fintype V] (G : SimpleGraph V) {a : V}
    (ha : AtMostOne G.Adj a) (hu : Graph.Used G.Adj a) : G.degree a=1 := by
  obtain ⟨b,hb⟩ := hu
  rw [←G.card_neighborFinset_eq_degree]
  have he : G.neighborFinset a={b} := by
    ext v
    simp only [SimpleGraph.mem_neighborFinset,Finset.mem_singleton]
    exact ⟨fun h=>ha h hb,fun h=>h ▸ hb⟩
  rw [he,Finset.card_singleton]

lemma degree_eq_two_of_two {V : Type*} [Fintype V] (G : SimpleGraph V)
    (h₂ : AtMostTwo G.Adj) {v : V} (hv : ∃ x y, G.Adj v x ∧ G.Adj v y ∧ x≠y) :
    G.degree v=2 := by
  obtain ⟨x,y,hx,hy,hxy⟩ := hv
  rw [←G.card_neighborFinset_eq_degree]
  have he : G.neighborFinset v={x,y} := by
    ext z
    simp only [SimpleGraph.mem_neighborFinset,Finset.mem_insert,Finset.mem_singleton]
    exact ⟨fun h=>h₂ hx hy h hxy,fun h=>h.elim (fun h=>h ▸ hx) (fun h=>h ▸ hy)⟩
  simp [he,hxy]

 

lemma endpoints_connected {V : Type*} [Fintype V] (G : SimpleGraph V)
    (h₂ : AtMostTwo G.Adj) {a b : V} (ha : AtMostOne G.Adj a)
    (hu : Graph.Used G.Adj a)
    (hi : ∀ v, v≠a → v≠b → Graph.Used G.Adj v →
      ∃ x y, G.Adj v x ∧ G.Adj v y ∧ x≠y) : G.Reachable a b := by
  apply reachable_of_odd_terminals G
  · rw [degree_eq_one_of_single G ha hu]
    exact odd_one
  · intro v hv
    by_cases hva : v=a
    · exact Or.inl hva
    by_cases hvb : v=b
    · exact Or.inr hvb
    exfalso
    by_cases hu : Graph.Used G.Adj v
    · rw [degree_eq_two_of_two G h₂ (hi v hva hvb hu)] at hv
      exact (by decide : ¬Odd (2:ℕ)) hv
    · have hz : G.degree v=0 := by
        rw [SimpleGraph.degree_eq_zero]
        intro w hw
        exact hu ⟨w,hw⟩
      rw [hz] at hv
      exact (by decide : ¬Odd (0:ℕ)) hv

 

lemma endpoints_connected_finite_support {V : Type*} (G : SimpleGraph V)
    (hf : G.support.Finite) (h₂ : AtMostTwo G.Adj) {a b : V}
    (ha : AtMostOne G.Adj a) (hu : Graph.Used G.Adj a)
    (hi : ∀ v, v≠a → v≠b → Graph.Used G.Adj v →
      ∃ x y, G.Adj v x ∧ G.Adj v y ∧ x≠y) :
    Relation.ReflTransGen G.Adj a b := by
  
  let S : Set V := insert b G.support
  have hs : S.Finite := hf.insert b
  let := hs.fintype
  let H := G.induce S
  let a' : S := ⟨a,Set.mem_insert_of_mem b hu⟩
  let b' : S := ⟨b,Set.mem_insert b _⟩
  have h₂' : AtMostTwo H.Adj := by
    intro v x y z hx hy hz hxy
    rcases h₂ hx hy hz (fun h=>hxy (Subtype.ext h)) with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have ha' : AtMostOne H.Adj a' := by
    intro x y hx hy
    exact Subtype.ext (ha hx hy)
  have hu' : Graph.Used H.Adj a' := by
    obtain ⟨w,hw⟩:=hu
    exact ⟨⟨w,Set.mem_insert_of_mem b ⟨a,G.symm.symm _ _ hw⟩⟩,hw⟩
  have hi' : ∀ v : S, v≠a' → v≠b' → Graph.Used H.Adj v →
      ∃ x y, H.Adj v x ∧ H.Adj v y ∧ x≠y := by
    intro v hva hvb hv
    have hv' : Graph.Used G.Adj v.val := by
      obtain ⟨w,hw⟩:=hv
      exact ⟨w.val,hw⟩
    obtain ⟨x,y,hx,hy,hxy⟩:=hi v (fun h=>hva (Subtype.ext h))
      (fun h=>hvb (Subtype.ext h)) hv'
    let x' : S := ⟨x,Set.mem_insert_of_mem b ⟨v,G.symm.symm _ _ hx⟩⟩
    let y' : S := ⟨y,Set.mem_insert_of_mem b ⟨v,G.symm.symm _ _ hy⟩⟩
    exact ⟨x',y',hx,hy,fun h=>hxy (congrArg Subtype.val h)⟩
  have hr := (SimpleGraph.reachable_iff_reflTransGen (G := H) a' b').mp
    (endpoints_connected H h₂' ha' hu' hi')
  exact Graph.map_reach Subtype.val (fun _ _ h=>.single h) hr

 

lemma drains_of_two_terminals {V : Type*} (G : SimpleGraph V)
    (hf : G.support.Finite) (h₂ : AtMostTwo G.Adj) {a b : V}
    (ha : AtMostOne G.Adj a) (hu : Graph.Used G.Adj a)
    (hi : ∀ v, v≠a → v≠b → Graph.Used G.Adj v →
      ∃ x y, G.Adj v x ∧ G.Adj v y ∧ x≠y)
    (hd : ∀ v w, G.Adj v w → Relation.ReflTransGen G.Adj v a ∨
      Relation.ReflTransGen G.Adj v b) : Graph.DrainsAt G.Adj a := by
  have := G.symm
  have hr:=endpoints_connected_finite_support G hf h₂ ha hu hi
  intro v w hvw
  exact (hd v w hvw).elim id (fun hv=>hv.trans (symm hr))

end
end CriticalStrip.Diagram.PathGraph

 

 

namespace CriticalStrip
noncomputable section
open scoped Classical
open Diagram Diagram.PathGraph

namespace Diagram.Graph

 

lemma reach_exit {V : Type*} {r : V → V → Prop} {S : Set V} {x z : V}
    (h : Relation.ReflTransGen r x z) (hx : x∈S) (hz : z∉S) :
    ∃ u v, u∈S ∧ v∉S ∧ r u v ∧
      Relation.ReflTransGen (fun a b=>a∈S ∧ b∈S ∧ r a b) x u := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact (hz hx).elim
  | @head y w hxy h ih =>
    by_cases hy : w∈S
    · obtain ⟨u,v,hu,hv,huv,hr⟩:=ih hy
      exact ⟨u,v,hu,hv,huv,hr.head ⟨hx,hy,hxy⟩⟩
    · exact ⟨y,w,hx,hy,hxy,.refl⟩

end Diagram.Graph

namespace HoneycombAssignment
variable {N M : ℕ}

 

def restrict (D : HoneycombAssignment N) (M : ℕ) (hM : M≤N) : HoneycombAssignment M where
  tile q := if q.2<M then D.tile q else .vacant
  physical q := by split <;> first | exact D.physical q | decide
  outside i j hj := ite_eq_right (by omega)
  horizontal i j := by
    by_cases hj : j<M
    · simp only [hj,ite_true]; exact D.horizontal i j
    · simp only [hj,ite_false,Tile.vacant_not_occupied]
  vertical i j hj := by
    have hj' : j<M := by omega
    simp only [hj,hj',ite_true]
    exact D.vertical i j (by omega)

@[simp] lemma restrict_tile (D : HoneycombAssignment N) (M : ℕ) (hM : M≤N)
    (i : ℤ) (j : ℕ) (hj : j<M) : (D.restrict M hM).tile (i,j)=D.tile (i,j) := by
  simp [restrict,hj]

lemma restrict_adj (D : HoneycombAssignment N) (M : ℕ) (hM : M≤N) (v w : Triangle) :
    (D.restrict M hM).graph.Adj v w ↔
      v.2.1<M ∧ w.2.1<M ∧ D.graph.Adj v w := by
  by_cases hv : v.2.1<M
  · by_cases hw : w.2.1<M
    · have hvN : v.2.1<N := lt_of_lt_of_le hv hM
      have hwN : w.2.1<N := lt_of_lt_of_le hw hM
      simp only [graph,tileGraph,hv,hw,hvN,hwN,true_and,upDownWire,
        restrict_tile D M hM v.1 v.2.1 hv,restrict_tile D M hM w.1 w.2.1 hw]
    · simp only [graph,tileGraph,hw,and_false,hv,false_and]
  · simp only [graph,tileGraph,hv,false_and]

lemma up_two (D : HoneycombAssignment N) (i : ℤ) (j : ℕ)
    (hbot : j=0 → ¬(D.tile (i,j)).Occupied 0)
    (hu : Graph.Used D.graph.Adj (up i j)) :
    ∃ x y,D.graph.Adj (up i j) x ∧ D.graph.Adj (up i j) y ∧ x≠y := by
  obtain ⟨w,hw⟩:=hu
  obtain ⟨hn,hw⟩:=(D.up_neighbors i j w).mp hw
  have hp : (D.tile (i,j)).Occupied 0 → 0<j := by
    intro h; by_contra hj; exact hbot (by omega) h
  rcases Tile.physical_up (D.tile (i,j)) (D.physical (i,j)) with h|h|h|h
  · rcases hw with ⟨_,hm⟩|⟨_,he⟩|⟨_,_,hs⟩
    · exact (h.2.2 hm).elim
    · exact (h.2.1 he).elim
    · exact (h.1 hs).elim
  · refine ⟨down i (j-1),down (i-1) j,
      (D.up_neighbors i j _).mpr ⟨hn,Or.inr (Or.inr ⟨hp h.1,rfl,h.1⟩)⟩,
      (D.up_neighbors i j _).mpr ⟨hn,Or.inr (Or.inl ⟨rfl,h.2.1⟩)⟩,?_⟩
    simp only [down,Prod.mk.injEq,ne_eq]; omega
  · refine ⟨down i (j-1),down i j,
      (D.up_neighbors i j _).mpr ⟨hn,Or.inr (Or.inr ⟨hp h.1,rfl,h.1⟩)⟩,
      (D.up_neighbors i j _).mpr ⟨hn,Or.inl ⟨rfl,h.2.2⟩⟩,?_⟩
    have hj := hp h.1
    simp only [down,Prod.mk.injEq,true_and,ne_eq]; omega
  · refine ⟨down (i-1) j,down i j,
      (D.up_neighbors i j _).mpr ⟨hn,Or.inr (Or.inl ⟨rfl,h.2.1⟩)⟩,
      (D.up_neighbors i j _).mpr ⟨hn,Or.inl ⟨rfl,h.2.2⟩⟩,?_⟩
    simp only [down,Prod.mk.injEq,ne_eq]; omega

lemma down_two (D : HoneycombAssignment N) (i : ℤ) (j : ℕ)
    (htop : j+1=N → ¬(D.tile (i,j)).Occupied 3)
    (hu : Graph.Used D.graph.Adj (down i j)) :
    ∃ x y,D.graph.Adj (down i j) x ∧ D.graph.Adj (down i j) y ∧ x≠y := by
  obtain ⟨w,hw⟩:=hu
  obtain ⟨hn,hw⟩:=(D.down_neighbors i j w).mp hw
  have hp : (D.tile (i,j)).Occupied 3 → j+1<N := by
    intro h; by_contra hj; exact htop (by omega) h
  rcases Tile.physical_down (D.tile (i,j)) (D.physical (i,j)) with h|h|h|h
  · rcases hw with ⟨_,hm⟩|⟨_,he⟩|⟨_,_,hs⟩
    · exact (h.2.2 hm).elim
    · exact (h.1 he).elim
    · exact (h.2.1 hs).elim
  · refine ⟨up (i+1) j,up i (j+1),
      (D.down_neighbors i j _).mpr ⟨hn,Or.inr (Or.inl ⟨rfl,h.1⟩)⟩,
      (D.down_neighbors i j _).mpr ⟨hn,Or.inr (Or.inr ⟨hp h.2.1,rfl,h.2.1⟩)⟩,?_⟩
    simp [up]
  · refine ⟨up (i+1) j,up i j,
      (D.down_neighbors i j _).mpr ⟨hn,Or.inr (Or.inl ⟨rfl,h.1⟩)⟩,
      (D.down_neighbors i j _).mpr ⟨hn,Or.inl ⟨rfl,h.2.2⟩⟩,?_⟩
    simp [up]
  · refine ⟨up i (j+1),up i j,
      (D.down_neighbors i j _).mpr ⟨hn,Or.inr (Or.inr ⟨hp h.2.1,rfl,h.2.1⟩)⟩,
      (D.down_neighbors i j _).mpr ⟨hn,Or.inl ⟨rfl,h.2.2⟩⟩,?_⟩
    simp [up]

lemma two_interior_top (D : HoneycombAssignment N) (hN : 1≤N) (a b : ℤ)
    (hs : ∀i,¬(D.tile (i,0)).Occupied 0)
    (ht : ∀i,(D.tile (i,N-1)).Occupied 3 → i=a ∨ i=b)
    (v : Triangle) (ha : v≠down a (N-1)) (hb : v≠down b (N-1))
    (hu : Graph.Used D.graph.Adj v) :
    ∃x y,D.graph.Adj v x ∧ D.graph.Adj v y ∧ x≠y := by
  rcases v with ⟨i,j,c⟩
  cases c
  · apply D.down_two i j _ hu
    intro hj ho
    have hj' : j=N-1 := by omega
    subst j
    exact (ht i ho).elim (fun h=>ha (by subst i; rfl)) (fun h=>hb (by subst i; rfl))
  · exact D.up_two i j (fun hj=>by subst j; exact hs i) hu

 

theorem restrict_drains_of_two_top (D : HoneycombAssignment (N+1)) (hN : 1≤N)
    (a b : ℤ) (root : Triangle) (hr : root.2.1=N)
    (hd : Graph.DrainsAt D.graph.Adj root)
    (hf : (D.restrict N (by omega)).graph.support.Finite)
    (hs : ∀i,¬(D.tile (i,0)).Occupied 0)
    (ht : ∀i,(D.tile (i,N)).Occupied 0 ↔ i=a ∨ i=b) :
    Graph.DrainsAt (D.restrict N (by omega)).graph.Adj (down b (N-1)) := by
  let E := D.restrict N (by omega)
  have ht' (i : ℤ) : (E.tile (i,N-1)).Occupied 3 ↔ i=a ∨ i=b := by
    rw [show E.tile (i,N-1)=D.tile (i,N-1) from D.restrict_tile N (by omega) i (N-1) (by omega)]
    have he := D.vertical i (N-1) (by omega)
    rw [show N-1+1=N by omega] at he
    exact he.trans (ht i)
  have hs' (i : ℤ) : ¬(E.tile (i,0)).Occupied 0 := by
    simpa only [show E.tile (i,0)=D.tile (i,0) from D.restrict_tile N (by omega) i 0 (by omega)] using hs i
  apply PathGraph.drains_of_two_terminals E.graph hf E.two (E.top_one hN ((ht' b).mpr (Or.inr rfl)))
    (E.top_used hN ((ht' b).mpr (Or.inr rfl)))
    (E.two_interior_top hN b a hs' (fun i h=>(ht' i |>.mp h).symm))
  intro v w hvw
  have hm := (D.restrict_adj N (by omega) v w).mp hvw
  have hvr := hd v w hm.2.2
  obtain ⟨x,y,hx,hy,hxy,hvx⟩:=Graph.reach_exit (S:={v : Triangle | v.2.1<N}) hvr hm.1 (by simp [hr])
  have hvx' : Relation.ReflTransGen E.graph.Adj v x :=
    Relation.ReflTransGen.mono (fun s t h=>(D.restrict_adj N (by omega) s t).mpr h) _ _ hvx
  rcases x with ⟨i,j,c⟩
  cases c
  · obtain ⟨hj,hxy⟩:=(D.down_neighbors i j y).mp hxy
    rcases hxy with ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨_,rfl,ho⟩
    · exact (hy hx).elim
    · exact (hy hx).elim
    · have hj' : j+1=N := by change ¬j+1<N at hy; have hx' : j<N := hx; omega
      have ho' : (D.tile (i,N)).Occupied 0 := by
        have he := D.vertical i j (by omega)
        simpa only [hj'] using he.mp ho
      have hj'' : j=N-1 := by omega
      rcases (ht i).mp ho' with rfl | rfl
      · exact Or.inr (hj'' ▸ hvx')
      · exact Or.inl (hj'' ▸ hvx')
  · obtain ⟨hj,hxy⟩:=(D.up_neighbors i j y).mp hxy
    rcases hxy with ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨_,rfl,_⟩
    · exact (hy hx).elim
    · exact (hy hx).elim
    · have hh : (down i (j-1)).2.1<N := by change j-1<N; have hx' : j<N := hx; omega
      exact (hy hh).elim

end HoneycombAssignment
end

 

 

noncomputable section
open scoped Classical
open Diagram

namespace Diagram.ColumnChain
variable {n : ℕ}

lemma read_map (ts : List (Configuration n)) (k : ℕ) (i : Fin n) :
    read ts k i=((ts.map (fun t=>t i))[k]?).getD Tile.vacant := by
  simp only [read,List.getElem?_map]
  cases ts[k]? <;> rfl

lemma north_shape_read (ts : List (Configuration (n+1))) (k l : ℕ)
    (h : ts.map (fun t=>t (Fin.last n))=
      List.replicate k Tile.diagonal₁ ++ Tile.vertical₀::List.replicate l Tile.vacant)
    (j : ℕ) : read ts j (Fin.last n)=
      if j<k then Tile.diagonal₁ else if j=k then Tile.vertical₀ else Tile.vacant := by
  rw [read_map,h,List.getElem?_append,List.length_replicate]
  split_ifs with hj hjk
  · rw [List.getElem?_replicate,ite_eq_left hj]; rfl
  · subst j
    simp
  · have hpos : 0<j-k := by omega
    have he : j-k=(j-k-1)+1 := by omega
    rw [he,List.getElem?_cons_succ,List.getElem?_replicate]
    split <;> rfl

end Diagram.ColumnChain

namespace SewnRectangle
variable {n : ℕ}

lemma tile_nonvacant_bounds (l r : List (Configuration n)) (q : Cell)
    (h : tile l r q≠.vacant) :
    -(l.length:ℤ)≤q.1 ∧ q.1<(r.length:ℤ) ∧ q.2<n := by
  rcases q with ⟨i,j⟩
  have hj : j<n := by
    by_contra hn
    exact h (tile_outside l r i j (by omega))
  refine ⟨?_,?_,hj⟩
  · by_contra hi
    have hn : i<0 := by omega
    have hk : l.length≤(-i-1).toNat := by omega
    simp only [tile,hj,dite_eq_left,hn,ite_true,ColumnChain.read_ge l _ hk] at h
    exact h rfl
  · by_contra hi
    have hn : ¬i<0 := by omega
    have hk : r.length ≤ i.toNat := by omega
    simp only [tile,hj,dite_eq_left,hn,ite_false,ColumnChain.read_ge r _ hk] at h
    exact h rfl

lemma finite_support (D : HoneycombAssignment n) (l r : List (Configuration n))
    (ht : D.tile=tile l r) : D.graph.support.Finite := by
  let F : Set Triangle := Set.Ico (-(l.length:ℤ)) (r.length:ℤ) ×ˢ
    (Set.Iio n ×ˢ (Set.univ : Set Bool))
  have hF : F.Finite := (Set.finite_Ico _ _).prod ((Set.finite_Iio n).prod (Set.toFinite _))
  apply hF.subset
  rintro ⟨i,j,b⟩ hv
  have hv' : D.tile (i,j)≠.vacant := by
    apply (Tile.nonvacant_iff_used _).mpr
    cases b
    · exact Or.inr ((D.down_support_iff i j).mp hv)
    · exact Or.inl ((D.up_support_iff i j).mp hv)
  rw [ht] at hv'
  obtain ⟨hi,hj,hk⟩:=tile_nonvacant_bounds l r (i,j) hv'
  exact ⟨⟨hi,hj⟩,hk,Set.mem_univ _⟩

lemma restrict_finite_support (D : HoneycombAssignment (n+1))
    (l r : List (Configuration (n+1))) (ht : D.tile=tile l r) :
    (D.restrict n (by omega)).graph.support.Finite := by
  apply (finite_support D l r ht).subset
  rintro v ⟨w,hw⟩
  exact ⟨w,((D.restrict_adj n (by omega) v w).mp hw).2.2⟩

lemma north_south_occupied (l r : List (Configuration (n+1))) (kl ll kr lr : ℕ)
    (hl : l.map (fun t=>t (Fin.last n))=
      List.replicate kl Tile.diagonal₁ ++ Tile.vertical₀::List.replicate ll Tile.vacant)
    (hr : r.map (fun t=>t (Fin.last n))=
      List.replicate kr Tile.diagonal₁ ++ Tile.vertical₀::List.replicate lr Tile.vacant)
    (i : ℤ) : (tile l r (i,n)).Occupied 0 ↔ i= -1-(kl:ℤ) ∨ i=(kr:ℤ) := by
  rcases split_column i with ⟨k,rfl⟩|⟨k,rfl⟩
  · rw [show tile l r (-1-(k:ℤ),n)=ColumnChain.read l k (Fin.last n) from tile_left l r k (Fin.last n),ColumnChain.north_shape_read l kl ll hl k]
    split_ifs with hk he
    · have hc : ¬-1-(k:ℤ)= -1-(kl:ℤ) := by omega
      have hc' : ¬-1-(k:ℤ)=(kr:ℤ) := by omega
      simp only [hc,hc',false_or]
      decide
    · subst k
      simp only [true_or]
      decide
    · have hc : ¬-1-(k:ℤ)= -1-(kl:ℤ) := by omega
      have hc' : ¬-1-(k:ℤ)=(kr:ℤ) := by omega
      simp only [hc,hc',false_or]
      decide
  · rw [show tile l r ((k:ℤ),n)=(ColumnChain.read r k (Fin.last n)).horizontal from tile_right l r k (Fin.last n),Tile.horizontal_occupied_zero,
      ColumnChain.north_shape_read r kr lr hr k]
    split_ifs with hk he
    · have hc : ¬(k:ℤ)= -1-(kl:ℤ) := by omega
      have hc' : ¬(k:ℤ)=(kr:ℤ) := by omega
      simp only [hc,hc',false_or]
      decide
    · subst k
      simp only [or_true]
      decide
    · have hc : ¬(k:ℤ)= -1-(kl:ℤ) := by omega
      have hc' : ¬(k:ℤ)=(kr:ℤ) := by omega
      simp only [hc,hc',false_or]
      decide

end SewnRectangle
end
end CriticalStrip

end OAI
