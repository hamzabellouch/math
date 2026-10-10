import Mathlib
import OAI.Combinatorics.StripMass.FiniteEnds

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped Classical
open Diagram

namespace Diagram.Tile

 
def turn : Tile → Tile
  | .vertical₀ => .vertical₁
  | .vertical₁ => .vertical₀
  | .cap => .cup
  | .cup => .cap
  | t => t

@[simp] lemma turn_turn (t : Tile) : t.turn.turn=t := by cases t <;> rfl
@[simp] lemma turn_vacant : Tile.vacant.turn=.vacant := rfl
@[simp] lemma turn_physical (t : Tile) : t.turn≠.verticalPair ↔ t≠.verticalPair := by
  cases t <;> decide
@[simp] lemma turn_occupied_zero (t : Tile) : t.turn.Occupied 0 ↔ t.Occupied 3 := by
  revert t; decide
@[simp] lemma turn_occupied_one (t : Tile) : t.turn.Occupied 1 ↔ t.Occupied 2 := by
  revert t; decide
@[simp] lemma turn_occupied_two (t : Tile) : t.turn.Occupied 2 ↔ t.Occupied 1 := by
  revert t; decide
@[simp] lemma turn_occupied_three (t : Tile) : t.turn.Occupied 3 ↔ t.Occupied 0 := by
  revert t; decide
@[simp] lemma turn_middle (t : Tile) : t.turn.middle=t.middle := by cases t <;> rfl
@[simp] lemma turn_weight (w : Weights ℝ) (t : Tile) : w.tile t.turn=w.tile t := by
  cases t <;> rfl

end Diagram.Tile

 

def turnTriangle (N : ℕ) (b : ℤ) (v : Triangle) : Triangle :=
  (b-v.1,N-1-v.2.1,!v.2.2)

lemma turnTriangle_in_strip (N : ℕ) (b : ℤ) {v : Triangle} (hv : v.2.1<N) :
    (turnTriangle N b v).2.1<N := by dsimp [turnTriangle]; omega

lemma turnTriangle_turnTriangle (N : ℕ) (b : ℤ) {v : Triangle} (hv : v.2.1<N) :
    turnTriangle N b (turnTriangle N b v)=v := by
  rcases v with ⟨i,j,c⟩
  simp only [turnTriangle,Bool.not_not]
  have hj : N-1-(N-1-j)=j := by dsimp at hv; omega
  simp [hj]

lemma turnTriangle_adjacent {N : ℕ} (b : ℤ) {v w : Triangle}
    (hv : v.2.1<N) (hw : w.2.1<N) (h : adjacent v w) :
    adjacent (turnTriangle N b v) (turnTriangle N b w) := by
  rcases v with ⟨i,j,c⟩; rcases w with ⟨k,l,d⟩
  cases c <;> cases d <;>
    simp only [adjacent,upDownAdjacent,turnTriangle,Bool.not_false,Bool.not_true,
      Bool.false_eq_true,Bool.true_eq_false,false_and,and_false,false_or,or_false,
      true_and] at h ⊢
  · rcases h with ⟨hjl,hik|hik⟩|⟨hjl,hik⟩ <;> omega
  · rcases h with ⟨hjl,hik|hik⟩|⟨hjl,hik⟩ <;> omega

lemma PathBetween.turn {N : ℕ} {a b : Triangle} {p : List Triangle}
    (hp : PathBetween N a b p) (k : ℤ) :
    PathBetween N (turnTriangle N k a) (turnTriangle N k b) (p.map (turnTriangle N k)) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [List.head?_map,hp.1]; rfl
  · rw [List.getLast?_map,hp.2.1]; rfl
  · apply hp.2.2.1.map_on
    intro v hv w hw h
    have hh:=congrArg (turnTriangle N k) h
    simpa only [turnTriangle_turnTriangle N k (hp.2.2.2.2 _ hv),
      turnTriangle_turnTriangle N k (hp.2.2.2.2 _ hw)] using hh
  · apply (List.isChain_map _).mpr
    apply List.isChain_iff_getElem.mpr
    intro i hi
    exact turnTriangle_adjacent k (hp.2.2.2.2 _ (List.getElem_mem (by omega)))
      (hp.2.2.2.2 _ (List.getElem_mem hi)) (List.isChain_iff_getElem.mp hp.2.2.2.1 i hi)
  · intro v hv
    obtain ⟨w,hw,rfl⟩:=List.mem_map.mp hv
    exact turnTriangle_in_strip N k (hp.2.2.2.2 _ hw)

namespace HoneycombAssignment
variable {N : ℕ}

 
def turn (D : HoneycombAssignment N) (b : ℤ) : HoneycombAssignment N where
  tile q := if q.2<N then (D.tile (b-q.1,N-1-q.2)).turn else .vacant
  physical q := by
    split
    · exact (Tile.turn_physical _).mpr (D.physical _)
    · decide
  outside i j hj := ite_eq_right (by omega)
  horizontal i j := by
    by_cases hj : j<N
    · simp only [hj,ite_true,Tile.turn_occupied_two,Tile.turn_occupied_one]
      have hh:=D.horizontal (b-(i+1)) (N-1-j)
      simpa only [show b-(i+1)+1=b-i by omega] using hh.symm
    · simp only [hj,ite_false,Tile.vacant_not_occupied]
  vertical i j hj := by
    have hj' : j<N := by omega
    have hh:=D.vertical (b-i) (N-1-(j+1)) (by omega)
    simp only [hj,hj',ite_true,Tile.turn_occupied_zero,Tile.turn_occupied_three]
    simpa only [show N-1-(j+1)+1=N-1-j by omega] using hh.symm

lemma turn_tile (D : HoneycombAssignment N) (b : ℤ) (i : ℤ) (j : ℕ) (hj : j<N) :
    (D.turn b).tile (i,j)=(D.tile (b-i,N-1-j)).turn := by simp [turn,hj]

lemma turn_turn (D : HoneycombAssignment N) (b : ℤ) : (D.turn b).turn b=D := by
  apply ext
  funext ⟨i,j⟩
  by_cases hj : j<N
  · have hj' : N-1-j<N := by omega
    rw [(D.turn b).turn_tile b i j hj,D.turn_tile b (b-i) (N-1-j) hj',
      Tile.turn_turn,show b-(b-i)=i by omega,show N-1-(N-1-j)=j by omega]
  · rw [(D.turn b).turn b |>.outside i j (by omega),D.outside i j (by omega)]

lemma turn_up_adj (D : HoneycombAssignment N) (b i : ℤ) (j : ℕ) (w : Triangle)
    (hj : j<N) (hw : w.2.1<N) :
    (D.turn b).graph.Adj (up i j) w ↔
      D.graph.Adj (turnTriangle N b (up i j)) (turnTriangle N b w) := by
  rcases w with ⟨k,l,c⟩
  rw [(D.turn b).up_neighbors]
  change (_ ∧ _) ↔ D.graph.Adj (down (b-i) (N-1-j)) (turnTriangle N b (k,l,c))
  rw [D.down_neighbors,D.turn_tile b i j hj,Tile.turn_middle,Tile.turn_occupied_one,
    Tile.turn_occupied_zero]
  have hj' : N-1-j<N := by omega
  simp only [hj,hj',true_and,up,down,turnTriangle,Prod.mk.injEq]
  have hl : l<N := hw
  cases c <;> simp only [Bool.not_false,Bool.not_true,Bool.false_eq_true,Bool.true_eq_false,
    and_true,and_false,false_and,or_false]
  apply or_congr
  · apply and_congr_left
    intro _
    omega
  · apply or_congr
    · apply and_congr_left
      intro _
      omega
    · simp only [←and_assoc]
      apply and_congr_left
      intro _
      omega

lemma turn_adj (D : HoneycombAssignment N) (b : ℤ) {v w : Triangle}
    (hv : v.2.1<N) (hw : w.2.1<N) :
    (D.turn b).graph.Adj v w ↔ D.graph.Adj (turnTriangle N b v) (turnTriangle N b w) := by
  rcases v with ⟨i,j,c⟩
  cases c
  · rcases w with ⟨k,l,d⟩
    cases d
    · constructor
      · intro h
        have hh:=(tileGraph_allowed N (D.turn b).tile h).1
        simp [adjacent,upDownAdjacent] at hh
      · intro h
        have hh:=(tileGraph_allowed N D.tile h).1
        simp [turnTriangle,adjacent,upDownAdjacent] at hh
    · exact (show (D.turn b).graph.Adj (down i j) (up k l) ↔
          (D.turn b).graph.Adj (up k l) (down i j) from
          ⟨(D.turn b).graph.symm.symm _ _,(D.turn b).graph.symm.symm _ _⟩).trans
        ((D.turn_up_adj b k l (down i j) hw hv).trans
          ⟨D.graph.symm.symm _ _,D.graph.symm.symm _ _⟩)
  · exact D.turn_up_adj b i j w hv hw

lemma turn_edge (D : HoneycombAssignment N) (b : ℤ) {v w : Triangle}
    (h : D.graph.Adj v w) :
    (D.turn b).graph.Adj (turnTriangle N b v) (turnTriangle N b w) := by
  have hh:=tileGraph_allowed N D.tile h
  apply (D.turn_adj b (turnTriangle_in_strip N b hh.2.1)
    (turnTriangle_in_strip N b hh.2.2)).mpr
  simpa only [turnTriangle_turnTriangle N b hh.2.1,
    turnTriangle_turnTriangle N b hh.2.2] using h

lemma turn_reach (D : HoneycombAssignment N) (b : ℤ) {v w : Triangle}
    (h : Relation.ReflTransGen D.graph.Adj v w) :
    Relation.ReflTransGen (D.turn b).graph.Adj (turnTriangle N b v) (turnTriangle N b w) :=
  Graph.map_reach (turnTriangle N b) (fun _ _ e=>.single (D.turn_edge b e)) h

lemma turn_drains (D : HoneycombAssignment N) (b : ℤ) {root : Triangle}
    (h : Graph.DrainsAt D.graph.Adj root) :
    Graph.DrainsAt (D.turn b).graph.Adj (turnTriangle N b root) := by
  intro v w hvw
  have hh:=tileGraph_allowed N (D.turn b).tile hvw
  have e:=(D.turn_adj b hh.2.1 hh.2.2).mp hvw
  simpa only [turnTriangle_turnTriangle N b hh.2.1] using
    D.turn_reach b (h _ _ e)

end HoneycombAssignment

 

structure TopArchConfiguration (N : ℕ) (a b : ℤ) extends HoneycombAssignment N where
  bottom : ∀i, ¬(tile (i,0)).Occupied 0
  top : ∀i, (tile (i,N-1)).Occupied 3 ↔ i=a ∨ i=b
  drains : Graph.DrainsAt toHoneycombAssignment.graph.Adj (down b (N-1))

namespace TopArchConfiguration
variable {N : ℕ} {a b : ℤ}

@[ext] lemma ext {D E : TopArchConfiguration N a b}
    (h : D.toHoneycombAssignment=E.toHoneycombAssignment) : D=E := by
  cases D; cases E; cases h; rfl

 
def toArch (D : TopArchConfiguration N a b) (hN : 1≤N) :
    HoneycombConfiguration N (.bottom (b-a)) where
  toHoneycombAssignment := D.toHoneycombAssignment.turn b
  bottom i := by
    rw [D.toHoneycombAssignment.turn_tile b i 0 (by omega),Tile.turn_occupied_zero]
    simp only [Nat.sub_zero,D.top,BoundaryPort.bottom.injEq]
    omega
  top i := by
    rw [D.toHoneycombAssignment.turn_tile b i (N-1) (by omega),
      show N-1-(N-1)=0 from Nat.sub_self _,Tile.turn_occupied_three]
    simp only [D.bottom,false_iff]
    exact BoundaryPort.noConfusion
  drains := by
    have hh:=D.toHoneycombAssignment.turn_drains b D.drains
    simpa only [Graph.DrainsAt,turnTriangle,down,up,sub_self,Nat.sub_self,Bool.not_false] using hh

def ofArch (D : HoneycombConfiguration N (.bottom (b-a))) (hN : 1≤N) :
    TopArchConfiguration N a b where
  toHoneycombAssignment := D.toHoneycombAssignment.turn b
  bottom i := by
    rw [D.toHoneycombAssignment.turn_tile b i 0 (by omega),Tile.turn_occupied_zero,Nat.sub_zero,
      D.top]
    exact BoundaryPort.noConfusion
  top i := by
    rw [D.toHoneycombAssignment.turn_tile b i (N-1) (by omega),
      Nat.sub_self,Tile.turn_occupied_three,D.bottom]
    simp only [BoundaryPort.bottom.injEq]
    omega
  drains := by
    have hh:=D.toHoneycombAssignment.turn_drains b D.drains
    simpa only [turnTriangle,down,up,sub_zero,Nat.sub_zero,Bool.not_true] using hh

@[simp] lemma ofArch_toArch (D : TopArchConfiguration N a b) (hN : 1≤N) :
    ofArch (D.toArch hN) hN=D := by
  apply ext
  exact D.toHoneycombAssignment.turn_turn b

@[simp] lemma toArch_ofArch (D : HoneycombConfiguration N (.bottom (b-a))) (hN : 1≤N) :
    (ofArch D hN).toArch hN=D := by
  apply HoneycombConfiguration.ext
  exact D.toHoneycombAssignment.turn_turn b

def equivArch (N : ℕ) (a b : ℤ) (hN : 1≤N) :
    TopArchConfiguration N a b ≃ HoneycombConfiguration N (.bottom (b-a)) where
  toFun D := D.toArch hN
  invFun D := ofArch D hN
  left_inv D := ofArch_toArch D hN
  right_inv D := toArch_ofArch D hN

end TopArchConfiguration
end
end CriticalStrip

 

 

namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

namespace PaddedColumn
variable {n : ℕ}

 

theorem runs_exists (hn : 0<n) (ts : List (Configuration n))
    (hc : ColumnChain.Compatible (empty n) ts)
    (hd : Graph.DrainsBoundary (wiring ts) boundary) :
    ∃ q, ColumnChain.Runs (empty n) ts q := by
  induction ts with
  | nil => exact ⟨empty n,rfl⟩
  | cons t ts ih =>
    obtain ⟨hc,ht⟩:=hc
    have hd' := (stepEquivalence t ts).symm.drains hd
    have hl := Graph.glued_drains_local (wiring ts) (BareColumn t) boundary
      (fun i=>(i,1)) (active ts) (fun i=>(i,2)) hd'
    obtain ⟨p,hp⟩:=ih hc hl
    have hg:=runs_realizes ts p hp
    have he : active ts=p.Occupied := by
      funext i
      exact propext ((ColumnChain.support_empty_read ts i).symm.trans
        (by rw [(ColumnChain.runs_sound _ _ _ hp).2.2]))
    rw [he] at hd'
    have ht' : ColumnCompatible p.Occupied t := by
      simpa only [(ColumnChain.runs_sound _ _ _ hp).2.2] using ht
    have hdr := (hg.substitute_drains_iff (BareColumn t) (fun i=>(i,1)) (fun i=>(i,2))).mp hd'
    obtain ⟨q,hq⟩:=realizes_exists_of_drains hn p t ht' ((ColumnSew.equivalence p t).drains hdr)
    exact ⟨q,p,hp,hq⟩

lemma runs_iff (hn : 0<n) (ts : List (Configuration n)) (q : Pairing n) :
    ColumnChain.Runs (empty n) ts q ↔
      ColumnChain.Compatible (empty n) ts ∧ GraphRealizes (wiring ts) boundary q := by
  constructor
  · exact fun h=>⟨(ColumnChain.runs_sound _ _ _ h).1,runs_realizes ts q h⟩
  · rintro ⟨hc,hg⟩
    obtain ⟨p,hp⟩:=runs_exists hn ts hc hg.drainsBoundary
    exact (runs_realizes ts p hp).unique hg ▸ hp

end PaddedColumn
end
end CriticalStrip.Diagram

 

 

namespace CriticalStrip
noncomputable section
open scoped Classical
open Diagram

namespace NorthExtension

 
def tile (a b i : ℤ) : Tile :=
  if i=a then .vertical₀ else if i=b then .cap else
    if a< i ∧ i<b then .diagonal₁ else .vacant

lemma physical (a b i : ℤ) : tile a b i≠.verticalPair := by
  unfold tile
  split_ifs <;> decide

lemma south (a b i : ℤ) (_h : a<b) :
    (tile a b i).Occupied 0 ↔ i=a ∨ i=b := by
  unfold tile
  split_ifs with ha hb hi
  · simp only [ha,true_or]; decide
  · simp only [hb,or_true]; decide
  · simp only [ha,hb,false_or]; decide
  · simp only [ha,hb,false_or]; decide

lemma west (a b i : ℤ) (h : a<b) :
    (tile a b i).Occupied 1 ↔ a< i ∧ i≤b := by
  unfold tile
  split_ifs with ha hb hi
  · subst i
    have hh : ¬a<a := by omega
    simp only [hh,false_and]
    decide
  · subst i
    simp only [h,le_refl,and_self]
    decide
  · have hb' : i≤b := le_of_lt hi.2
    simp only [hi.1,hb',and_self]
    decide
  · have hi' : ¬(a< i ∧ i≤b) := by omega
    simp only [hi']
    decide

lemma east (a b i : ℤ) (h : a<b) :
    (tile a b i).Occupied 2 ↔ a≤ i ∧ i<b := by
  unfold tile
  split_ifs with ha hb hi
  · subst i
    simp only [h,le_refl,and_self]
    decide
  · subst i
    have hh : ¬b<b := by omega
    simp only [hh,and_false]
    decide
  · have ha' : a≤ i := le_of_lt hi.1
    simp only [ha',hi.2,and_self]
    decide
  · have hi' : ¬(a≤ i ∧ i<b) := by omega
    simp only [hi']
    decide

lemma north (a b i : ℤ) : ¬(tile a b i).Occupied 3 := by
  unfold tile
  split_ifs <;> decide

lemma middle (a b i : ℤ) (h : a<b) :
    (tile a b i).middle ↔ a≤ i ∧ i<b := by
  unfold tile
  split_ifs with ha hb hi
  · subst i
    simp only [h,le_refl,and_self]; decide
  · subst i
    have hh : ¬b<b := by omega
    simp only [hh,and_false]; decide
  · have ha' : a≤ i := le_of_lt hi.1
    simp only [ha',hi.2,and_self]; decide
  · have hi' : ¬(a≤ i ∧ i<b) := by omega
    simp only [hi']; decide

lemma nonvacant (a b i : ℤ) (h : a<b) : tile a b i≠.vacant ↔ a≤ i ∧ i≤b := by
  unfold tile
  split_ifs <;> simp_all <;> omega

end NorthExtension

namespace TopArchConfiguration
variable {N : ℕ} {a b : ℤ}

 

def extend (D : TopArchConfiguration N a b) (hN : 1≤N) (hab : a<b) :
    HoneycombAssignment (N+1) where
  tile q := if q.2=N then NorthExtension.tile a b q.1 else D.tile q
  physical q := by split; exact NorthExtension.physical _ _ _; exact D.physical q
  outside i j hj := by
    rw [ite_eq_right (by omega)]
    exact D.outside i j (by omega)
  horizontal i j := by
    by_cases hj : j=N
    · simp only [hj,ite_true,NorthExtension.east a b i hab,
        NorthExtension.west a b (i+1) hab]
      omega
    · simpa only [hj,ite_false] using D.horizontal i j
  vertical i j hj := by
    have hn : j<N := by omega
    have hn' : j≠N := by omega
    simp only [hn',ite_false]
    by_cases he : j+1=N
    · rw [ite_eq_left he,NorthExtension.south _ _ _ hab]
      have he' : j=N-1 := by omega
      exact he' ▸ D.top i
    · rw [ite_eq_right he]
      exact D.vertical i j (by omega)

@[simp] lemma extend_last (D : TopArchConfiguration N a b) (hN : 1≤N) (hab : a<b) (i : ℤ) :
    (D.extend hN hab).tile (i,N)=NorthExtension.tile a b i := by simp [extend]

lemma extend_base (D : TopArchConfiguration N a b) (hN : 1≤N) (hab : a<b)
    (i : ℤ) (j : ℕ) (hj : j<N) : (D.extend hN hab).tile (i,j)=D.tile (i,j) :=
  ite_eq_right (by omega)

@[simp] lemma extend_restrict (D : TopArchConfiguration N a b) (hN : 1≤N) (hab : a<b) :
    (D.extend hN hab).restrict N (by omega)=D.toHoneycombAssignment := by
  apply HoneycombAssignment.ext
  funext ⟨i,j⟩
  by_cases hj : j<N
  · rw [HoneycombAssignment.restrict_tile _ _ _ i j hj,D.extend_base hN hab i j hj]
  · rw [HoneycombAssignment.outside _ i j (by omega),D.outside i j (by omega)]

lemma extend_base_edge (D : TopArchConfiguration N a b) (hN : 1≤N) (hab : a<b)
    {v w : Triangle} (h : D.toHoneycombAssignment.graph.Adj v w) :
    (D.extend hN hab).graph.Adj v w := by
  have hh:=tileGraph_allowed N D.tile h
  have he:= (D.extend hN hab).restrict_adj N (by omega) v w
  rw [D.extend_restrict hN hab] at he
  exact (he.mp h).2.2

lemma extend_up_edge (D : TopArchConfiguration N a b) (hN : 1≤N) (hab : a<b)
    {i : ℤ} (ha : a≤ i) (hb : i<b) :
    (D.extend hN hab).graph.Adj (up i N) (down i N) := by
  apply (HoneycombAssignment.up_neighbors _ _ _ _).mpr
  refine ⟨by omega,Or.inl ⟨rfl,?_⟩⟩
  rw [D.extend_last hN hab,NorthExtension.middle _ _ _ hab]
  exact ⟨ha,hb⟩

lemma extend_next_edge (D : TopArchConfiguration N a b) (hN : 1≤N) (hab : a<b)
    {i : ℤ} (ha : a≤ i) (hb : i<b) :
    (D.extend hN hab).graph.Adj (down i N) (up (i+1) N) := by
  apply (HoneycombAssignment.down_neighbors _ _ _ _).mpr
  refine ⟨by omega,Or.inr (Or.inl ⟨rfl,?_⟩)⟩
  rw [D.extend_last hN hab,NorthExtension.east _ _ _ hab]
  exact ⟨ha,hb⟩

lemma extend_up_reach (D : TopArchConfiguration N a b) (hN : 1≤N) (hab : a<b)
    {i : ℤ} (ha : a≤ i) (hb : i≤b) :
    Relation.ReflTransGen (D.extend hN hab).graph.Adj (up i N) (up b N) := by
  generalize he : (b-i).toNat=k
  induction k using Nat.strong_induction_on generalizing i with
  | h k ih =>
    by_cases hi : i=b
    · subst i; exact .refl
    · have hlt : i<b := by omega
      have he' : (b-(i+1)).toNat<k := by omega
      exact (Relation.ReflTransGen.single (D.extend_up_edge hN hab ha hlt)).trans
        ((Relation.ReflTransGen.single (D.extend_next_edge hN hab ha hlt)).trans
          (ih _ he' (by omega) (by omega) rfl))

lemma extend_enter (D : TopArchConfiguration N a b) (hN : 1≤N) (hab : a<b) :
    (D.extend hN hab).graph.Adj (down b (N-1)) (up b N) := by
  apply (HoneycombAssignment.down_neighbors _ _ _ _).mpr
  refine ⟨by omega,Or.inr (Or.inr ⟨by omega,?_,?_⟩)⟩
  · congr 1; omega
  · rw [D.extend_base hN hab b (N-1) (by omega)]
    exact (D.top b).mpr (Or.inr rfl)

lemma extend_drains_right (D : TopArchConfiguration N a b) (hN : 1≤N) (hab : a<b) :
    Graph.DrainsAt (D.extend hN hab).graph.Adj (up b N) := by
  intro v w hvw
  have hv:=(tileGraph_allowed (N+1) (D.extend hN hab).tile hvw).2.1
  by_cases hvN : v.2.1<N
  · have hu : Graph.Used D.toHoneycombAssignment.graph.Adj v := by
      rcases v with ⟨i,j,c⟩
      cases c
      · apply (D.toHoneycombAssignment.down_support_iff i j).mpr
        rw [←D.extend_base hN hab i j hvN]
        exact (HoneycombAssignment.down_support_iff _ i j).mp ⟨w,hvw⟩
      · apply (D.toHoneycombAssignment.up_support_iff i j).mpr
        rw [←D.extend_base hN hab i j hvN]
        exact (HoneycombAssignment.up_support_iff _ i j).mp ⟨w,hvw⟩
    obtain ⟨x,hx⟩:=hu
    exact (Relation.ReflTransGen.mono (fun _ _=>D.extend_base_edge hN hab) _ _
      (D.drains _ _ hx)).tail (D.extend_enter hN hab)
  · have hvN' : v.2.1=N := by omega
    rcases v with ⟨i,j,c⟩
    dsimp at hvN'; subst j
    cases c
    · obtain ⟨_,hh⟩:=(HoneycombAssignment.down_neighbors _ _ _ _).mp hvw
      rw [D.extend_last hN hab,NorthExtension.middle _ _ _ hab,
        NorthExtension.east _ _ _ hab] at hh
      have hi : a≤ i ∧ i<b := by
        rcases hh with ⟨_,h⟩|⟨_,h⟩|⟨h,_,_⟩
        · exact h
        · exact h
        · omega
      exact (Relation.ReflTransGen.single (D.extend_next_edge hN hab hi.1 hi.2)).trans
        (D.extend_up_reach hN hab (by omega) (by omega))
    · obtain ⟨_,hh⟩:=(HoneycombAssignment.up_neighbors _ _ _ _).mp hvw
      rw [D.extend_last hN hab,NorthExtension.middle _ _ _ hab,
        NorthExtension.west _ _ _ hab,NorthExtension.south _ _ _ hab] at hh
      have hi : a≤ i ∧ i≤b := by
        rcases hh with ⟨_,h⟩|⟨_,h⟩|⟨_,_,h|h⟩ <;> omega
      exact D.extend_up_reach hN hab hi.1 hi.2

lemma extend_drains (D : TopArchConfiguration N a b) (hN : 1≤N) (hab : a<b)
    (ha : a≤0) (hb : 0≤b) :
    Graph.DrainsAt (D.extend hN hab).graph.Adj (up 0 N) := by
  apply (D.extend_drains_right hN hab).mono_root
  have := (D.extend hN hab).graph.symm
  exact symm (D.extend_up_reach hN hab ha hb)

end TopArchConfiguration
end
end CriticalStrip

end OAI
