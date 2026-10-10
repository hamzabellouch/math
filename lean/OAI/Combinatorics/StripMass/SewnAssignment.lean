import Mathlib
import OAI.Combinatorics.StripMass.ReversedConvergence

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped Classical
open Diagram

namespace Diagram.Tile
@[simp] lemma horizontal_occupied_zero (t : Tile) : t.horizontal.Occupied 0 ↔ t.Occupied 0 := by
  revert t; decide
@[simp] lemma horizontal_occupied_one (t : Tile) : t.horizontal.Occupied 1 ↔ t.Occupied 2 := by
  simpa [horizontalPort] using horizontal_occupied t 2
@[simp] lemma horizontal_occupied_two (t : Tile) : t.horizontal.Occupied 2 ↔ t.Occupied 1 := by
  simpa [horizontalPort] using horizontal_occupied t 1
@[simp] lemma horizontal_occupied_three (t : Tile) : t.horizontal.Occupied 3 ↔ t.Occupied 3 := by
  revert t; decide
end Diagram.Tile

namespace SewnRectangle
variable {n : ℕ}

 

def tile (l r : List (Configuration n)) (v : Cell) : Tile :=
  if hj : v.2<n then
    if v.1<0 then ColumnChain.read l (-v.1-1).toNat ⟨v.2,hj⟩
    else (ColumnChain.read r v.1.toNat ⟨v.2,hj⟩).horizontal
  else .vacant

@[simp] lemma tile_left (l r : List (Configuration n)) (k : ℕ) (j : Fin n) :
    tile l r (-1-(k:ℤ),j.val)=ColumnChain.read l k j := by
  have hk : -1-(k:ℤ)<0 := by omega
  have he : -(-1-(k:ℤ))-1=(k:ℤ) := by omega
  simp only [tile,j.isLt,dite_eq_left,hk,ite_true,he,Int.toNat_natCast]
@[simp] lemma tile_right (l r : List (Configuration n)) (k : ℕ) (j : Fin n) :
    tile l r ((k:ℤ),j.val)=(ColumnChain.read r k j).horizontal := by
  simp [tile,j.isLt,show ¬(k:ℤ)<0 by omega]
@[simp] lemma tile_outside (l r : List (Configuration n)) (i : ℤ) (j : ℕ) (hj : n≤j) :
    tile l r (i,j)=.vacant := by simp [tile,show ¬j<n by omega]

lemma split_column (i : ℤ) : (∃ k : ℕ,i= -1-(k:ℤ)) ∨ ∃k : ℕ,i=(k:ℤ) := by
  by_cases hi : i<0
  · left; refine ⟨(-i-1).toNat,?_⟩
    rw [Int.toNat_of_nonneg (by omega)]; omega
  · right; exact ⟨i.toNat,(Int.toNat_of_nonneg (by omega)).symm⟩

lemma physical (l r : List (Configuration n))
    (hl : ∀k j, ColumnChain.read l k j≠.verticalPair)
    (hr : ∀k j, ColumnChain.read r k j≠.capCup) (v : Cell) : tile l r v≠.verticalPair := by
  rcases v with ⟨i,j⟩
  by_cases hj : j<n
  · rcases split_column i with ⟨k,rfl⟩ | ⟨k,rfl⟩
    · exact (tile_left l r k ⟨j,hj⟩) ▸ hl k ⟨j,hj⟩
    · rw [tile_right l r k ⟨j,hj⟩]
      exact (Tile.physical_horizontal _).mpr (hr k ⟨j,hj⟩)
  · rw [tile_outside l r i j (by omega)]; decide

lemma horizontal (l r : List (Configuration n))
    (hl : ColumnChain.LocallyCompatible l) (hr : ColumnChain.LocallyCompatible r)
    (hcut : ∀j, (ColumnChain.read l 0 j).Occupied 2 ↔ (ColumnChain.read r 0 j).Occupied 2)
    (i : ℤ) (j : ℕ) : (tile l r (i,j)).Occupied 2 ↔ (tile l r (i+1,j)).Occupied 1 := by
  by_cases hj : j<n
  · let j' : Fin n := ⟨j,hj⟩
    rcases split_column i with ⟨k,rfl⟩ | ⟨k,rfl⟩
    · cases k with
      | zero =>
        change (tile l r (-1-(0:ℕ),j'.val)).Occupied 2 ↔ (tile l r ((0:ℕ),j'.val)).Occupied 1
        rw [tile_left l r 0 j',tile_right l r 0 j',Tile.horizontal_occupied_one]
        exact hcut j'
      | succ k =>
        have he : -1-((k+1:ℕ):ℤ)+1 = -1-(k:ℤ) := by omega
        rw [tile_left l r (k+1) j',he,tile_left l r k j']
        exact hl.horizontal k j'
    · rw [tile_right l r k j',show (k:ℤ)+1=((k+1:ℕ):ℤ) by omega,tile_right l r (k+1) j',
        Tile.horizontal_occupied_two,Tile.horizontal_occupied_one]
      exact (hr.horizontal k j').symm
  · rw [tile_outside l r i j (by omega),tile_outside l r (i+1) j (by omega)]
    exact ⟨fun h=>(Tile.vacant_not_occupied 2 h).elim,fun h=>(Tile.vacant_not_occupied 1 h).elim⟩

lemma vertical (l r : List (Configuration n))
    (hl : ColumnChain.LocallyCompatible l) (hr : ColumnChain.LocallyCompatible r)
    (i : ℤ) (j : ℕ) (hj : j+1<n) :
    (tile l r (i,j)).Occupied 3 ↔ (tile l r (i,j+1)).Occupied 0 := by
  rcases split_column i with ⟨k,rfl⟩ | ⟨k,rfl⟩
  · rw [tile_left l r k ⟨j,by omega⟩,tile_left l r k ⟨j+1,hj⟩]
    exact hl.vertical k _ _ rfl
  · rw [tile_right l r k ⟨j,by omega⟩,tile_right l r k ⟨j+1,hj⟩,
      Tile.horizontal_occupied_three,Tile.horizontal_occupied_zero]
    exact hr.vertical k _ _ rfl

 

def assignment (l r : List (Configuration n))
    (hl : ColumnChain.LocallyCompatible l) (hr : ColumnChain.LocallyCompatible r)
    (hcut : ∀j, (ColumnChain.read l 0 j).Occupied 2 ↔ (ColumnChain.read r 0 j).Occupied 2)
    (hp : ∀k j, ColumnChain.read l k j≠.verticalPair)
    (hq : ∀k j, ColumnChain.read r k j≠.capCup) : HoneycombAssignment n where
  tile := tile l r
  physical := physical l r hp hq
  outside := tile_outside l r
  horizontal := horizontal l r hl hr hcut
  vertical := vertical l r hl hr

lemma south_vacant (l r : List (Configuration n))
    (hl : ColumnChain.LocallyCompatible l) (hr : ColumnChain.LocallyCompatible r) (i : ℤ) :
    ¬(tile l r (i,0)).Occupied 0 := by
  by_cases hn : 0<n
  · rcases split_column i with ⟨k,rfl⟩ | ⟨k,rfl⟩
    · rw [tile_left l r k ⟨0,hn⟩]; exact hl.south k _ rfl
    · rw [tile_right l r k ⟨0,hn⟩,Tile.horizontal_occupied_zero]; exact hr.south k _ rfl
  · rw [tile_outside l r i 0 (by omega)]; exact Tile.vacant_not_occupied 0

lemma north_vacant (l r : List (Configuration n))
    (hl : ColumnChain.LocallyCompatible l) (hr : ColumnChain.LocallyCompatible r) (i : ℤ) (hn : 0<n) :
    ¬(tile l r (i,n-1)).Occupied 3 := by
  rcases split_column i with ⟨k,rfl⟩ | ⟨k,rfl⟩
  · rw [tile_left l r k ⟨n-1,by omega⟩]; exact hl.north k _ (by dsimp; omega)
  · rw [tile_right l r k ⟨n-1,by omega⟩,Tile.horizontal_occupied_three]
    exact hr.north k _ (by dsimp; omega)

lemma physical_from_weights (l r : List (Configuration (n+1)))
    (hl : ColumnChain.weight (Fin.snoc (fun _ : Fin n=>physicalWeights (2*Diagram.lambda)) northInjectionWeights) l≠0)
    (hr : ColumnChain.weight (Fin.snoc (fun _ : Fin n=>physicalWeights Diagram.lambda) northInjectionWeights) r≠0) :
    (∀k j, ColumnChain.read l k j≠.verticalPair) ∧ (∀k j, ColumnChain.read r k j≠.capCup) := by
  constructor
  · intro k j h
    have hh := ColumnChain.read_tile_ne_zero hl k j
    rw [h] at hh
    induction j using Fin.lastCases with
    | last => simp [Fin.snoc_last,northInjectionWeights,Weights.tile] at hh
    | cast i =>
      rw [Fin.snoc_castSucc] at hh
      change (physicalWeights (2*Diagram.lambda)).E≠0 at hh
      rw [physicalWeights_two_lambda] at hh
      exact hh rfl
  · intro k j h
    have hh := ColumnChain.read_tile_ne_zero hr k j
    rw [h] at hh
    induction j using Fin.lastCases with
    | last => simp [Fin.snoc_last,northInjectionWeights,Weights.tile] at hh
    | cast i =>
      rw [Fin.snoc_castSucc] at hh
      change (physicalWeights Diagram.lambda).F≠0 at hh
      rw [physicalWeights_lambda] at hh
      exact hh rfl

end SewnRectangle
end
end CriticalStrip

 

 

namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

namespace Graph

lemma drainsAt_iff {V : Type*} {r : V → V → Prop} {root : V} :
    DrainsAt r root ↔ Patch.drains r (fun v=>v=root) := by
  constructor
  · intro h v w hvw
    exact ⟨root,rfl,h v w hvw⟩
  · intro h v w hvw
    obtain ⟨_,rfl,hr⟩:=h v w hvw
    exact hr

lemma drainsAt_glued_iff {V W I : Type*} (r : V → V → Prop) (s : W → W → Prop)
    (a : I → V) (b : I → W) (active : I → Prop) (root : W) :
    DrainsAt (Patch.glued r s a b active) (.inr root) ↔
      (∀ v w,r v w → ∃ i,active i ∧ Relation.ReflTransGen r v (a i)) ∧
      DrainsAt (Patch.compressed r s a b active) root := by
  have he : (fun v : V⊕W=>v=Sum.inr root)=Patch.exteriorOutput (fun w=>w=root) := by
    funext v
    cases v <;> simp [Patch.exteriorOutput]
  rw [drainsAt_iff,he,Patch.drains_glued_iff,←drainsAt_iff]

end Graph

namespace GraphRealizes
variable {V W : Type*} {n : ℕ} {r : V → V → Prop} {s : W → W → Prop}
    {a : Fin n → V} {b : Fin n → W} {p q : Pairing n}

lemma compressed_closure_edge (hp : GraphRealizes r a p) {x y : W}
    (h : Patch.compressed r s a b p.Occupied x y) :
    x=y ∨ Graph.boundaryClosure s b p x y := by
  rcases h with h | ⟨i,j,hi,hj,hr,rfl,rfl⟩
  · exact Or.inr (Or.inl h)
  · rcases (hp.reach i j).mp hr with rfl | he
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨i,j,he,rfl,rfl⟩)

lemma closure_compressed_edge (hp : GraphRealizes r a p) {x y : W}
    (h : Graph.boundaryClosure s b p x y) :
    Patch.compressed r s a b p.Occupied x y := by
  rcases h with h | ⟨i,j,hij,rfl,rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨i,j,⟨j,hij⟩,⟨i,Pairing.adj_symm hij⟩,
      (hp.reach i j).mpr (Or.inr hij),rfl,rfl⟩

lemma compressed_closure_reach (hp : GraphRealizes r a p) (x y : W) :
    Relation.ReflTransGen (Patch.compressed r s a b p.Occupied) x y ↔
      Relation.ReflTransGen (Graph.boundaryClosure s b p) x y := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | @tail z w h hzw ih =>
      rcases hp.compressed_closure_edge hzw with rfl | he
      · exact ih
      · exact ih.tail he
  · exact Relation.ReflTransGen.mono (fun _ _=>hp.closure_compressed_edge) _ _

lemma compressed_closure_drains (hp : GraphRealizes r a p) (root : W) :
    Graph.DrainsAt (Patch.compressed r s a b p.Occupied) root ↔
      Graph.DrainsAt (Graph.boundaryClosure s b p) root := by
  constructor
  · intro h v w hvw
    exact (hp.compressed_closure_reach v root).mp (h v w (hp.closure_compressed_edge hvw))
  · intro h v w hvw
    apply (hp.compressed_closure_reach v root).mpr
    rcases hvw with he | ⟨i,j,⟨k,hik⟩,hj,hr,rfl,rfl⟩
    · exact h v w (Or.inl he)
    · exact h (b i) (b k) (Or.inr ⟨i,k,hik,rfl,rfl⟩)

 

theorem sewn_drains_iff (hp : GraphRealizes r a p) (hq : GraphRealizes s b q)
    (hb : Function.Injective b) (root : Fin n) :
    Graph.DrainsAt (Patch.glued r s a b p.Occupied) (.inr (b root)) ↔
      Graph.DrainsAt (p.join q) root := by
  rw [Graph.drainsAt_glued_iff,hp.compressed_closure_drains,hq.closure_drains_iff hb]
  have he : Graph.DrainsAt (q.join p) root ↔ Graph.DrainsAt (p.join q) root := by
    have hj : q.join p=p.join q := by funext i j; exact propext or_comm
    rw [hj]
  rw [he]
  exact ⟨fun h=>h.2,fun h=>⟨hp.no_loop,h⟩⟩

 

theorem gluesAt_iff_sewn (hp : GraphRealizes r a p) (hq : GraphRealizes s b q)
    (ha : Function.Injective a) (hb : Function.Injective b) (root : Fin n) :
    p.GluesAt root q ↔ Graph.Used r (a root) ∧
      (∀ i,Graph.Used r (a i) ↔ Graph.Used s (b i)) ∧
      Graph.DrainsAt (Patch.glued r s a b p.Occupied) (.inr (b root)) := by
  simp only [hp.boundary_used_iff ha,hq.boundary_used_iff hb,
    hp.sewn_drains_iff hq hb,Pairing.GluesAt]

end GraphRealizes

 

 


namespace PaddedColumn
variable {n : ℕ}
abbrev V (n : ℕ) := ℕ × Vertex n

def wiring (ts : List (Configuration n)) : V n → V n → Prop
  | (k,i,a),(l,j,b) =>
    (k=l ∧ BareColumn (ColumnChain.read ts k) (i,a) (j,b)) ∨
    (i=j ∧ a=2 ∧ b=1 ∧ l+1=k ∧ (ColumnChain.read ts k i).Occupied 2) ∨
    (i=j ∧ a=1 ∧ b=2 ∧ k+1=l ∧ (ColumnChain.read ts l j).Occupied 2)

def boundary (i : Fin n) : V n := (0,i,2)

lemma boundary_injective : Function.Injective (boundary (n:=n)) := by
  intro i j h; exact congrArg (fun x=>x.2.1) h

def active (ts : List (Configuration n)) (i : Fin n) : Prop :=
  (ColumnChain.read ts 0 i).Occupied 2

lemma wiring_nil (v w : V n) : ¬wiring [] v w := by
  rcases v with ⟨k,i,a⟩
  rcases w with ⟨l,j,b⟩
  simp only [wiring,ColumnChain.read_nil,BareColumn]
  have he (a b : Fin 4) : ¬Tile.vacant.Adj a b := by
    exact fun h=>Tile.vacant_not_occupied a ⟨b,h⟩
  simp [he,Tile.vacant_not_occupied]

lemma empty_realizes : GraphRealizes (wiring ([] : List (Configuration n))) boundary (empty n) := by
  constructor
  · exact fun v w h=>(wiring_nil v w h).elim
  · intro i j
    constructor
    · intro hr
      have hn (v w : V n) (h : Relation.ReflTransGen (wiring []) v w) : v=w := by
        induction h with
        | refl => rfl
        | @tail v w h h₁ ih => exact (wiring_nil v w h₁).elim
      have he := hn _ _ hr
      exact Or.inl (boundary_injective he)
    · rintro (rfl | h)
      · exact .refl
      · exact (empty_not_occupied i ⟨j,h⟩).elim

 
def addColumn (n : ℕ) : Sum (V n) (Vertex n) ≃ V n where
  toFun
    | .inl (k,v) => (k+1,v)
    | .inr v => (0,v)
  invFun
    | (0,v) => .inr v
    | (k+1,v) => .inl (k,v)
  left_inv := by rintro (⟨k,v⟩|v) <;> rfl
  right_inv := by rintro ⟨k,v⟩; cases k <;> rfl

lemma wiring_step (t : Configuration n) (ts : List (Configuration n))
    (v w : Sum (V n) (Vertex n)) :
    Patch.glued (wiring ts) (BareColumn t) boundary (fun i=>(i,1)) (active ts) v w ↔
      wiring (t::ts) (addColumn n v) (addColumn n w) := by
  cases v with
  | inl v =>
    rcases v with ⟨k,i,a⟩
    cases w with
    | inl w =>
      rcases w with ⟨l,j,b⟩
      simp [Patch.glued,wiring,addColumn]
    | inr w =>
      rcases w with ⟨j,b⟩
      by_cases hij : i=j
      · subst j
        simp [Patch.glued,wiring,addColumn,boundary,active,and_assoc,and_left_comm,and_comm]
        intro h _ _; subst h; rfl
      · simp [Patch.glued,wiring,addColumn,boundary,active,hij,Ne.symm hij]
  | inr v =>
    rcases v with ⟨i,a⟩
    cases w with
    | inl w =>
      rcases w with ⟨l,j,b⟩
      by_cases hij : i=j
      · subst j
        simp [Patch.glued,wiring,addColumn,boundary,active,and_assoc,and_left_comm,and_comm]
        intro h _ _; subst h; rfl
      · simp [Patch.glued,wiring,addColumn,boundary,active,hij,Ne.symm hij]
    | inr w =>
      rcases w with ⟨j,b⟩
      simp [Patch.glued,wiring,addColumn,BareColumn]

def stepEquivalence (t : Configuration n) (ts : List (Configuration n)) :
    Graph.BoundaryEquiv
      (Patch.glued (wiring ts) (BareColumn t) boundary (fun i=>(i,1)) (active ts))
      (wiring (t::ts)) (fun i=>.inr (i,2)) boundary :=
  Graph.BoundaryEquiv.ofEquiv (addColumn n) (wiring_step t ts) (fun _=>rfl)

 

theorem runs_realizes (ts : List (Configuration n)) (q : Pairing n)
    (h : ColumnChain.Runs (empty n) ts q) : GraphRealizes (wiring ts) boundary q := by
  induction ts generalizing q with
  | nil => exact h ▸ empty_realizes
  | cons t ts ih =>
    obtain ⟨p,hp,ht⟩ := h
    have hg := ih p hp
    have he : active ts=p.Occupied := by
      funext i
      exact propext ((ColumnChain.support_empty_read ts i).symm.trans
        (by rw [(ColumnChain.runs_sound _ _ _ hp).2.2]))
    apply (stepEquivalence t ts).realizes
    rw [he,hg.substitute_iff]
    exact (ColumnSew.equivalence p t).symm.realizes ((realizes_iff_column_graph p q t).mp ht).2

end PaddedColumn
end
end CriticalStrip.Diagram

 

 

namespace CriticalStrip
noncomputable section
open scoped Classical
open Diagram

namespace Diagram.Graph

 

lemma drainsAt_embedding_iff {V W : Type*} {r : V → V → Prop} {s : W → W → Prop}
    (f : V → W) (hf : Function.Injective f)
    (he : ∀v w, s (f v) (f w) ↔ r v w)
    (hs : ∀x y, s x y → x∈Set.range f ∧ y∈Set.range f) (root : V) :
    DrainsAt r root ↔ DrainsAt s (f root) := by
  have lift {x y : W} (h : Relation.ReflTransGen s x y) :
      ∀v, x=f v → ∃w, y=f w ∧ Relation.ReflTransGen r v w := by
    induction h with
    | refl => intro v hv; exact ⟨v,hv,.refl⟩
    | @tail y z h hyz ih =>
      intro v hv
      obtain ⟨u,rfl,hu⟩:=ih v hv
      obtain ⟨w,rfl⟩:=(hs _ _ hyz).2
      exact ⟨w,rfl,hu.tail ((he u w).mp hyz)⟩
  constructor
  · intro h x y hxy
    obtain ⟨v,rfl⟩:=(hs x y hxy).1
    obtain ⟨w,rfl⟩:=(hs _ y hxy).2
    exact map_reach f (fun x y h=>.single ((he x y).mpr h)) (h v w ((he v w).mp hxy))
  · intro h v w hvw
    obtain ⟨u,hu,hr⟩:=lift (h (f v) (f w) ((he v w).mpr hvw)) v rfl
    exact (hf hu).symm ▸ hr

end Diagram.Graph

namespace SewnRectangle
variable {n : ℕ}

 
def port : Sum (PaddedColumn.V n) (PaddedColumn.V n) → HoneycombPort
  | .inl (k,j,a) => ((-1-(k:ℤ),j.val),a)
  | .inr (k,j,a) => (((k:ℤ),j.val),Tile.horizontalPort a)

lemma port_injective : Function.Injective (port (n:=n)) := by
  rintro (⟨k,j,a⟩|⟨k,j,a⟩) (⟨l,i,b⟩|⟨l,i,b⟩) h
  all_goals simp only [port,Prod.mk.injEq] at h
  · obtain ⟨⟨hk,hj⟩,rfl⟩:=h
    have hk : k=l := by omega
    have hj : j=i := Fin.ext hj
    subst k j; rfl
  · obtain ⟨⟨hk,_⟩,_⟩:=h; omega
  · obtain ⟨⟨hk,_⟩,_⟩:=h; omega
  · obtain ⟨⟨hk,hj⟩,ha⟩:=h
    have hk : k=l := by omega
    have hj : j=i := Fin.ext hj
    have ha : a=b := Tile.horizontalPort.injective ha
    subst k j a; rfl

lemma mem_range_port (v : HoneycombPort) (hv : v.1.2<n) :
    v∈Set.range (port (n:=n)) := by
  rcases v with ⟨⟨i,j⟩,a⟩
  rcases split_column i with ⟨k,rfl⟩|⟨k,rfl⟩
  · exact ⟨.inl (k,⟨j,hv⟩,a),rfl⟩
  · exact ⟨.inr (k,⟨j,hv⟩,Tile.horizontalPort.symm a),by simp [port]⟩

lemma horizontalPort_eq (a b : Fin 4) :
    Tile.horizontalPort a=b ↔ a=Tile.horizontalPort b := by
  revert a b; decide

lemma wiring_left (D : HoneycombAssignment n) (l r : List (Configuration n))
    (ht : D.tile=tile l r) (k l' : ℕ) (i j : Fin n) (a b : Fin 4) :
    D.portWiring (port (.inl (k,i,a))) (port (.inl (l',j,b))) ↔
      PaddedColumn.wiring l (k,i,a) (l',j,b) := by
  have h₁ : -1-(k:ℤ)= -1-(l':ℤ) ↔ k=l' := by omega
  have h₂ : -1-(k:ℤ)+1= -1-(l':ℤ) ↔ l'+1=k := by omega
  have h₃ : -1-(l':ℤ)+1= -1-(k:ℤ) ↔ k+1=l' := by omega
  simp only [HoneycombAssignment.portWiring,port,ht,
    tile_left l r k i,tile_left l r l' j,Prod.mk.injEq,h₁,h₂,h₃,
    Fin.val_inj,j.isLt,i.isLt,PaddedColumn.wiring,BareColumn]
  constructor
  · rintro (⟨⟨hki,hij⟩,ht⟩|h|h|⟨hki,hij,_,ha,hb,ho⟩|⟨hki,hij,_,hb,ha,ho⟩)
    · exact Or.inl ⟨hki,Or.inl ⟨hij,ht⟩⟩
    · exact Or.inr (Or.inl ⟨h.1,h.2.2.1,h.2.2.2.1,h.2.1,h.2.2.2.2⟩)
    · exact Or.inr (Or.inr ⟨h.1.symm,h.2.2.2.1,h.2.2.1,h.2.1,h.2.2.2.2⟩)
    · exact Or.inl ⟨hki,Or.inr (Or.inl ⟨ha,hb,hij,ho⟩)⟩
    · have he : l'=k := by omega
      subst l'; exact Or.inl ⟨rfl,Or.inr (Or.inr ⟨hb,ha,hij,ho⟩)⟩
  · rintro (⟨rfl,(h|h|h)⟩|h|h)
    · exact Or.inl ⟨⟨rfl,h.1⟩,h.2⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,h.2.2.1,True.intro,h.1,h.2.1,h.2.2.2⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl,h.2.2.1,True.intro,h.1,h.2.1,h.2.2.2⟩)))
    · exact Or.inr (Or.inl ⟨h.1,h.2.2.2.1,h.2.1,h.2.2.1,h.2.2.2.2⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h.1.symm,h.2.2.2.1,h.2.2.1,h.2.1,h.2.2.2.2⟩))

lemma wiring_right (D : HoneycombAssignment n) (l r : List (Configuration n))
    (ht : D.tile=tile l r) (hr : ColumnChain.LocallyCompatible r)
    (k l' : ℕ) (i j : Fin n) (a b : Fin 4) :
    D.portWiring (port (.inr (k,i,a))) (port (.inr (l',j,b))) ↔
      PaddedColumn.wiring r (k,i,a) (l',j,b) := by
  have h₁ : (k:ℤ)=(l':ℤ) ↔ k=l' := by omega
  have h₂ : (k:ℤ)+1=(l':ℤ) ↔ k+1=l' := by omega
  have h₃ : (l':ℤ)+1=(k:ℤ) ↔ l'+1=k := by omega
  have h₄ : (l':ℤ)=(k:ℤ) ↔ k=l' := by omega
  have hp₀ : Tile.horizontalPort 0=0 := by decide
  have hp₁ : Tile.horizontalPort 1=2 := by decide
  have hp₂ : Tile.horizontalPort 2=1 := by decide
  have hp₃ : Tile.horizontalPort 3=3 := by decide
  simp only [HoneycombAssignment.portWiring,port,ht,
    tile_right l r k i,tile_right l r l' j,Prod.mk.injEq,h₁,h₂,h₃,h₄,
    Fin.val_inj,j.isLt,i.isLt,PaddedColumn.wiring,BareColumn,
    Tile.horizontal_adj,horizontalPort_eq,hp₀,hp₁,hp₂,hp₃,
    Tile.horizontal_occupied_two,Tile.horizontal_occupied_three]
  constructor
  · rintro (⟨⟨hki,hij⟩,ht⟩|⟨hij,hkl,ha,hb,ho⟩|⟨hij,hkl,hb,ha,ho⟩|
      ⟨hki,hij,_,ha,hb,ho⟩|⟨hki,hij,_,hb,ha,ho⟩)
    · exact Or.inl ⟨hki,Or.inl ⟨hij,ht⟩⟩
    · subst l'; subst j
      exact Or.inr (Or.inr ⟨rfl,ha,hb,rfl,(hr.horizontal k i).mpr ho⟩)
    · subst k; subst j
      exact Or.inr (Or.inl ⟨rfl,ha,hb,rfl,(hr.horizontal l' i).mpr ho⟩)
    · exact Or.inl ⟨hki,Or.inr (Or.inl ⟨ha,hb,hij,ho⟩)⟩
    · subst l'; exact Or.inl ⟨rfl,Or.inr (Or.inr ⟨hb,ha,hij,ho⟩)⟩
  · rintro (⟨rfl,(h|h|h)⟩|⟨hij,ha,hb,hkl,ho⟩|⟨hij,ha,hb,hkl,ho⟩)
    · exact Or.inl ⟨⟨rfl,h.1⟩,h.2⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,h.2.2.1,True.intro,h.1,h.2.1,h.2.2.2⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl,h.2.2.1,True.intro,h.1,h.2.1,h.2.2.2⟩)))
    · subst k; subst j
      exact Or.inr (Or.inr (Or.inl ⟨rfl,rfl,hb,ha,(hr.horizontal l' i).mp ho⟩))
    · subst l'; subst j
      exact Or.inr (Or.inl ⟨rfl,rfl,ha,hb,(hr.horizontal k i).mp ho⟩)

lemma wiring_cross (D : HoneycombAssignment n) (l r : List (Configuration n))
    (ht : D.tile=tile l r) (k l' : ℕ) (i j : Fin n) (a b : Fin 4) :
    D.portWiring (port (.inl (k,i,a))) (port (.inr (l',j,b))) ↔
      ∃ h : Fin n, PaddedColumn.active l h ∧
        (k,i,a)=PaddedColumn.boundary h ∧ (l',j,b)=PaddedColumn.boundary h := by
  have h₁ : ¬ -1-(k:ℤ)=(l':ℤ) := by omega
  have h₂ : -1-(k:ℤ)+1=(l':ℤ) ↔ k=0 ∧ l'=0 := by omega
  have h₃ : ¬ (l':ℤ)+1= -1-(k:ℤ) := by omega
  have h₄ : ¬ (l':ℤ)= -1-(k:ℤ) := by omega
  have hp₁ : Tile.horizontalPort 1=2 := by decide
  simp only [HoneycombAssignment.portWiring,port,ht,
    tile_left l r k i,tile_right l r l' j,Prod.mk.injEq,h₁,h₂,h₃,h₄,
    horizontalPort_eq,hp₁,false_and,and_false,false_or,or_false,Fin.val_inj]
  constructor
  · rintro ⟨rfl,⟨rfl,rfl⟩,rfl,rfl,ho⟩
    exact ⟨i,ho,rfl,rfl⟩
  · rintro ⟨h,ho,he,hf⟩
    simp only [PaddedColumn.boundary,Prod.mk.injEq] at he hf
    rcases he with ⟨rfl,rfl,rfl⟩
    rcases hf with ⟨rfl,rfl,rfl⟩
    exact ⟨rfl,⟨rfl,rfl⟩,rfl,rfl,ho⟩

 

theorem sewn_wiring (D : HoneycombAssignment n) (l r : List (Configuration n))
    (ht : D.tile=tile l r) (hr : ColumnChain.LocallyCompatible r)
    (v w : Sum (PaddedColumn.V n) (PaddedColumn.V n)) :
    D.portWiring (port v) (port w) ↔
      Patch.glued (PaddedColumn.wiring l) (PaddedColumn.wiring r)
        PaddedColumn.boundary PaddedColumn.boundary (PaddedColumn.active l) v w := by
  cases v with
  | inl v =>
    rcases v with ⟨k,i,a⟩
    cases w with
    | inl w =>
      rcases w with ⟨l',j,b⟩
      exact wiring_left D l r ht k l' i j a b
    | inr w =>
      rcases w with ⟨l',j,b⟩
      exact wiring_cross D l r ht k l' i j a b
  | inr v =>
    rcases v with ⟨k,i,a⟩
    cases w with
    | inl w =>
      rcases w with ⟨l',j,b⟩
      have hs : D.portWiring (port (.inr (k,i,a))) (port (.inl (l',j,b))) ↔
          D.portWiring (port (.inl (l',j,b))) (port (.inr (k,i,a))) :=
        ⟨D.portWiring_symm,D.portWiring_symm⟩
      rw [hs,wiring_cross D l r ht l' k j i b a]
      simp only [Patch.glued,and_comm]
    | inr w =>
      rcases w with ⟨l',j,b⟩
      exact wiring_right D l r ht hr k l' i j a b

lemma sewn_drains_iff (D : HoneycombAssignment n) (l r : List (Configuration n))
    (ht : D.tile=tile l r) (hr : ColumnChain.LocallyCompatible r)
    (root : Sum (PaddedColumn.V n) (PaddedColumn.V n)) :
    Graph.DrainsAt (Patch.glued (PaddedColumn.wiring l) (PaddedColumn.wiring r)
      PaddedColumn.boundary PaddedColumn.boundary (PaddedColumn.active l)) root ↔
      Graph.DrainsAt D.portWiring (port root) := by
  apply Graph.drainsAt_embedding_iff port port_injective (sewn_wiring D l r ht hr)
  intro v w hvw
  exact ⟨mem_range_port v (D.port_in_strip ((D.port_used v).mp ⟨w,hvw⟩)),
    mem_range_port w (D.port_in_strip ((D.port_used w).mp ⟨v,D.portWiring_symm hvw⟩))⟩

 

theorem gluesAt_physical_iff (l r : List (Configuration n)) (p q : Pairing n)
    (hl : ColumnChain.Runs (empty n) l p) (hr : ColumnChain.Runs (empty n) r q)
    (D : HoneycombAssignment n) (ht : D.tile=tile l r) (root : Fin n) :
    p.GluesAt root q ↔ p.Occupied root ∧
      (∀i, p.Occupied i ↔ q.Occupied i) ∧
      Graph.DrainsAt D.portWiring ((0,root.val),1) := by
  have hl' := ColumnChain.runs_sound _ _ _ hl
  have hr' := ColumnChain.runs_sound _ _ _ hr
  have ha : PaddedColumn.active l=p.Occupied := by
    funext i
    exact propext ((ColumnChain.support_empty_read l i).symm.trans
      (by rw [hl'.2.2]))
  have hd := sewn_drains_iff D l r ht (ColumnChain.compatible_empty_iff r |>.mp hr'.1)
    (.inr (PaddedColumn.boundary root))
  have hp := PaddedColumn.runs_realizes l p hl
  have hq := PaddedColumn.runs_realizes r q hr
  have hg := hp.sewn_drains_iff hq PaddedColumn.boundary_injective root
  rw [ha] at hd
  have he : port (.inr (PaddedColumn.boundary root))=((0,root.val),1) := rfl
  rw [he] at hd
  rw [Pairing.GluesAt,hd.symm,hg]

end SewnRectangle
end
end CriticalStrip

end OAI
