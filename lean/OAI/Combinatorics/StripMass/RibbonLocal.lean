import Mathlib
import OAI.Combinatorics.StripMass.TurnRectangleMatching

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.HoneycombBranch
noncomputable section
open scoped Classical
open Diagram

 
def slot (b : Bool) (p : Fin 3) : Fin 3 :=
  if b then if p=0 then 1 else if p=1 then 0 else 2
  else if p=0 then 2 else if p=1 then 1 else 0

 
def lane (b : Bool) (p : Fin 3) (l : Fin 2) : Fin 6 :=
  ⟨2*(slot b p).val+l.val,by have := (slot b p).isLt; omega⟩

def localGauge (b : Bool) : Fin 6 → ℤ :=
  if b then TurnDisk.Rhombus.upGauge else TurnDisk.Rhombus.downGauge

lemma slot_injective (b : Bool) : Function.Injective (slot b) := by
  intro p q h
  cases b <;> fin_cases p <;> fin_cases q <;> simp_all [slot]

lemma lane_injective (b : Bool) {p q : Fin 3} {l m : Fin 2} :
    lane b p l=lane b q m ↔ p=q ∧ l=m := by
  constructor
  · intro h
    have hh:=congrArg Fin.val h
    change 2*(slot b p).val+l.val=2*(slot b q).val+m.val at hh
    have hs : slot b p=slot b q := Fin.ext (by have := l.isLt; have :=m.isLt; omega)
    exact ⟨slot_injective b hs,Fin.ext (by have :=l.isLt; have :=m.isLt; omega)⟩
  · rintro ⟨rfl,rfl⟩; rfl

lemma lane_cover (b : Bool) (i : Fin 6) : ∃ p l,lane b p l=i := by
  cases b <;> fin_cases i <;> decide

lemma local_turn (b : Bool) (p : Fin 3) (a : Bool) :
    Pairing.arcTurn (localGauge b) (lane b p 0) (lane b (outgoing p a) 1)=sign a := by
  cases b <;> cases a <;> fin_cases p <;> decide

end

 

 

noncomputable section
open scoped Classical
open Diagram FiniteBranchTree

 
def passes (s : State) : List Bool → List (State × Fin 3)
  | []=>[]
  | b::l=>(s,outgoing s.2 b)::passes (next s b) l

@[simp] lemma passes_nil (s : State) : passes s []=[] := rfl
@[simp] lemma passes_cons (s : State) (b : Bool) (l : List Bool) :
    passes s (b::l)=(s,outgoing s.2 b)::passes (next s b) l := rfl

lemma passes_vertices (s : State) (l : List Bool) :
    (passes s l).map (fun x=>x.1.1)=visited Prod.fst next s l := by
  induction l generalizing s with
  | nil=>rfl
  | cons b l ih=>simp only [passes,List.map_cons,visited,ih]

lemma passes_append (s : State) (l m : List Bool) :
    passes s (l++m)=passes s l++passes (terminal next s l) m := by
  induction l generalizing s with
  | nil=>rfl
  | cons b l ih=>simp only [List.cons_append,passes,terminal,ih]

lemma passes_shift (s : State) (l : List Bool) :
    s::(passes s l).map (fun x=>(neighbor x.1.1 x.2,x.2)) =
      (passes s l).map Prod.fst ++ [terminal next s l] := by
  induction l generalizing s with
  | nil=>rfl
  | cons b l ih=>
    simp only [passes,List.map_cons,List.cons_append,terminal,List.cons.injEq,true_and]
    exact ih (next s b)

lemma passes_mem_vertex {s : State} {l : List Bool} {v : Vertex} {p q : Fin 3}
    (h : ((v,p),q)∈passes s l) : v∈visited Prod.fst next s l := by
  rw [←passes_vertices]
  exact List.mem_map.mpr ⟨((v,p),q),h,rfl⟩

lemma passes_ne {s : State} {l : List Bool} {v : Vertex} {p q : Fin 3}
    (h : ((v,p),q)∈passes s l) : q≠p := by
  induction l generalizing s with
  | nil=>simp only [passes,List.not_mem_nil] at h
  | cons b l ih=>
    rcases List.mem_cons.mp h with he|h
    · have hp := congrArg (fun z : State × Fin 3 => z.1.2) he
      have hq := congrArg (fun z : State × Fin 3 => z.2) he
      change p=s.2 at hp
      change q=outgoing s.2 b at hq
      rw [hq,hp]
      exact outgoing_ne _ _
    · exact ih h

 
def routes (s : State) (l : List Bool) (v : Vertex) : Finset (Fin 3 × Fin 3) :=
  Finset.univ.filter (fun pq=>((v,pq.1),pq.2)∈passes s l)

@[simp] lemma mem_routes (s : State) (l : List Bool) (v : Vertex) (pq : Fin 3 × Fin 3) :
    pq∈routes s l v ↔ ((v,pq.1),pq.2)∈passes s l := by simp [routes]

@[simp] lemma routes_nil (s : State) (v : Vertex) : routes s [] v=∅ := by
  ext x; simp

lemma routes_cons (s : State) (b : Bool) (l : List Bool) (v : Vertex) :
    routes s (b::l) v=(if v=s.1 then {(s.2,outgoing s.2 b)} else ∅) ∪ routes (next s b) l v := by
  rcases s with ⟨w,p⟩
  ext ⟨i,j⟩
  simp only [mem_routes,passes_cons,List.mem_cons,Prod.mk.injEq,Finset.mem_union]
  split_ifs <;> simp_all

lemma routes_append (s : State) (l m : List Bool) (v : Vertex) :
    routes s (l++m) v=routes s l v ∪ routes (terminal next s l) m v := by
  ext x; simp [passes_append]

def swapPass (x : State × Fin 3) : State × Fin 3 := ((x.1.1,x.2),x.1.2)

lemma passes_reverseTurns (s : State) (l : List Bool) :
    passes (back (terminal next s l)) (reverseTurns l)=((passes s l).map swapPass).reverse := by
  induction l generalizing s with
  | nil=>rfl
  | cons b l ih=>
    simp only [reverseTurns,List.reverse_cons,List.map_append,List.map_singleton,terminal,passes_append]
    change passes (back (terminal next (next s b) l)) (reverseTurns l) ++
      passes (terminal next (back (terminal next (next s b) l)) (reverseTurns l)) [!b]=_
    rw [ih,terminal_reverseTurns]
    simp only [passes,List.map_cons,List.reverse_cons,back_next,swapPass,outgoing_opp]

lemma routes_reverseTurns (s : State) (l : List Bool) (v : Vertex) :
    routes (back (terminal next s l)) (reverseTurns l) v = (routes s l v).image Prod.swap := by
  ext ⟨p,q⟩
  simp only [mem_routes,passes_reverseTurns,List.mem_reverse,List.mem_map,Finset.mem_image]
  constructor
  · rintro ⟨⟨⟨w,i⟩,j⟩,hm,he⟩
    change ((w,j),i)=((v,p),q) at he
    obtain ⟨⟨rfl,rfl⟩,rfl⟩:=Prod.mk.inj he
    exact ⟨(i,p),by simpa using hm,rfl⟩
  · rintro ⟨⟨i,j⟩,hm,he⟩
    obtain ⟨rfl,rfl⟩:=Prod.mk.inj he
    exact ⟨_,by simpa using hm,rfl⟩

lemma routes_empty_of_notMem {s : State} {l : List Bool} {v : Vertex}
    (h : v∉visited Prod.fst next s l) : routes s l v=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact h (passes_mem_vertex ((mem_routes _ _ _ _).mp hx))

lemma routes_singleton_of_nodup {s : State} {l : List Bool}
    (hn : (visited Prod.fst next s l).Nodup) (v : Vertex) :
    routes s l v=∅ ∨ ∃ p q, q≠p ∧ routes s l v={(p,q)} := by
  induction l generalizing s with
  | nil=>exact Or.inl (routes_nil _ _)
  | cons b l ih=>
    have hn':=(List.nodup_cons.mp hn)
    rw [routes_cons]
    by_cases hv : v=s.1
    · subst v
      rw [ite_eq_left rfl,routes_empty_of_notMem hn'.1,Finset.union_empty]
      exact Or.inr ⟨s.2,outgoing s.2 b,outgoing_ne _ _,rfl⟩
    · rw [ite_eq_right hv,Finset.empty_union]
      exact ih hn'.2

 
def ribbonArcs (b : Bool) (a : Finset (Fin 3 × Fin 3)) : Finset (Fin 6 × Fin 6) :=
  a.image (fun pq=>Pairing.orderedEdge (lane b pq.1 0) (lane b pq.2 1))

lemma ribbonArcs_empty (b : Bool) : ribbonArcs b ∅=∅ := by simp [ribbonArcs]
lemma ribbonArcs_union (b : Bool) (a d : Finset (Fin 3 × Fin 3)) :
    ribbonArcs b (a∪d)=ribbonArcs b a ∪ ribbonArcs b d := Finset.image_union _ _

lemma ribbon_singleton (b : Bool) (p q : Fin 3) : IsPairing (ribbonArcs b {(p,q)}) := by
  cases b <;> fin_cases p <;> fin_cases q <;>
    simp [IsPairing,ribbonArcs,Pairing.orderedEdge,lane,slot]
lemma ribbon_double (b : Bool) (p q : Fin 3) (h : p≠q) :
    IsPairing (ribbonArcs b {(p,q),(q,p)}) := by
  cases b <;> fin_cases p <;> fin_cases q <;>
    first | exact (h rfl).elim | simp [IsPairing,ribbonArcs,Pairing.orderedEdge,lane,slot]
lemma ribbon_joint (b : Bool) (p : Fin 3) :
    IsPairing (ribbonArcs b {(p,outgoing p true),(outgoing p false,p)}) := by
  cases b <;> fin_cases p <;>
    simp [IsPairing,ribbonArcs,Pairing.orderedEdge,lane,slot,outgoing]

 
def RibbonSimple (s : State) (l : List Bool) : Prop :=
  ∀ v, IsPairing (ribbonArcs v.2.2 (routes s l v))

lemma ribbonSimple_of_nodup {s : State} {l : List Bool}
    (hn : (visited Prod.fst next s l).Nodup) : RibbonSimple s l := by
  intro v
  rcases routes_singleton_of_nodup hn v with he|⟨p,q,_,he⟩
  · rw [he,ribbonArcs_empty]; exact (empty 6).property
  · rw [he]; exact ribbon_singleton _ _ _

end

 

 

noncomputable section
open scoped Classical
open Diagram Diagram.TurnNetwork Diagram.TurnDisk
namespace RibbonRectangle
section Geometry

variable (L : ℤ) (M N : ℕ)

def Inside (v : Vertex) : Prop :=
  L≤v.1 ∧ v.1<L+(M:ℤ) ∧ 0≤v.2.1 ∧ v.2.1<(N:ℤ)

def vertex (c : Fin M) (r : Fin N) (b : Bool) : Vertex := (L+(c.val:ℤ),(r.val:ℤ),b)

lemma vertex_inside (c : Fin M) (r : Fin N) (b : Bool) : Inside L M N (vertex L M N c r b) := by
  dsimp [Inside,vertex]
  have :=c.isLt; have :=r.isLt
  omega

variable {L M N}

def col {v : Vertex} (h : Inside L M N v) : Fin M := ⟨(v.1-L).toNat,by dsimp [Inside] at h; omega⟩
def row {v : Vertex} (h : Inside L M N v) : Fin N := ⟨v.2.1.toNat,by dsimp [Inside] at h; omega⟩

lemma vertex_col_row {v : Vertex} (h : Inside L M N v) : vertex L M N (col h) (row h) v.2.2=v := by
  dsimp [vertex,col,row]
  congr 1
  · dsimp [Inside] at h; omega
  · apply Prod.ext
    · dsimp [Inside] at h; omega
    · rfl

@[simp] lemma col_vertex (c : Fin M) (r : Fin N) (b : Bool) :
    col (vertex_inside L M N c r b)=c := by
  apply Fin.ext
  simp [col,vertex]
@[simp] lemma row_vertex (c : Fin M) (r : Fin N) (b : Bool) :
    row (vertex_inside L M N c r b)=r := by
  apply Fin.ext
  simp [row,vertex]

variable (L M N) (F : Vertex → Pairing 6)

def up (t : ℕ) : Pairing 6 := F (L+((t/N:ℕ):ℤ),((t%N:ℕ):ℤ),true)
def down (t : ℕ) : Pairing 6 := F (L+((t/N:ℕ):ℤ),((t%N:ℕ):ℤ),false)

def node {v : Vertex} (h : Inside L M N v) (i : Fin 6) : Node (TurnRectangle.ports M N) (M*N) :=
  TurnRectangle.cellNode (col h) (row h) (if v.2.2 then .inl i else .inr i)

lemma up_time (c : Fin M) (r : Fin N) : up L N F (c.val*N+r.val)=F (vertex L M N c r true) := by
  simp only [up,vertex]
  congr 2
  · rw [Nat.mul_comm c.val N,Nat.mul_add_div (by have :=r.isLt; omega : 0<N),Nat.div_eq_of_lt r.isLt,Nat.add_zero]
  · rw [Nat.mul_comm c.val N,Nat.mul_add_mod,Nat.mod_eq_of_lt r.isLt]
lemma down_time (c : Fin M) (r : Fin N) : down L N F (c.val*N+r.val)=F (vertex L M N c r false) := by
  simp only [down,vertex]
  congr 2
  · rw [Nat.mul_comm c.val N,Nat.mul_add_div (by have :=r.isLt; omega : 0<N),Nat.div_eq_of_lt r.isLt,Nat.add_zero]
  · rw [Nat.mul_comm c.val N,Nat.mul_add_mod,Nat.mod_eq_of_lt r.isLt]

variable {L M N F}

lemma at_vertex (c : Fin M) (r : Fin N) (b : Bool) (i : Fin 6) :
    node L M N (vertex_inside L M N c r b) i=
      TurnRectangle.cellNode c r (if b then .inl i else .inr i) := by
  unfold node
  rw [col_vertex,row_vertex]
  rfl

variable (hM : 1≤M) (hN : 1≤N) (F : Vertex → Pairing 6)

abbrev start := TurnRectangle.startPairing (M:=M) (N:=N) (up L N F)
abbrev graph := TurnRectangle.edges hM hN (start (L:=L) F) (up L N F) (down L N F)
abbrev turnEdge := TurnRectangle.turns hM hN (start (L:=L) F) (up L N F) (down L N F)
abbrev boundary := TurnRectangle.bdry hM hN (start (L:=L) F) (TurnRectangle.starterGauge M N)
  (up L N F) (down L N F) (M*N)

lemma arc_edge {v : Vertex} (h : Inside L M N v) {i j : Fin 6} (hij : (F v).Adj i j) :
    graph (L:=L) hM hN F (node L M N h i) (node L M N h j) := by
  obtain ⟨c,r,b,rfl⟩ : ∃ c r b,v=vertex L M N c r b :=
    ⟨col h,row h,v.2.2,(vertex_col_row h).symm⟩
  cases b
  · rw [at_vertex,at_vertex]
    apply TurnRectangle.down_edge hM hN (start (L:=L) F) (up L N F) (down L N F)
    rwa [down_time]
  · rw [at_vertex,at_vertex]
    apply TurnRectangle.up_edge hM hN (start (L:=L) F) (up L N F) (down L N F)
    rwa [up_time]

lemma arc_turn {v : Vertex} (h : Inside L M N v) {i j : Fin 6} (hij : (F v).Adj i j) :
    turnEdge (L:=L) hM hN F (node L M N h i) (node L M N h j)=Pairing.arcTurn (localGauge v.2.2) i j := by
  obtain ⟨c,r,b,rfl⟩ : ∃ c r b,v=vertex L M N c r b :=
    ⟨col h,row h,v.2.2,(vertex_col_row h).symm⟩
  cases b
  · rw [at_vertex,at_vertex]
    apply TurnRectangle.down_turn hM hN (start (L:=L) F) (up L N F) (down L N F)
    rwa [down_time]
  · rw [at_vertex,at_vertex]
    apply TurnRectangle.up_turn hM hN (start (L:=L) F) (up L N F) (down L N F)
    rwa [up_time]

 
def Matches : Prop := ∀ v p, Inside L M N v → Inside L M N (neighbor v p) → ∀ l : Fin 2,
  (F v).Occupied (lane v.2.2 p l) ↔ (F (neighbor v p)).Occupied (lane (!v.2.2) p (1-l))

lemma interior_matches (hm : Matches (L:=L) (M:=M) (N:=N) F) :
    TurnRectangle.InteriorMatches (M:=M) (N:=N) (up L N F) (down L N F) := by
  refine ⟨?_,?_,?_⟩
  · intro c r hc hr l
    have hh:=hm (vertex L M N ⟨c,hc⟩ ⟨r,hr⟩ true) 2
      (vertex_inside _ _ _ _ _ _) (by simpa [neighbor,vertex] using
          (vertex_inside L M N ⟨c,hc⟩ ⟨r,hr⟩ false)) l
    rw [up_time L M N F ⟨c,hc⟩ ⟨r,hr⟩,down_time L M N F ⟨c,hc⟩ ⟨r,hr⟩]
    fin_cases l <;> simpa [neighbor,lane,slot,vertex] using hh
  · intro c r hc hr hr0 l
    have hv:=vertex_inside L M N (⟨c,hc⟩:Fin M) (⟨r,hr⟩:Fin N) true
    have he : neighbor (vertex L M N ⟨c,hc⟩ ⟨r,hr⟩ true) 0=
        vertex L M N ⟨c,hc⟩ ⟨r-1,by omega⟩ false := by
      dsimp [neighbor,vertex]; congr 2; omega
    have hh:=hm _ 0 hv (by rw [he]; exact vertex_inside _ _ _ _ _ _) (1-l)
    rw [he] at hh
    rw [down_time L M N F ⟨c,hc⟩ ⟨r-1,by omega⟩,up_time L M N F ⟨c,hc⟩ ⟨r,hr⟩]
    fin_cases l <;> simpa [lane,slot,vertex] using hh.symm
  · intro c r hc hc0 hr l
    have hv:=vertex_inside L M N (⟨c,hc⟩:Fin M) (⟨r,hr⟩:Fin N) true
    have he : neighbor (vertex L M N ⟨c,hc⟩ ⟨r,hr⟩ true) 1=
        vertex L M N ⟨c-1,by omega⟩ ⟨r,hr⟩ false := by
      dsimp [neighbor,vertex]; congr 2; omega
    have hh:=hm _ 1 hv (by rw [he]; exact vertex_inside _ _ _ _ _ _) (1-l)
    rw [he] at hh
    rw [down_time L M N F ⟨c-1,by omega⟩ ⟨r,hr⟩,up_time L M N F ⟨c,hc⟩ ⟨r,hr⟩]
    fin_cases l <;> simpa [lane,slot,vertex] using hh.symm

lemma physical_matches (hm : Matches (L:=L) (M:=M) (N:=N) F) :
    TurnRectangle.PhysicalMatches hM hN (start (L:=L) F) (up L N F) (down L N F) :=
  TurnRectangle.starter_physical hM hN _ _ (interior_matches F hm)

end Geometry

 

 


variable {L : ℤ} {M N : ℕ}

lemma node_eq {v w : Vertex} (hv : Inside L M N v) (hw : Inside L M N w)
    (he : v=w) (i : Fin 6) : node L M N hv i=node L M N hw i := by
  subst w; rfl

lemma node_of_vertex {v : Vertex} (h : Inside L M N v) {c : Fin M} {r : Fin N} {b : Bool}
    (he : v=vertex L M N c r b) (i : Fin 6) :
    node L M N h i=TurnRectangle.cellNode c r (if b then .inl i else .inr i) := by
  subst v
  exact at_vertex c r b i

variable (hM : 1≤M) (hN : 1≤N) (F : Vertex → Pairing 6)
  (hm : Matches (L:=L) (M:=M) (N:=N) F)
include hm

lemma up_wire (c : Fin M) (r : Fin N) (p : Fin 3) (l : Fin 2)
    (hw : Inside L M N (neighbor (vertex L M N c r true) p))
    (hi : (F (vertex L M N c r true)).Occupied (lane true p l)) :
    graph (L:=L) hM hN F
      (node L M N (vertex_inside L M N c r true) (lane true p l))
      (node L M N hw (lane false p (1-l))) ∧
    turnEdge (L:=L) hM hN F
      (node L M N (vertex_inside L M N c r true) (lane true p l))
      (node L M N hw (lane false p (1-l)))=0 := by
  have hm':=physical_matches hM hN F hm
  fin_cases p
  · have hr : 0<r.val := by dsimp [Inside,neighbor,vertex] at hw; omega
    have he : neighbor (vertex L M N c r true) 0=
        vertex L M N c ⟨r.val-1,by omega⟩ false := by
      dsimp [neighbor,vertex]; congr 2; omega
    rw [at_vertex,node_of_vertex hw he]
    have hh : (up L N F (c.val*N+r.val)).Occupied ⟨3-(1-l).val,by omega⟩ := by
      rw [up_time]
      fin_cases l <;> exact hi
    have hE:=TurnRectangle.vertical_edge hM hN (start (L:=L) F) (up L N F) (down L N F) hm' hr (1-l) hh
    have hT:=TurnRectangle.vertical_turn hM hN (start (L:=L) F) (up L N F) (down L N F) hm' hr (1-l) hh
    fin_cases l
    · refine ⟨symm hE,?_⟩
      rw [turnEdge,TurnRectangle.turns,TurnNetwork.edgeTurn_reverse]
      exact congrArg Neg.neg hT
    · refine ⟨symm hE,?_⟩
      rw [turnEdge,TurnRectangle.turns,TurnNetwork.edgeTurn_reverse]
      exact congrArg Neg.neg hT
  · have hc : 0<c.val := by dsimp [Inside,neighbor,vertex] at hw; omega
    have he : neighbor (vertex L M N c r true) 1=
        vertex L M N ⟨c.val-1,by omega⟩ r false := by
      dsimp [neighbor,vertex]; congr 2; omega
    rw [at_vertex,node_of_vertex hw he]
    have hh : (up L N F (c.val*N+r.val)).Occupied ⟨1-(1-l).val,by omega⟩ := by
      rw [up_time]
      fin_cases l <;> exact hi
    have hE:=TurnRectangle.horizontal_edge hM hN (start (L:=L) F) (up L N F) (down L N F) hm' hc (1-l) hh
    have hT:=TurnRectangle.horizontal_turn hM hN (start (L:=L) F) (up L N F) (down L N F) hm' hc (1-l) hh
    fin_cases l
    · refine ⟨symm hE,?_⟩
      rw [turnEdge,TurnRectangle.turns,TurnNetwork.edgeTurn_reverse]
      exact congrArg Neg.neg hT
    · refine ⟨symm hE,?_⟩
      rw [turnEdge,TurnRectangle.turns,TurnNetwork.edgeTurn_reverse]
      exact congrArg Neg.neg hT
  · have he : neighbor (vertex L M N c r true) 2=vertex L M N c r false := rfl
    rw [at_vertex,node_of_vertex hw he]
    have hh : (up L N F (c.val*N+r.val)).Occupied ⟨4+l.val,by omega⟩ := by
      rw [up_time]
      exact hi
    have hE:=TurnRectangle.diagonal_edge hM hN (start (L:=L) F) (up L N F) (down L N F) hm' l hh
    have hT:=TurnRectangle.diagonal_turn hM hN (start (L:=L) F) (up L N F) (down L N F) hm' l hh
    fin_cases l <;> exact ⟨hE,hT⟩

lemma wire {v : Vertex} (hv : Inside L M N v) (p : Fin 3) (l : Fin 2)
    (hw : Inside L M N (neighbor v p))
    (hi : (F v).Occupied (lane v.2.2 p l)) :
    graph (L:=L) hM hN F (node L M N hv (lane v.2.2 p l))
      (node L M N hw (lane (!v.2.2) p (1-l))) ∧
    turnEdge (L:=L) hM hN F (node L M N hv (lane v.2.2 p l))
      (node L M N hw (lane (!v.2.2) p (1-l)))=0 := by
  let w:=neighbor v p
  have hb : w.2.2= !v.2.2 := by
    cases he : v.2.2 <;> simp [w,neighbor,he] <;> split_ifs <;> rfl
  have hww : neighbor w p=v := neighbor_reverse v p
  cases hvb : v.2.2
  · have hwb : w.2.2=true := by simp [hb,hvb]
    have hwv : vertex L M N (col hw) (row hw) true=w := by
      rw [←hwb]
      exact vertex_col_row hw
    have hi' : (F w).Occupied (lane true p (1-l)) := by
      rw [←hwb,hb]
      exact (hm v p hv hw l).mp hi
    have hww' : neighbor (vertex L M N (col hw) (row hw) true) p=v := by rw [hwv,hww]
    have hh:=up_wire hM hN F hm (col hw) (row hw) p (1-l)
      (by rw [hww']; exact hv) (by rwa [hwv])
    have hn₁ (i : Fin 6) : node L M N (vertex_inside L M N (col hw) (row hw) true) i=
        node L M N hw i := by rw [at_vertex,node_of_vertex hw hwv.symm]
    have hn₂ (i : Fin 6) (hx : Inside L M N (neighbor (vertex L M N (col hw) (row hw) true) p)) :
        node L M N hx i=node L M N hv i := by
      exact node_eq hx hv hww' i
    rw [hn₁,hn₂] at hh
    simp only [Bool.not_false]
    have hll : 1-(1-l)=l := by fin_cases l <;> decide
    rw [hll] at hh
    refine ⟨symm hh.1,?_⟩
    rw [turnEdge,TurnRectangle.turns,TurnNetwork.edgeTurn_reverse]
    exact congrArg Neg.neg hh.2
  · have hvv : v=vertex L M N (col hv) (row hv) true := by
      rw [←hvb]
      exact (vertex_col_row hv).symm
    have hw' : Inside L M N (neighbor (vertex L M N (col hv) (row hv) true) p) := by rwa [←hvv]
    have hh:=up_wire hM hN F hm (col hv) (row hv) p l hw' (by rwa [←hvv,←hvb])
    rw [node_eq _ hv hvv.symm, node_eq _ hw (congrArg (fun x=>neighbor x p) hvv.symm)] at hh
    simpa only [hvb,Bool.not_true] using hh

end RibbonRectangle
end

 

 

noncomputable section
open scoped Classical
open Diagram FiniteBranchTree

 
def ribbon {s : State} {l : List Bool} (h : RibbonSimple s l) (v : Vertex) : Pairing 6 :=
  ⟨ribbonArcs v.2.2 (routes s l v),h v⟩

lemma ribbon_arc {s : State} {l : List Bool} (h : RibbonSimple s l) {v : Vertex} {p q : Fin 3}
    (hp : ((v,p),q)∈passes s l) : (ribbon h v).Adj (lane v.2.2 p 0) (lane v.2.2 q 1) := by
  have hm : Pairing.orderedEdge (lane v.2.2 p 0) (lane v.2.2 q 1)∈(ribbon h v).val :=
    Finset.mem_image.mpr ⟨(p,q),(mem_routes _ _ _ _).mpr hp,rfl⟩
  unfold Pairing.orderedEdge at hm
  rcases le_total (lane v.2.2 p 0) (lane v.2.2 q 1) with he|he
  · exact Or.inl (by simpa only [min_eq_left he,max_eq_right he] using hm)
  · exact Or.inr (by simpa only [min_eq_right he,max_eq_left he] using hm)

lemma ribbon_occupied {s : State} {l : List Bool} (h : RibbonSimple s l) (v : Vertex) (i : Fin 6) :
    (ribbon h v).Occupied i ↔ ∃ p q, ((v,p),q)∈passes s l ∧
      (i=lane v.2.2 p 0 ∨ i=lane v.2.2 q 1) := by
  constructor
  · rintro ⟨j,hj|hj⟩ <;> obtain ⟨⟨p,q⟩,hp,he⟩:=Finset.mem_image.mp hj
    · refine ⟨p,q,(mem_routes _ _ _ _).mp hp,?_⟩
      have hi:=congrArg Prod.fst he
      change min (lane v.2.2 p 0) (lane v.2.2 q 1)=i at hi
      rcases le_total (lane v.2.2 p 0) (lane v.2.2 q 1) with hh|hh
      · exact Or.inl (hi.symm.trans (min_eq_left hh))
      · exact Or.inr (hi.symm.trans (min_eq_right hh))
    · refine ⟨p,q,(mem_routes _ _ _ _).mp hp,?_⟩
      have hi:=congrArg Prod.snd he
      change max (lane v.2.2 p 0) (lane v.2.2 q 1)=i at hi
      rcases le_total (lane v.2.2 p 0) (lane v.2.2 q 1) with hh|hh
      · exact Or.inr (hi.symm.trans (max_eq_right hh))
      · exact Or.inl (hi.symm.trans (max_eq_left hh))
  · rintro ⟨p,q,hp,rfl|rfl⟩
    · exact ⟨_,ribbon_arc h hp⟩
    · exact ⟨_,(ribbon_arc h hp).symm⟩

lemma ribbon_incoming {s : State} {l : List Bool} (h : RibbonSimple s l) (v : Vertex) (p : Fin 3) :
    (ribbon h v).Occupied (lane v.2.2 p 0) ↔ ∃ q, ((v,p),q)∈passes s l := by
  rw [ribbon_occupied]
  simp only [lane_injective,Fin.zero_ne_one,and_false,or_false,and_true]
  constructor
  · rintro ⟨p',q,hp,rfl⟩; exact ⟨q,hp⟩
  · rintro ⟨q,hq⟩; exact ⟨p,q,hq,rfl⟩

lemma ribbon_outgoing {s : State} {l : List Bool} (h : RibbonSimple s l) (v : Vertex) (p : Fin 3) :
    (ribbon h v).Occupied (lane v.2.2 p 1) ↔ ∃ q, ((v,q),p)∈passes s l := by
  rw [ribbon_occupied]
  simp only [lane_injective,(show (1:Fin 2)≠0 from by decide),and_false,false_or,and_true]
  constructor
  · rintro ⟨p',q,hp,rfl⟩; exact ⟨p',hp⟩
  · rintro ⟨q,hq⟩; exact ⟨q,p,hq,rfl⟩

lemma route_shift_iff (s : State) (l : List Bool) (v : Vertex) (p : Fin 3) :
    ((v,p)=s ∨ ∃ q,((neighbor v p,q),p)∈passes s l) ↔
      (∃q,((v,p),q)∈passes s l) ∨ (v,p)=terminal next s l := by
  have hs:=congrArg (fun xs : List State => (v,p)∈xs) (passes_shift s l)
  simp only [List.mem_cons,List.mem_append,List.mem_map] at hs
  have ha : (∃ a∈passes s l,(neighbor a.1.1 a.2,a.2)=(v,p)) ↔
      ∃q,((neighbor v p,q),p)∈passes s l := by
    constructor
    · rintro ⟨⟨⟨w,q⟩,r⟩,hm,he⟩
      obtain ⟨hw,hp⟩:=Prod.mk.inj he
      change r=p at hp
      subst r
      have hv := congrArg (fun z=>neighbor z p) hw
      rw [neighbor_reverse] at hv
      change w=neighbor v p at hv
      subst w
      exact ⟨q,hm⟩
    · rintro ⟨q,hq⟩
      exact ⟨((neighbor v p,q),p),hq,by simp only [neighbor_reverse]⟩
  have hb : (∃a∈passes s l,a.1=(v,p)) ↔ ∃q,((v,p),q)∈passes s l := by
    constructor
    · rintro ⟨⟨w,q⟩,hm,he⟩; change w=(v,p) at he; subst w; exact ⟨q,hm⟩
    · rintro ⟨q,hq⟩; exact ⟨((v,p),q),hq,rfl⟩
  simpa only [ha,hb,List.not_mem_nil,or_false] using (Iff.of_eq hs)

lemma neighbor_bool (v : Vertex) (p : Fin 3) : (neighbor v p).2.2= !v.2.2 := by
  unfold neighbor
  split_ifs <;> simp_all

namespace RibbonRectangle
variable {L : ℤ} {M N : ℕ} {s : State} {l : List Bool}

lemma route_interior_match
    (hs : ¬Inside L M N (back s).1) (ht : ¬Inside L M N (terminal next s l).1)
    {v : Vertex} {p : Fin 3} (hv : Inside L M N v) (hw : Inside L M N (neighbor v p)) :
    (∃q,((v,p),q)∈passes s l) ↔ (∃q,((neighbor v p,q),p)∈passes s l) := by
  have h₀ : (v,p)≠s := by
    intro he
    have hh:=congrArg back he
    exact hs (hh ▸ hw)
  have h₁ : (v,p)≠terminal next s l := by
    intro he
    exact ht (congrArg Prod.fst he ▸ hv)
  have hh:=route_shift_iff s l v p
  simpa only [h₀,h₁,false_or,or_false] using hh.symm

lemma ribbon_matches (h : RibbonSimple s l)
    (hs : ¬Inside L M N (back s).1) (ht : ¬Inside L M N (terminal next s l).1) :
    Matches (L:=L) (M:=M) (N:=N) (ribbon h) := by
  intro v p hv hw j
  rw [←neighbor_bool v p]
  fin_cases j
  · change (ribbon h v).Occupied (lane v.2.2 p 0) ↔
      (ribbon h (neighbor v p)).Occupied (lane (neighbor v p).2.2 p 1)
    rw [ribbon_incoming,ribbon_outgoing]
    exact route_interior_match hs ht hv hw
  · change (ribbon h v).Occupied (lane v.2.2 p 1) ↔
      (ribbon h (neighbor v p)).Occupied (lane (neighbor v p).2.2 p 0)
    rw [ribbon_outgoing,ribbon_incoming]
    have hh:=route_interior_match (p:=p) hs ht hw (by simpa only [neighbor_reverse] using hv)
    simpa only [neighbor_reverse] using hh.symm

end RibbonRectangle
end
end CriticalStrip.HoneycombBranch

end OAI
