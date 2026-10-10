import Mathlib
import OAI.Combinatorics.StripMass.BridgeUnfold
import OAI.Combinatorics.StripMass.RibbonWalk

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
namespace HoneycombBranch
open scoped Classical
section TreeMass
open Diagram FiniteBranchTree

 
def bottom (i : ℤ) : State := ((i,0,true),0)
def top (H : ℕ) (i : ℤ) : State := ((i,(H:ℤ)-1,false),0)

lemma finite_columns (p : List Vertex) (i j : ℤ) :
    ∃ L : ℤ, ∃ M : ℕ, 1 ≤ M ∧ L ≤ i ∧ i < L + (M:ℤ) ∧ L ≤ j ∧ j < L + (M:ℤ) ∧
      ∀v∈p,L≤v.1 ∧ v.1<L+(M:ℤ) := by
  let F:= ((bottom i).1::(bottom j).1::p).toFinset
  let B:=F.sup (fun v=>v.1.natAbs)
  have hb (v : Vertex) (hv : v∈F) : -(B:ℤ)≤v.1 ∧ v.1<(B:ℤ)+1 := by
    have hh:=Finset.le_sup (f:=fun v : Vertex=>v.1.natAbs) hv
    have h₁:=(Int.le_natAbs : v.1 ≤ (v.1.natAbs : ℤ))
    have h₂:=(Int.le_natAbs : -v.1 ≤ ((-v.1).natAbs : ℤ))
    rw [Int.natAbs_neg] at h₂
    change v.1.natAbs≤B at hh
    omega
  have hi:=hb (bottom i).1 (by simp [F])
  have hj:=hb (bottom j).1 (by simp [F])
  dsimp only [bottom,Prod.fst] at hi hj
  refine ⟨-(B:ℤ),2*B+1,by omega,by omega,by omega,by omega,by omega,?_⟩
  intro v hv
  have hh:=hb v (by simp only [F,List.mem_toFinset,List.mem_cons]; tauto)
  constructor <;> omega

lemma finite_rows (p : List Vertex) : ∃N : ℕ,1≤N ∧ ∀v∈p,v.2.1<(N:ℤ) := by
  let B:=p.toFinset.sup (fun v=>v.2.1.natAbs)
  refine ⟨B+1,by omega,?_⟩
  intro v hv
  have hh:=Finset.le_sup (f:=fun v : Vertex=>v.2.1.natAbs) (List.mem_toFinset.mpr hv)
  have ha:=(Int.le_natAbs : v.2.1 ≤ (v.2.1.natAbs : ℤ))
  change v.2.1.natAbs≤B at hh
  omega

 

theorem bottom_turn (i j : ℤ) (l : List Bool) (hl : l≠[])
    (hr : RibbonSimple (bottom i) l)
    (hrow : ∀v∈visited Prod.fst next (bottom i) l,0≤v.2.1)
    (ht : terminal next (bottom i) l=back (bottom j)) :
    turn l=if i≤j then -3 else 3 := by
  obtain ⟨L,M,hM,hi₁,hi₂,hj₁,hj₂,hcol⟩:=finite_columns (visited Prod.fst next (bottom i) l) i j
  obtain ⟨N,hN,hupper⟩:=finite_rows (visited Prod.fst next (bottom i) l)
  let c₀ : Fin M:=⟨(i-L).toNat,by omega⟩
  let c₁ : Fin M:=⟨(j-L).toNat,by omega⟩
  have he₀ : (RibbonRectangle.vertex L M N c₀ ⟨0,by omega⟩ true,0)=bottom i := by
    dsimp [RibbonRectangle.vertex,bottom,c₀]
    congr 2
    omega
  have he₁ : (RibbonRectangle.vertex L M N c₁ ⟨0,by omega⟩ true,0)=bottom j := by
    dsimp [RibbonRectangle.vertex,bottom,c₁]
    congr 2
    omega
  have hh:=RibbonRectangle.bottom_turn hM hN c₀ c₁ l hl
    (by rw [he₀]; exact hr) (by
      rw [he₀]
      intro x hx
      have hm:=passes_mem_vertex hx
      exact ⟨(hcol _ hm).1,(hcol _ hm).2,hrow _ hm,hupper _ hm⟩)
    (by rw [he₀,he₁]; exact ht)
  rw [hh]
  have he : c₀≤c₁ ↔ i≤j := by dsimp [c₀,c₁]; simp only [Fin.le_iff_val_le_val]; omega
  simp only [he]

lemma closed_cycle_true_turn (i : ℤ) (stem tail : List Bool)
    (hn : (visited Prod.fst next (bottom i) (stem++true::tail)).Nodup)
    (hrow : ∀v∈visited Prod.fst next (bottom i) (stem++true::tail),0≤v.2.1)
    (hc : terminal next (bottom i) (stem++true::tail)=
      ((terminal next (bottom i) stem).1,outgoing (terminal next (bottom i) stem).2 false)) :
    turn (true::tail)= -4 := by
  have hh:=bottom_turn i i (closeStem stem tail) (by simp [closeStem])
    (closeStem_simple _ stem tail hn hc)
    (fun v hv=>hrow v (closeStem_visits _ stem tail hc v hv))
    (closeStem_terminal _ stem tail hc)
  rw [ite_eq_left le_rfl,closeStem_turn] at hh
  omega

 

theorem collision_cycle_turn (D : Finset Vertex) (i : ℤ) (stem : List Bool)
    (b : Bool) (tail : List Bool) (hD : ∀v∈D,0≤v.2.1)
    (hl : stem++b::tail∈words D (bottom i))
    (hc : (terminal next (bottom i) (stem++b::tail)).1=(terminal next (bottom i) stem).1) :
    turn (b::tail)%8=4 := by
  have hs : (back (bottom i)).1∉D := by
    intro h
    have hh:=hD _ h
    norm_num [bottom,back,neighbor] at hh
  have hn:=visited_nodup Prod.fst next hl
  have hrow:=fun v hv=>hD v (visited_mem_domain Prod.fst next hl v hv)
  have h₀:=collision_port_not_stem D (bottom i) stem b tail hs hl hc
  have hn' : (visited Prod.fst next (terminal next (bottom i) stem) (b::tail)).Nodup := by
    rw [visited_append] at hn
    exact hn.of_append_right
  have hc' := hc
  rw [terminal_append] at hc'
  have h₁:=collision_port_not_first _ b tail hn' hc'
  have hq:=third_port (terminal next (bottom i) stem).2
    (terminal next (bottom i) (stem++b::tail)).2 b h₀ (by simpa only [terminal_append] using h₁)
  cases b with
  | true=>
    have ht:=closed_cycle_true_turn i stem tail hn hrow (Prod.ext hc hq)
    rw [ht]
    decide
  | false=>
    have hcfull : (terminal next (bottom i) (stem++false::tail)).1∈D := by
      rw [hc]
      apply visited_mem_domain Prod.fst next hl
      rw [visited_append]
      exact List.mem_append_right _ List.mem_cons_self
    have hr:=prefix_reverseCycle_mem D (bottom i) stem false tail hl hc h₀ (by simpa only [terminal_append] using h₁)
    have ht:=terminal_reverseCycle (terminal next (bottom i) stem) false tail hc'
      (by simpa only [terminal_append] using h₀) h₁
    have he : terminal next (bottom i) (stem++true::reverseTurns tail)=
        ((terminal next (bottom i) stem).1,outgoing (terminal next (bottom i) stem).2 false) := by
      rw [terminal_append]
      exact ht
    have hh:=closed_cycle_true_turn i stem (reverseTurns tail)
      (visited_nodup Prod.fst next hr)
      (fun v hv=>hD v (visited_mem_domain Prod.fst next hr v hv)) he
    change turn (reverseCycle (false::tail))= -4 at hh
    rw [turn_reverseCycle] at hh
    omega

 

theorem collisionMass_zero (D : Finset Vertex) (i : ℤ) (hD : ∀v∈D,0≤v.2.1) :
    collisionMass Prod.fst next factor D (bottom i)=0 := by
  apply collisionMass_zero_of_turns
  · intro h
    have hh:=hD _ h
    norm_num [bottom,back,neighbor] at hh
  · intro l hl ht
    obtain ⟨stem,b,tail,rfl,hc⟩:=collision_split D (bottom i) l hl ht
    have he : collisionIndex (bottom i) (stem++b::tail)=stem.length := by
      rw [collisionIndex,hc,collision_index_eq _ _ _ _ (visited_nodup Prod.fst next hl)]
    rw [he,List.drop_left]
    exact collision_cycle_turn D i stem b tail hD hl hc

theorem finite_boundary_flux (D : Finset Vertex) (i : ℤ) (hD : ∀v∈D,0≤v.2.1) :
    exitMass Prod.fst next factor D (bottom i)=1 := by
  have h:=exit_plus_collision D (bottom i)
  rwa [collisionMass_zero D i hD,add_zero] at h

end TreeMass

section BoundaryConnection
open Diagram Diagram.TurnNetwork Diagram.TurnDisk FiniteBranchTree
namespace RibbonRectangle
variable {L : ℤ} {M N : ℕ} (hM : 1≤M) (hN : 1≤N)

lemma top_outside (c : Fin M) :
    ¬Inside L M N (back (vertex L M N c ⟨N-1,by omega⟩ false,0)).1 := by
  have he : ((N-1:ℕ):ℤ)+1=(N:ℤ) := by omega
  simp [Inside,back,neighbor,vertex,he]

include hM in
lemma top_turn (c₀ c₁ : Fin M) (l : List Bool) (hl : l≠[])
    (hr : RibbonSimple (vertex L M N c₀ ⟨0,by omega⟩ true,0) l)
    (hI : ∀x∈passes (vertex L M N c₀ ⟨0,by omega⟩ true,0) l,Inside L M N x.1.1)
    (ht : terminal next (vertex L M N c₀ ⟨0,by omega⟩ true,0) l=
      back (vertex L M N c₁ ⟨N-1,by omega⟩ false,0)) : turn l=0 := by
  let s : State:=(vertex L M N c₀ ⟨0,by omega⟩ true,0)
  have hm:=ribbon_matches (L:=L) (M:=M) (N:=N) hr (bottom_outside hN c₀)
    (by rw [ht]; exact top_outside hN c₁)
  have hi:=bottom_connector hM hN (ribbon hr) hm c₀ 0 (first_occupied s l hl hr)
  have heV : (back (terminal next s l)).1=vertex L M N c₁ ⟨N-1,by omega⟩ false := by rw [ht,back_back]
  have heP : (terminal next s l).2=0 := by rw [ht]; rfl
  have heNode : node L M N (last_inside s l hl hI)
        (lane (back (terminal next s l)).1.2.2 (terminal next s l).2 1)=
      node L M N (vertex_inside L M N c₁ ⟨N-1,by omega⟩ false) (lane false 0 1) := by
    rw [node_of_vertex _ heV,at_vertex,heV,heP]
    rfl
  have hbd : boundary (L:=L) hM hN (ribbon hr) (TurnRectangle.northSlot hM hN c₁.isLt 1)=
      node L M N (last_inside s l hl hI)
        (lane (back (terminal next s l)).1.2.2 (terminal next s l).2 1) := by
    rw [heNode,top_boundary]
  have hlt : bottomIndex (N:=N) c₀ 0 < TurnRectangle.northSlot hM hN c₁.isLt 1 := by
    have hh:=bottomIndex_lt (N:=N) c₀ 0
    rw [Fin.lt_def,TurnRectangle.northSlot_val]
    omega
  have hh:=endpoint_turn hM hN s l hl hr (vertex_inside _ _ _ _ _ _) hI hm
    (bottomIndex c₀ 0) (TurnRectangle.northSlot hM hN c₁.isLt 1) (ne_of_lt hlt) hi.1
    (by rw [hbd])
    (fun P hP=>⟨hi.2 P hP,by rw [hbd,sub_self]⟩)
  rw [hh,Pairing.arcTurn,bottom_gauge,top_gauge,Pairing.turnOrder,ite_eq_left hlt]
  norm_num

end RibbonRectangle

 
theorem top_turn (H : ℕ) (hH : 1≤H) (i j : ℤ) (l : List Bool) (hl : l≠[])
    (hn : (visited Prod.fst next (bottom i) l).Nodup)
    (hrow : ∀v∈visited Prod.fst next (bottom i) l,0≤v.2.1 ∧ v.2.1<(H:ℤ))
    (ht : terminal next (bottom i) l=back (top H j)) : turn l=0 := by
  obtain ⟨L,M,hM,hi₁,hi₂,hj₁,hj₂,hcol⟩:=finite_columns (visited Prod.fst next (bottom i) l) i j
  let c₀ : Fin M:=⟨(i-L).toNat,by omega⟩
  let c₁ : Fin M:=⟨(j-L).toNat,by omega⟩
  have he₀ : (RibbonRectangle.vertex L M H c₀ ⟨0,by omega⟩ true,0)=bottom i := by
    dsimp [RibbonRectangle.vertex,bottom,c₀]
    congr 2
    omega
  have he₁ : (RibbonRectangle.vertex L M H c₁ ⟨H-1,by omega⟩ false,0)=top H j := by
    dsimp [RibbonRectangle.vertex,top,c₁]
    congr 2
    · omega
    · ext <;> dsimp
      omega
  apply RibbonRectangle.top_turn hM hH c₀ c₁ l hl
    (by rw [he₀]; exact ribbonSimple_of_nodup hn) (by
      rw [he₀]
      intro x hx
      have hm:=passes_mem_vertex hx
      exact ⟨(hcol _ hm).1,(hcol _ hm).2,(hrow _ hm).1,(hrow _ hm).2⟩)
    (by rw [he₀,he₁]; exact ht)

end BoundaryConnection

open FiniteBranchTree

 

lemma word_unique (s : State) (l m : List Bool)
    (hv : visited Prod.fst next s l=visited Prod.fst next s m)
    (ht : terminal next s l=terminal next s m) : l=m := by
  induction l generalizing s m with
  | nil=>
    have hh:=congrArg List.length hv
    have hm : m.length=0 := by simpa only [visited_length,List.length_nil] using hh.symm
    exact (List.eq_nil_of_length_eq_zero hm).symm
  | cons b l ih=>
    cases m with
    | nil=>have hh:=congrArg List.length hv; simp only [visited_length,List.length_cons,List.length_nil] at hh; omega
    | cons c m=>
      have htail : visited Prod.fst next (next s b) l=visited Prod.fst next (next s c) m := (List.cons.inj hv).2
      have hlen : l.length=m.length := by simpa only [visited_length] using congrArg List.length htail
      have hbc : b=c := by
        apply next_injective s
        by_cases hl : l=[]
        · have hm : m=[] := by apply List.eq_nil_of_length_eq_zero; simpa only [hl,List.length_nil] using hlen.symm
          simpa only [hl,hm,terminal] using congrArg Prod.fst ht
        · have hm : m≠[] := by intro hh; apply hl; apply List.eq_nil_of_length_eq_zero; simpa only [hh,List.length_nil] using hlen
          have hh:=congrArg List.head? htail
          rw [visited_head _ _ _ _ hl,visited_head _ _ _ _ hm] at hh
          exact Option.some.inj hh
      subst c
      exact congrArg (List.cons b) (ih (next s b) m htail ht)

 

lemma exists_word (s t : State) (p : List Vertex)
    (hh : p.head?=some s.1) (hl : p.getLast?=some (back t).1)
    (hn : p.Nodup) (hc : p.IsChain (fun v w=>∃q : Fin 3,neighbor v q=w))
    (hi : (back s).1∉p) (ho : t.1∉p) (hne : s≠back t) :
    ∃l : List Bool, visited Prod.fst next s l=p ∧ terminal next s l=t := by
  induction p generalizing s with
  | nil=>simp only [List.head?_nil,reduceCtorEq] at hh
  | cons v p ih=>
    have he : v=s.1 := Option.some.inj hh
    subst v
    cases p with
    | nil=>
      have hs : s.1=(back t).1 := by simpa only [List.getLast?_cons,List.getLast?_nil,Option.getD_none,Option.some.injEq] using hl
      have hport : t.2≠s.2 := by
        intro ht
        exact hne (Prod.ext hs ht.symm)
      obtain ⟨b,hb,_⟩:=outgoing_exhaust s.2 t.2 hport
      refine ⟨[b],rfl,?_⟩
      change next s b=t
      dsimp [next]
      rw [hb,hs]
      exact back_back t
    | cons w p=>
      have had : ∃q : Fin 3,neighbor s.1 q=w := (List.isChain_cons_cons.mp hc).1
      obtain ⟨q,hq⟩:=had
      have hqne : q≠s.2 := by
        intro he
        have hew : w=(back s).1 := by rw [←hq,he]; rfl
        exact hi (hew ▸ List.mem_cons_of_mem _ List.mem_cons_self)
      obtain ⟨b,hb,_⟩:=outgoing_exhaust s.2 q hqne
      have hnext : (next s b).1=w := by dsimp [next]; rw [hb,hq]
      have hsnew : next s b≠back t := by
        intro he
        have hh : t.1=s.1 := by
          have he':=congrArg back he
          rw [back_back,back_next] at he'
          exact (congrArg Prod.fst he').symm
        exact ho (hh ▸ List.mem_cons_self)
      obtain ⟨l,hv,ht⟩:=ih (next s b) (by simp only [List.head?_cons,hnext])
        (by simpa only [List.getLast?_cons_cons] using hl) hn.tail
        (List.isChain_cons_cons.mp hc).2
        (by rw [back_next]; exact (List.nodup_cons.mp hn).1)
        (fun h=>ho (List.mem_cons_of_mem _ h)) hsnew
      exact ⟨b::l,by simp only [visited,hv],ht⟩

lemma word_nonempty_of_head (s : State) (l : List Bool) (p : List Vertex)
    (hh : p.head?=some s.1) (hv : visited Prod.fst next s l=p) : l≠[] := by
  intro hl
  subst l
  change []=p at hv
  rw [←hv,List.head?_nil] at hh
  contradiction

lemma word_terminal_ne_source {s : State} {l : List Bool} (hl : l≠[])
    (hn : (visited Prod.fst next s l).Nodup) : terminal next s l≠back s := by
  cases l with
  | nil=>exact (hl rfl).elim
  | cons b l=>
    intro ht
    cases l with
    | nil=>
      have hh:=congrArg Prod.snd ht
      exact outgoing_ne s.2 b hh
    | cons c l=>
      have hm:=lastVisited_mem (next s b) (c::l) (by simp)
      change (back (terminal next s (b::c::l))).1∈_ at hm
      rw [ht,back_back] at hm
      exact (List.nodup_cons.mp hn).1 hm

 

def retractVertex (v : Vertex) : Triangle := (v.1,v.2.1.toNat,v.2.2)

lemma retract_embed (v : Triangle) : retractVertex (embedTriangle v)=v := by
  rcases v with ⟨i,r,b⟩
  simp [retractVertex,embedTriangle]
lemma embed_retract (v : Vertex) (h : 0≤v.2.1) : embedTriangle (retractVertex v)=v := by
  rcases v with ⟨i,r,b⟩
  simp only [retractVertex,embedTriangle,Int.toNat_of_nonneg h]

lemma visited_head_last (s : State) (l : List Bool) (hl : l≠[]) :
    (visited Prod.fst next s l).head?=some s.1 ∧
    (visited Prod.fst next s l).getLast?=some (back (terminal next s l)).1 := by
  refine ⟨visited_head _ _ _ _ hl,?_⟩
  induction l generalizing s with
  | nil=>exact (hl rfl).elim
  | cons b l ih=>
    cases l with
    | nil=>simp only [visited,terminal,back_next,List.getLast?_singleton]
    | cons c l=>
      simpa only [visited,List.getLast?_cons_cons,terminal] using ih (next s b) (by simp)

lemma visited_retract_path (H : ℕ) (a b : Triangle) (s : State) (l : List Bool) (hl : l≠[])
    (hs : s.1=embedTriangle a) (ht : (back (terminal next s l)).1=embedTriangle b)
    (hn : (visited Prod.fst next s l).Nodup)
    (hband : ∀v∈visited Prod.fst next s l,0≤v.2.1 ∧ v.2.1<(H:ℤ)) :
    PathBetween H a b ((visited Prod.fst next s l).map retractVertex) := by
  have hheads:=visited_head_last s l hl
  have he : ((visited Prod.fst next s l).map retractVertex).map embedTriangle=visited Prod.fst next s l := by
    rw [List.map_map]
    conv_rhs => rw [←List.map_id (visited Prod.fst next s l)]
    apply List.map_congr_left
    intro v hv
    exact embed_retract v (hband v hv).1
  have hc := visited_chain s l
  have hc' : (((visited Prod.fst next s l).map retractVertex).map embedTriangle).IsChain
      (fun v w=>∃q : Fin 3,neighbor v q=w) := by rw [he]; exact hc
  have ha:= (List.isChain_map _).mp hc'
  refine ⟨?_,?_,?_,ha.imp (fun v w h=>(adjacent_iff v w).mpr h),?_⟩
  · rw [List.head?_map,hheads.1,Option.map_some,hs,retract_embed]
  · rw [List.getLast?_map,hheads.2,Option.map_some,ht,retract_embed]
  · apply List.Nodup.of_map (f:=embedTriangle)
    rw [he]
    exact hn
  · intro v hv
    obtain ⟨w,hw,rfl⟩:=List.mem_map.mp hv
    have hb:=hband w hw
    change w.2.1.toNat<H
    omega

end HoneycombBranch
open scoped Classical BigOperators

 

lemma exists_column_to_bottom (H : ℕ) (i : ℤ) (j : ℕ) (b : Bool) (hj : j<H) :
    ∃ p : List Triangle, PathBetween H (i,j,b) (up i 0) p ∧
      (∀ v∈p,v.1=i) ∧ p.length≤2*H := by
  let a : Fin (2*H):=⟨2*j+(if b then 0 else 1),by split <;> omega⟩
  let z : Fin (2*H):=⟨0,by omega⟩
  obtain ⟨w,hw⟩:=((SimpleGraph.pathGraph_preconnected (2*H)) a z).exists_isPath
  let f : Fin (2*H)→Triangle:=fun r=>ladderVertex i r.val
  have hf : Function.Injective f := (ladderVertex_injective i).comp Fin.val_injective
  refine ⟨w.support.map f,⟨?_,?_,hw.support_nodup.map hf,?_,?_⟩,?_,?_⟩
  · simp only [List.head?_map,List.head?_eq_some_head w.support_ne_nil,w.head_support,Option.map_some]
    cases b <;> simp [f,a,ladderVertex]
    omega
  · simp [List.getLast?_map,List.getLast?_eq_some_getLast w.support_ne_nil,w.getLast_support,f,z,ladderVertex,up]
  · apply (List.isChain_map _).mpr
    apply w.isChain_adj_support.imp
    intro v w h
    rcases SimpleGraph.pathGraph_adj.mp h with hh|hh
    · change adjacent (ladderVertex i v.val) (ladderVertex i w.val)
      rw [←hh]
      exact ladderVertex_adjacent i _
    · change adjacent (ladderVertex i v.val) (ladderVertex i w.val)
      rw [←hh]
      exact adjacent_symmetric.symm _ _ (ladderVertex_adjacent i _)
  · intro v hv
    obtain ⟨r,_,rfl⟩:=List.mem_map.mp hv
    change r.val/2<H
    have :=r.isLt
    omega
  · intro v hv
    obtain ⟨r,_,rfl⟩:=List.mem_map.mp hv
    rfl
  · rw [List.length_map]
    have :=List.Nodup.length_le_card hw.support_nodup
    simpa only [Fintype.card_fin] using this

namespace HoneycombBranch
open FiniteBranchTree

lemma terminal_eq_of_visited {s : State} {l m : List Bool} (hl : l≠[]) (hm : m≠[])
    (hv : visited Prod.fst next s l=visited Prod.fst next s m)
    (hp : (terminal next s l).2=(terminal next s m).2) :
    terminal next s l=terminal next s m := by
  have he:=congrArg List.getLast? hv
  rw [(visited_head_last s l hl).2,(visited_head_last s m hm).2] at he
  have hb : back (terminal next s l)=back (terminal next s m) := Prod.ext (Option.some.inj he) hp
  have ht:=congrArg back hb
  simpa only [back_back] using ht

 

def SideWord (H : ℕ) (i k : ℤ) := {l : List Bool //
  l≠[] ∧ (visited Prod.fst next (bottom i) l).Nodup ∧
  (∀v∈visited Prod.fst next (bottom i) l,0≤v.2.1 ∧ v.2.1<(H:ℤ) ∧ v.1≠k) ∧
  (terminal next (bottom i) l).2=1 ∧ (terminal next (bottom i) l).1.1=k}

namespace SideWord
variable {H : ℕ} {i k : ℤ}

def state (x : SideWord H i k) : State:=terminal next (bottom i) x.val

def path (x : SideWord H i k) : List Triangle:=
  (visited Prod.fst next (bottom i) x.val).map retractVertex

lemma band (x : SideWord H i k) : 0≤x.state.1.2.1 ∧ x.state.1.2.1<(H:ℤ) := by
  have hm:=lastVisited_mem (bottom i) x.val x.property.1
  have hb:=x.property.2.2.1 _ hm
  have he : (back x.state).1.2.1=x.state.1.2.1 := by
    dsimp [back,state]
    rw [x.property.2.2.2.1]
    dsimp [neighbor]
    split <;> rfl
  exact he ▸ ⟨hb.1,hb.2.1⟩

lemma path_spec (x : SideWord H i k) :
    PathBetween H (up i 0) (retractVertex (back x.state).1) x.path := by
  apply visited_retract_path H _ _ (bottom i) x.val x.property.1 rfl
    (by apply (embed_retract _ _).symm; exact (x.property.2.2.1 _ (lastVisited_mem _ _ x.property.1)).1)
    x.property.2.1
  intro v hv
  exact ⟨(x.property.2.2.1 v hv).1,(x.property.2.2.1 v hv).2.1⟩

lemma path_no_column (x : SideWord H i k) : ∀v∈x.path,v.1≠k := by
  intro v hv
  obtain ⟨w,hw,rfl⟩:=List.mem_map.mp hv
  exact (x.property.2.2.1 w hw).2.2

lemma connector_exists (x : SideWord H i k) :
    ∃p : List Triangle, PathBetween H (retractVertex x.state.1) (up k 0) p ∧
      (∀v∈p,v.1=k) ∧ p.length≤2*H := by
  have hj : x.state.1.2.1.toNat<H := by have :=x.band; omega
  have hh:=exists_column_to_bottom H k x.state.1.2.1.toNat x.state.1.2.2 hj
  have he : retractVertex x.state.1=(k,x.state.1.2.1.toNat,x.state.1.2.2) := by
    dsimp [retractVertex,state]
    rw [x.property.2.2.2.2]
  rwa [he]

 def connector (x : SideWord H i k) : List Triangle:=x.connector_exists.choose
 lemma connector_spec (x : SideWord H i k) :
    PathBetween H (retractVertex x.state.1) (up k 0) x.connector ∧
      (∀v∈x.connector,v.1=k) ∧ x.connector.length≤2*H := x.connector_exists.choose_spec

 def arch (x : SideWord H i k) : List Triangle:=x.path++x.connector

lemma arch_spec (x : SideWord H i k) : PathBetween H (up i 0) (up k 0) x.arch := by
  apply x.path_spec.append x.connector_spec.1
  · apply List.disjoint_left.mpr
    intro v hv hv'
    exact x.path_no_column v hv (x.connector_spec.2.1 v hv')
  · apply (adjacent_iff _ _).mpr
    have hb : 0≤(back x.state).1.2.1 := (x.property.2.2.1 _ (lastVisited_mem _ _ x.property.1)).1
    rw [embed_retract _ hb,embed_retract _ x.band.1]
    exact ⟨x.state.2,neighbor_reverse _ _⟩

lemma arch_filter (x : SideWord H i k) :
    x.arch.filter (fun v=>decide (v.1≠k))=x.path := by
  have hp : x.path.filter (fun v=>decide (v.1≠k))=x.path :=
    List.filter_eq_self.mpr (fun v hv=>by simpa using x.path_no_column v hv)
  have hc : x.connector.filter (fun v=>decide (v.1≠k))=[] :=
    List.filter_eq_nil_iff.mpr (fun v hv=>by simp [x.connector_spec.2.1 v hv])
  simp only [arch,List.filter_append,hp,hc,List.append_nil]

lemma path_embed (x : SideWord H i k) :
    x.path.map embedTriangle=visited Prod.fst next (bottom i) x.val := by
  rw [path,List.map_map]
  conv_rhs => rw [←List.map_id (visited Prod.fst next (bottom i) x.val)]
  apply List.map_congr_left
  intro v hv
  exact embed_retract v (x.property.2.2.1 v hv).1

lemma arch_injective : Function.Injective (arch (H:=H) (i:=i) (k:=k)) := by
  intro x y he
  have hp : x.path=y.path := by rw [←x.arch_filter,he,y.arch_filter]
  have hv : visited Prod.fst next (bottom i) x.val=visited Prod.fst next (bottom i) y.val := by
    rw [←x.path_embed,hp,y.path_embed]
  apply Subtype.ext
  apply word_unique _ _ _ hv
  apply terminal_eq_of_visited x.property.1 y.property.1 hv
  exact x.property.2.2.2.1.trans y.property.2.2.2.1.symm

lemma arch_length (x : SideWord H i k) : x.arch.length≤x.val.length+2*H := by
  simp only [arch,List.length_append,path,List.length_map,visited_length]
  have :=x.connector_spec.2.2
  omega

lemma weighted_bound (hik : i≠k) (x : SideWord H i k) :
    rho^(2*H)*rho^x.val.length≤betweenArchWeight H i k x.arch := by
  rw [betweenArchWeight,ite_eq_left ⟨hik,x.arch_spec⟩,←pow_add]
  exact pow_le_pow_of_le_one rho_pos.le BridgePath.rho_le_one (by have:=x.arch_length; omega)

lemma sum_le (hH : 1≤H) (hik : i≠k) (F : Finset (SideWord H i k)) :
    ∑ x∈F,rho^x.val.length ≤ (rho^(2*H))⁻¹*K H (k-i) := by
  have hs := (summable_betweenArchWeight_iff H i k).mpr ((stripSumsFinite hH).1 _)
  have hi : Summable (fun x : SideWord H i k=>betweenArchWeight H i k x.arch) :=
    hs.comp_injective arch_injective
  have hh : rho^(2*H)*(∑ x∈F,rho^x.val.length)≤K H (k-i) := by
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ x∈F,betweenArchWeight H i k x.arch := Finset.sum_le_sum (fun x _=>weighted_bound hik x)
      _ ≤ ∑' x : SideWord H i k,betweenArchWeight H i k x.arch :=
        hi.sum_le_tsum F (fun x _=>betweenArchWeight_nonneg _ _ _ _)
      _ ≤ ∑' p,betweenArchWeight H i k p :=
        tsum_comp_le_tsum_of_inj hs (betweenArchWeight_nonneg H i k) arch_injective
      _ = K H (k-i) := betweenArchKernel_eq H i k
  have hh' : (∑ x∈F,rho^x.val.length)≤K H (k-i)/rho^(2*H) :=
    (le_div_iff₀ (pow_pos rho_pos _)).mpr (by simpa only [mul_comm] using hh)
  simpa only [div_eq_mul_inv,mul_comm] using hh'

end SideWord
end HoneycombBranch
end
end CriticalStrip

end OAI
