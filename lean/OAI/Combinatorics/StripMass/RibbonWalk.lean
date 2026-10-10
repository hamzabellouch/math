import Mathlib
import OAI.Combinatorics.StripMass.RibbonLocal

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.HoneycombBranch
noncomputable section
open scoped Classical
open Diagram FiniteBranchTree
namespace RibbonRectangle

variable {L : ℤ} {M N : ℕ} (hM : 1≤M) (hN : 1≤N) (F : Vertex → Pairing 6)
  (hm : Matches (L:=L) (M:=M) (N:=N) F)
include hm

lemma route_reach (s : State) (l : List Bool) (hs : Inside L M N s.1)
    (hI : ∀x∈passes s l,Inside L M N x.1.1)
    (hA : ∀x∈passes s l,(F x.1.1).Adj (lane x.1.1.2.2 x.1.2 0) (lane x.1.1.2.2 x.2 1))
    {v : Vertex} {p q : Fin 3} (hp : ((v,p),q)∈passes s l) :
    Relation.ReflTransGen (graph (L:=L) hM hN F)
      (node L M N hs (lane s.1.2.2 s.2 0))
      (node L M N (hI _ hp) (lane v.2.2 p 0)) ∧
    Relation.ReflTransGen (graph (L:=L) hM hN F)
      (node L M N hs (lane s.1.2.2 s.2 0))
      (node L M N (hI _ hp) (lane v.2.2 q 1)) := by
  induction l generalizing s with
  | nil => simp only [passes,List.not_mem_nil] at hp
  | cons b l ih =>
    have ha:=hA _ (List.mem_cons_self)
    have ea:=arc_edge hM hN F hs ha
    rcases List.mem_cons.mp hp with he|hp
    · have he₁:=congrArg (fun z : State × Fin 3=>z.1.1) he
      have he₂:=congrArg (fun z : State × Fin 3=>z.1.2) he
      have he₃:=congrArg (fun z : State × Fin 3=>z.2) he
      change v=s.1 at he₁; change p=s.2 at he₂; change q=outgoing s.2 b at he₃
      subst v p q
      exact ⟨.refl,.single ea⟩
    · cases l with
      | nil => simp only [passes,List.not_mem_nil] at hp
      | cons c l =>
        have hs' : Inside L M N (next s b).1 := hI _ (by exact List.mem_cons_of_mem _ List.mem_cons_self)
        have ew:= (wire hM hN F hm hs (outgoing s.2 b) 1 hs' ⟨_,ha.symm⟩).1
        have heB : (!s.1.2.2)=(next s b).1.2.2 := (neighbor_bool s.1 (outgoing s.2 b)).symm
        have heL : (1-(1:Fin 2))=0 := rfl
        rw [heB,heL] at ew
        obtain ⟨hi,ho⟩:=ih (next s b) hs'
          (fun x hx=>hI x (List.mem_cons_of_mem _ hx))
          (fun x hx=>hA x (List.mem_cons_of_mem _ hx)) hp
        exact ⟨(Relation.ReflTransGen.single ea).trans ((Relation.ReflTransGen.single ew).trans hi),
          (Relation.ReflTransGen.single ea).trans ((Relation.ReflTransGen.single ew).trans ho)⟩

omit hm in
lemma last_inside (s : State) (l : List Bool) (hl : l≠[])
    (hI : ∀x∈passes s l,Inside L M N x.1.1) :
    Inside L M N (back (terminal next s l)).1 := by
  have hh:=lastVisited_mem s l hl
  rw [←passes_vertices] at hh
  obtain ⟨x,hx,he⟩:=List.mem_map.mp hh
  exact he ▸ hI x hx

lemma route_turn (s : State) (l : List Bool) (hl : l≠[]) (hs : Inside L M N s.1)
    (hI : ∀x∈passes s l,Inside L M N x.1.1)
    (hA : ∀x∈passes s l,(F x.1.1).Adj (lane x.1.1.2.2 x.1.2 0) (lane x.1.1.2.2 x.2 1))
    (P : Diagram.TurnNetwork.Node (Diagram.TurnRectangle.ports M N) (M*N) → ℤ)
    (hP : ∀v w, graph (L:=L) hM hN F v w → P w-P v=turnEdge (L:=L) hM hN F v w) :
    P (node L M N (last_inside s l hl hI)
      (lane (back (terminal next s l)).1.2.2 (terminal next s l).2 1)) -
    P (node L M N hs (lane s.1.2.2 s.2 0))=turn l := by
  induction l generalizing s with
  | nil => exact (hl rfl).elim
  | cons b l ih =>
    have ha:=hA _ List.mem_cons_self
    have hp:=hP _ _ (arc_edge hM hN F hs ha)
    rw [arc_turn hM hN F hs ha,local_turn] at hp
    cases l with
    | nil =>
      simp only [terminal,back_next]
      simpa only [turn,add_zero,next] using hp
    | cons c l =>
      have hs' : Inside L M N (next s b).1 := hI _ (List.mem_cons_of_mem _ List.mem_cons_self)
      have ew:= wire hM hN F hm hs (outgoing s.2 b) 1 hs' ⟨_,ha.symm⟩
      have heB : (!s.1.2.2)=(next s b).1.2.2 := (neighbor_bool s.1 (outgoing s.2 b)).symm
      have heL : (1-(1:Fin 2))=0 := rfl
      rw [heB,heL] at ew
      have hw:= (hP _ _ ew.1).trans ew.2
      have ht:=ih (next s b) (by simp)
        hs' (fun x hx=>hI x (List.mem_cons_of_mem _ hx))
        (fun x hx=>hA x (List.mem_cons_of_mem _ hx))
      change _=sign b+turn (c::l)
      change _-P (node L M N hs' (lane (next s b).1.2.2 (next s b).2 0))=turn (c::l) at ht
      change P (node L M N hs' (lane (next s b).1.2.2 (next s b).2 0))-_ =0 at hw
      dsimp only [terminal] at ht ⊢
      dsimp only [next] at hw ht ⊢
      dsimp only at hp
      omega

end RibbonRectangle
end

 

 

noncomputable section
open scoped Classical
open Diagram Diagram.TurnNetwork Diagram.TurnDisk FiniteBranchTree
namespace RibbonRectangle

variable {L : ℤ} {M N : ℕ}

section BoundaryConnection
lemma node_occupied (F : Vertex → Pairing 6) {v : Vertex} (h : Inside L M N v) (i : Fin 6) :
    TurnNetwork.Occupied (start (L:=L) F) (up L N F) (down L N F) (M*N) (node L M N h i) ↔
      (F v).Occupied i := by
  obtain ⟨c,r,b,rfl⟩ : ∃ c r b,v=vertex L M N c r b :=
    ⟨col h,row h,v.2.2,(vertex_col_row h).symm⟩
  rw [at_vertex]
  cases b
  · change (down L N F (c.val*N+r.val)).Occupied i ↔ _
    rw [down_time]
  · change (up L N F (c.val*N+r.val)).Occupied i ↔ _
    rw [up_time]

lemma cover_node (hN : 1≤N) (x : Node (TurnRectangle.ports M N) (M*N)) :
    (∃i,x=.inl i) ∨ ∃ (v : Vertex) (h : Inside L M N v),∃i, x=node L M N h i := by
  rcases x with i|⟨t,z⟩
  · exact Or.inl ⟨i,rfl⟩
  · have hc : t.val/N<M := (Nat.div_lt_iff_lt_mul (by omega)).mpr t.isLt
    have hr : t.val%N<N := Nat.mod_lt _ (by omega)
    let c : Fin M:=⟨t.val/N,hc⟩
    let r : Fin N:=⟨t.val%N,hr⟩
    have he : (⟨c.val*N+r.val,TurnRectangle.time_lt r.isLt c.isLt⟩:Fin (M*N))=t := by
      apply Fin.ext
      change (t.val/N)*N+t.val%N=t.val
      simpa only [Nat.mul_comm] using Nat.div_add_mod t.val N
    rcases z with i|i
    · refine Or.inr ⟨vertex L M N c r true,vertex_inside _ _ _ _ _ _,i,?_⟩
      rw [at_vertex]
      change Sum.inr (t,Sum.inl i)=Sum.inr (⟨c.val*N+r.val,_⟩,Sum.inl i)
      rw [he]
    · refine Or.inr ⟨vertex L M N c r false,vertex_inside _ _ _ _ _ _,i,?_⟩
      rw [at_vertex]
      change Sum.inr (t,Sum.inr i)=Sum.inr (⟨c.val*N+r.val,_⟩,Sum.inr i)
      rw [he]

variable (hM : 1≤M) (hN : 1≤N)

lemma starter_drains (F : Vertex → Pairing 6) (i : Fin (TurnRectangle.ports M N))
    (hi : (start (L:=L) F).Occupied i) :
    ∃j,Relation.ReflTransGen (graph (L:=L) hM hN F) (.inl i) (boundary (L:=L) hM hN F j) := by
  have hb (j : Fin (TurnRectangle.width M N)) : boundary (L:=L) hM hN F
      (TurnStarter.left (TurnRectangle.width M N) j)=.inl (TurnStarter.left (TurnRectangle.width M N) j) :=
    TurnRectangle.retained_boundary hM hN (start (L:=L) F) (TurnRectangle.starterGauge M N)
      (up L N F) (down L N F) (M*N) _ (by change TurnRectangle.width M N-1-j.val<TurnRectangle.width M N; omega)
  rcases TurnStarter.cover (TurnRectangle.width M N) i with ⟨j,rfl⟩|⟨j,rfl⟩
  · refine ⟨TurnStarter.left _ j,?_⟩
    rw [hb]
  · have hActive := (TurnStarter.occupied_right _ _ _).mp hi
    refine ⟨TurnStarter.left _ j,?_⟩
    rw [hb]
    exact .single (symm (TurnRectangle.starter_edge hM hN (up L N F) (down L N F) hActive))

lemma ribbon_drains (s : State) (l : List Bool) (hr : RibbonSimple s l)
    (hs : Inside L M N s.1) (hI : ∀x∈passes s l,Inside L M N x.1.1)
    (hm : Matches (L:=L) (M:=M) (N:=N) (ribbon hr))
    (i₀ : Fin (TurnRectangle.ports M N))
    (h₀ : Relation.ReflTransGen (graph (L:=L) hM hN (ribbon hr))
      (boundary (L:=L) hM hN (ribbon hr) i₀) (node L M N hs (lane s.1.2.2 s.2 0))) :
    Graph.DrainsBoundary (graph (L:=L) hM hN (ribbon hr)) (boundary (L:=L) hM hN (ribbon hr)) := by
  have hm':=TurnRectangle.physical_matches hM hN (start (L:=L) (ribbon hr))
    (up L N (ribbon hr)) (down L N (ribbon hr)) (physical_matches hM hN (ribbon hr) hm)
  intro v w hvw
  have ho := (TurnNetwork.occupied_iff_used _ _ _ _ _ _ (M*N) hm' v).mp ⟨w,hvw⟩
  rcases cover_node (L:=L) hN v with ⟨i,rfl⟩|⟨u,hu,j,rfl⟩
  · exact starter_drains hM hN (ribbon hr) i ho
  · rw [node_occupied,ribbon_occupied] at ho
    obtain ⟨p,q,hp,hj⟩:=ho
    obtain ⟨hri,hro⟩:=route_reach hM hN (ribbon hr) hm s l hs hI
      (fun x hx=>ribbon_arc hr hx) hp
    refine ⟨i₀,?_⟩
    rcases hj with rfl|rfl
    · exact ConnectivityCertificate.reach_symm ⟨fun _ _ hedge=>symm hedge⟩ (h₀.trans hri)
    · exact ConnectivityCertificate.reach_symm ⟨fun _ _ hedge=>symm hedge⟩ (h₀.trans hro)

end BoundaryConnection

 

 


def bottomIndex (c : Fin M) (l : Fin 2) : Fin (TurnRectangle.ports M N) :=
  TurnStarter.left (TurnRectangle.width M N) (TurnRectangle.southRay c (1-l))

lemma bottomIndex_val (c : Fin M) (l : Fin 2) :
    (bottomIndex (N:=N) c l).val=2*N+2*c.val+l.val := by
  have hl : (1-l).val=1-l.val := by fin_cases l <;> decide
  dsimp [bottomIndex,TurnStarter.left,TurnRectangle.southRay,TurnRectangle.width]
  rw [hl]
  omega

lemma bottomIndex_lt (c : Fin M) (l : Fin 2) : (bottomIndex (N:=N) c l).val<TurnRectangle.width M N := by
  rw [bottomIndex_val]
  dsimp [TurnRectangle.width]
  omega

variable (hM : 1≤M) (hN : 1≤N) (F : Vertex → Pairing 6)

abbrev gauge := (TurnRectangle.box hM hN (start (L:=L) F) (TurnRectangle.starterGauge M N)
  (up L N F) (down L N F) (M*N)).gauge

lemma bottom_boundary (c : Fin M) (l : Fin 2) :
    boundary (L:=L) hM hN F (bottomIndex c l)=.inl (bottomIndex c l) := by
  exact TurnRectangle.retained_boundary _ _ _ _ _ _ _ _ (bottomIndex_lt c l)

lemma bottom_gauge (c : Fin M) (l : Fin 2) : gauge (L:=L) hM hN F (bottomIndex c l)= -3 := by
  rw [gauge,←TurnNetwork.namedGauge_boundary]
  change namedGauge (TurnRectangle.starterGauge M N) (M*N) (boundary (L:=L) hM hN F (bottomIndex c l))= -3
  rw [bottom_boundary]
  change TurnRectangle.starterGauge M N (bottomIndex c l)= -3
  unfold TurnRectangle.starterGauge
  rw [bottomIndex_val]
  have hi:=bottomIndex_lt (N:=N) c l
  rw [bottomIndex_val] at hi
  split_ifs <;> omega

lemma top_boundary (c : Fin M) (l : Fin 2) :
    boundary (L:=L) hM hN F (TurnRectangle.northSlot hM hN c.isLt l)=
      node L M N (vertex_inside L M N c ⟨N-1,by omega⟩ false) (lane false 0 l) := by
  rw [boundary,TurnRectangle.north_boundary,at_vertex]
  rfl

lemma top_gauge (c : Fin M) (l : Fin 2) :
    gauge (L:=L) hM hN F (TurnRectangle.northSlot hM hN c.isLt l)=0 := by
  rw [gauge,←TurnNetwork.namedGauge_boundary]
  change namedGauge (TurnRectangle.starterGauge M N) (M*N)
    (boundary (L:=L) hM hN F (TurnRectangle.northSlot hM hN c.isLt l))=0
  rw [top_boundary,at_vertex]
  fin_cases l <;> rfl

variable (hm : Matches (L:=L) (M:=M) (N:=N) F)
include hm

lemma bottom_connector (c : Fin M) (l : Fin 2)
    (hi : (F (vertex L M N c ⟨0,by omega⟩ true)).Occupied (lane true 0 l)) :
    Relation.ReflTransGen (graph (L:=L) hM hN F)
      (boundary (L:=L) hM hN F (bottomIndex c l))
      (node L M N (vertex_inside L M N c ⟨0,by omega⟩ true) (lane true 0 l)) ∧
    ∀ P : Node (TurnRectangle.ports M N) (M*N) → ℤ,
      (∀v w,graph (L:=L) hM hN F v w → P w-P v=turnEdge (L:=L) hM hN F v w) →
      P (node L M N (vertex_inside L M N c ⟨0,by omega⟩ true) (lane true 0 l))-
        P (boundary (L:=L) hM hN F (bottomIndex c l))=0 := by
  have him : (up L N F (c.val*N)).Occupied ⟨3-(1-l).val,by omega⟩ := by
    have hh:=up_time L M N F c (⟨0,by omega⟩:Fin N)
    simp only [Nat.add_zero] at hh
    rw [hh]
    fin_cases l <;> exact hi
  have hact:=(TurnRectangle.active_south (up L N F) c (1-l)).mpr him
  have e₁:=TurnRectangle.starter_edge hM hN (up L N F) (down L N F) hact
  have t₁:=TurnRectangle.starter_turn hM hN (up L N F) (down L N F) hact
  have e₂:=TurnRectangle.south_edge hM hN (up L N F) (down L N F) (interior_matches F hm) (1-l) him
  have t₂:=TurnRectangle.south_turn hM hN (up L N F) (down L N F) (interior_matches F hm) (1-l) him
  rw [TurnRectangle.southSlot_right] at e₂ t₂
  rw [bottom_boundary,at_vertex]
  have he : (⟨3-(1-l).val,by omega⟩:Fin 6)=lane true 0 l := by fin_cases l <;> rfl
  rw [he] at e₂ t₂
  refine ⟨(Relation.ReflTransGen.single e₁).trans (.single e₂),?_⟩
  intro P hP
  have hp₁:=(hP _ _ e₁).trans t₁
  have hp₂:=(hP _ _ e₂).trans t₂
  simp only [ite_true]
  change _-P (Sum.inl (TurnStarter.left _ _))=0
  omega

end RibbonRectangle

 

 


lemma last_pass (s : State) (l : List Bool) (hl : l≠[]) :
    ∃ p, (((back (terminal next s l)).1,p),(terminal next s l).2)∈passes s l := by
  induction l generalizing s with
  | nil=>exact (hl rfl).elim
  | cons b l ih=>
    cases l with
    | nil=>
      refine ⟨s.2,?_⟩
      simp only [terminal,back_next]
      exact List.mem_cons_self
    | cons c l=>
      obtain ⟨p,hp⟩:=ih (next s b) (by simp)
      exact ⟨p,List.mem_cons_of_mem _ hp⟩

lemma first_occupied (s : State) (l : List Bool) (hl : l≠[]) (hr : RibbonSimple s l) :
    (ribbon hr s.1).Occupied (lane s.1.2.2 s.2 0) := by
  cases l with
  | nil=>exact (hl rfl).elim
  | cons b l=>exact ⟨_,ribbon_arc hr List.mem_cons_self⟩

namespace RibbonRectangle
variable {L : ℤ} {M N : ℕ} (hM : 1≤M) (hN : 1≤N)

lemma endpoint_turn (s : State) (l : List Bool) (hl : l≠[]) (hr : RibbonSimple s l)
    (hs : Inside L M N s.1) (hI : ∀x∈passes s l,Inside L M N x.1.1)
    (hm : Matches (L:=L) (M:=M) (N:=N) (ribbon hr))
    (i j : Fin (TurnRectangle.ports M N)) (hne : i≠j)
    (hsi : Relation.ReflTransGen (graph (L:=L) hM hN (ribbon hr))
      (boundary (L:=L) hM hN (ribbon hr) i) (node L M N hs (lane s.1.2.2 s.2 0)))
    (hjt : Relation.ReflTransGen (graph (L:=L) hM hN (ribbon hr))
      (boundary (L:=L) hM hN (ribbon hr) j)
      (node L M N (last_inside s l hl hI)
        (lane (back (terminal next s l)).1.2.2 (terminal next s l).2 1)))
    (hzero : ∀P : Node (TurnRectangle.ports M N) (M*N) → ℤ,
      (∀v w,graph (L:=L) hM hN (ribbon hr) v w →
        P w-P v=turnEdge (L:=L) hM hN (ribbon hr) v w) →
      P (node L M N hs (lane s.1.2.2 s.2 0))-
          P (boundary (L:=L) hM hN (ribbon hr) i)=0 ∧
      P (node L M N (last_inside s l hl hI)
        (lane (back (terminal next s l)).1.2.2 (terminal next s l).2 1))-
          P (boundary (L:=L) hM hN (ribbon hr) j)=0) :
    turn l=Pairing.arcTurn (gauge (L:=L) hM hN (ribbon hr)) i j := by
  have hc:=TurnRectangle.compatible hM hN (start (L:=L) (ribbon hr))
    (up L N (ribbon hr)) (down L N (ribbon hr)) (physical_matches hM hN (ribbon hr) hm)
  obtain ⟨a,P,hreach,ha,he⟩:=TurnNetwork.potential (start (L:=L) (ribbon hr))
    (TurnRectangle.starterGauge M N) (up L N (ribbon hr)) (down L N (ribbon hr))
    (TurnRectangle.position M N) (TurnRectangle.position_bound hM hN) (M*N) hc
    (ribbon_drains hM hN s l hr hs hI hm i hsi)
  obtain ⟨p,hp⟩:=last_pass s l hl
  have hrt:=(route_reach hM hN (ribbon hr) hm s l hs hI (fun x hx=>ribbon_arc hr hx) hp).2
  have hab : a.Adj i j := ((hreach i j).mp (hsi.trans (hrt.trans
    (ConnectivityCertificate.reach_symm ⟨fun _ _ hedge=>symm hedge⟩ hjt)))).resolve_left hne
  have ht:=route_turn hM hN (ribbon hr) hm s l hl hs hI (fun x hx=>ribbon_arc hr hx) P he
  have hz:=hzero P he
  have hb:=ha i j hab
  change P (boundary (L:=L) hM hN (ribbon hr) j)-P (boundary (L:=L) hM hN (ribbon hr) i)=Pairing.arcTurn (gauge (L:=L) hM hN (ribbon hr)) i j at hb
  omega

lemma bottom_outside (c : Fin M) :
    ¬Inside L M N (back (vertex L M N c ⟨0,by omega⟩ true,0)).1 := by
  simp [Inside,back,neighbor,vertex]

include hM in
lemma bottom_turn (c₀ c₁ : Fin M) (l : List Bool) (hl : l≠[])
    (hr : RibbonSimple (vertex L M N c₀ ⟨0,by omega⟩ true,0) l)
    (hI : ∀x∈passes (vertex L M N c₀ ⟨0,by omega⟩ true,0) l,Inside L M N x.1.1)
    (ht : terminal next (vertex L M N c₀ ⟨0,by omega⟩ true,0) l=
      back (vertex L M N c₁ ⟨0,by omega⟩ true,0)) :
    turn l=if c₀≤c₁ then -3 else 3 := by
  let s : State:=(vertex L M N c₀ ⟨0,by omega⟩ true,0)
  have hm:=ribbon_matches (L:=L) (M:=M) (N:=N) hr (bottom_outside hN c₀)
    (by rw [ht]; exact bottom_outside hN c₁)
  have hi:=bottom_connector hM hN (ribbon hr) hm c₀ 0 (first_occupied s l hl hr)
  have heV : (back (terminal next s l)).1=vertex L M N c₁ ⟨0,by omega⟩ true := by rw [ht,back_back]
  have heP : (terminal next s l).2=0 := by rw [ht]; rfl
  obtain ⟨p,hp⟩:=last_pass s l hl
  have hocc : (ribbon hr (vertex L M N c₁ ⟨0,by omega⟩ true)).Occupied (lane true 0 1) := by
    have hh : (ribbon hr (back (terminal next s l)).1).Occupied
        (lane (back (terminal next s l)).1.2.2 (terminal next s l).2 1) := ⟨_,(ribbon_arc hr hp).symm⟩
    simpa only [heV,heP,vertex] using hh
  have hj:=bottom_connector hM hN (ribbon hr) hm c₁ 1 hocc
  have heNode : node L M N (last_inside s l hl hI)
        (lane (back (terminal next s l)).1.2.2 (terminal next s l).2 1)=
      node L M N (vertex_inside L M N c₁ ⟨0,by omega⟩ true) (lane true 0 1) := by
    rw [node_of_vertex _ heV,at_vertex,heV,heP]
    rfl
  have hne : bottomIndex (N:=N) c₀ 0 ≠bottomIndex c₁ 1 := by
    intro he
    have hv:=congrArg Fin.val he
    simp only [bottomIndex_val,Fin.val_zero,Fin.val_one] at hv
    omega
  have hh:=endpoint_turn hM hN s l hl hr (vertex_inside _ _ _ _ _ _) hI hm
    (bottomIndex c₀ 0) (bottomIndex c₁ 1) hne hi.1 (by rw [heNode]; exact hj.1)
    (fun P hP=>⟨hi.2 P hP,by rw [heNode]; exact hj.2 P hP⟩)
  rw [hh,Pairing.arcTurn,bottom_gauge,bottom_gauge]
  unfold Pairing.turnOrder
  simp only [Fin.le_iff_val_le_val,Fin.lt_def,bottomIndex_val,Fin.val_zero,Fin.val_one]
  split_ifs <;> omega

end RibbonRectangle
end

 

 

noncomputable section
open scoped Classical
open Diagram FiniteBranchTree

def closeStem (stem tail : List Bool) : List Bool :=
  (stem++true::tail)++true::reverseTurns stem

lemma closeStem_depart (s : State) (stem tail : List Bool)
    (hc : terminal next s (stem++true::tail)=
      ((terminal next s stem).1,outgoing (terminal next s stem).2 false)) :
    next (terminal next s (stem++true::tail)) true=back (terminal next s stem) := by
  rw [hc]
  have hp:=outgoing_opp (terminal next s stem).2 false
  change outgoing (outgoing (terminal next s stem).2 false) true=(terminal next s stem).2 at hp
  simp only [next,hp,back]

lemma closeStem_terminal (s : State) (stem tail : List Bool)
    (hc : terminal next s (stem++true::tail)=
      ((terminal next s stem).1,outgoing (terminal next s stem).2 false)) :
    terminal next s (closeStem stem tail)=back s := by
  rw [closeStem,terminal_append,terminal,closeStem_depart s stem tail hc,terminal_reverseTurns]

lemma closeStem_routes (s : State) (stem tail : List Bool) (v : Vertex)
    (hc : terminal next s (stem++true::tail)=
      ((terminal next s stem).1,outgoing (terminal next s stem).2 false)) :
    routes s (closeStem stem tail) v =
      routes s stem v ∪
      (if v=(terminal next s stem).1 then
        {((terminal next s stem).2,outgoing (terminal next s stem).2 true),
         (outgoing (terminal next s stem).2 false,(terminal next s stem).2)} else ∅) ∪
      routes (next (terminal next s stem) true) tail v ∪
      (routes s stem v).image Prod.swap := by
  have hp:=outgoing_opp (terminal next s stem).2 false
  change outgoing (outgoing (terminal next s stem).2 false) true=(terminal next s stem).2 at hp
  rw [closeStem,routes_append,routes_append,routes_cons,routes_cons,
    closeStem_depart s stem tail hc,routes_reverseTurns,hc]
  dsimp only [Prod.fst,Prod.snd]
  rw [hp]
  split_ifs <;> ext z <;> simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
    Finset.notMem_empty] <;> tauto

lemma closeStem_simple (s : State) (stem tail : List Bool)
    (hn : (visited Prod.fst next s (stem++true::tail)).Nodup)
    (hc : terminal next s (stem++true::tail)=
      ((terminal next s stem).1,outgoing (terminal next s stem).2 false)) :
    RibbonSimple s (closeStem stem tail) := by
  rw [visited_append] at hn
  have hs:=hn.of_append_left
  have hj:=List.nodup_cons.mp hn.of_append_right
  have hd:=hn.disjoint
  intro v
  rw [closeStem_routes s stem tail v hc]
  by_cases hv : v=(terminal next s stem).1
  · subst v
    have h₁ : (terminal next s stem).1∉visited Prod.fst next s stem := by
      intro h
      exact List.disjoint_left.mp hd h List.mem_cons_self
    rw [ite_eq_left rfl,routes_empty_of_notMem h₁,routes_empty_of_notMem hj.1]
    simp only [Finset.empty_union,Finset.union_empty,Finset.image_empty]
    exact ribbon_joint _ _
  · rw [ite_eq_right hv,Finset.union_empty]
    rcases routes_singleton_of_nodup hs v with he|⟨p,q,hpq,he⟩
    · rw [he,Finset.empty_union,Finset.image_empty,Finset.union_empty]
      exact ribbonSimple_of_nodup hj.2 v
    · have hm : v∈visited Prod.fst next s stem :=
        passes_mem_vertex ((mem_routes _ _ _ _).mp (he ▸ Finset.mem_singleton_self _))
      have hnot : v∉visited Prod.fst next (next (terminal next s stem) true) tail := by
        intro hh
        exact List.disjoint_left.mp hd hm (List.mem_cons_of_mem _ hh)
      rw [routes_empty_of_notMem hnot,Finset.union_empty,he]
      simp only [Finset.image_singleton,Finset.singleton_union,Prod.swap_prod_mk]
      exact ribbon_double _ p q hpq.symm

lemma closeStem_visits (s : State) (stem tail : List Bool)
    (hc : terminal next s (stem++true::tail)=
      ((terminal next s stem).1,outgoing (terminal next s stem).2 false)) :
    ∀v∈visited Prod.fst next s (closeStem stem tail),
      v∈visited Prod.fst next s (stem++true::tail) := by
  have hv : (terminal next s (stem++true::tail)).1=(terminal next s stem).1 := by rw [hc]
  simp only [closeStem,visited_append,visited,closeStem_depart s stem tail hc,
    visited_reverseTurns,List.mem_append,List.mem_cons,List.mem_reverse,hv]
  intro v h
  tauto

lemma closeStem_turn (stem tail : List Bool) :
    turn (closeStem stem tail)=turn (true::tail)+1 := by
  simp only [closeStem,turn_append,turn,sign,ite_true,turn_reverseTurns]
  omega

end
end CriticalStrip.HoneycombBranch

end OAI
