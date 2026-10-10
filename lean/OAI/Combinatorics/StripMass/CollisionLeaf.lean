import Mathlib
import OAI.Combinatorics.StripMass.BoundaryTree

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.HoneycombBranch
noncomputable section
open scoped Classical BigOperators
open FiniteBranchTree

lemma lastVisited_mem (s : State) (l : List Bool) (hl : l ≠ []) :
    (back (terminal next s l)).1 ∈ visited Prod.fst next s l := by
  induction l generalizing s with
  | nil => exact (hl rfl).elim
  | cons b l ih =>
    cases l with
    | nil => simp only [terminal,back_next,visited,List.mem_cons,true_or]
    | cons c l => exact List.mem_cons_of_mem _ (ih _ (by simp))

lemma exists_split_visit (s : State) (l : List Bool) (v : Vertex)
    (hv : v ∈ visited Prod.fst next s l) :
    ∃ stem b tail, l=stem++b::tail ∧ (terminal next s stem).1=v := by
  induction l generalizing s with
  | nil => simp only [visited,List.not_mem_nil] at hv
  | cons b l ih =>
    rcases List.mem_cons.mp hv with he | hv
    · exact ⟨[],b,l,rfl,he.symm⟩
    · obtain ⟨stem,c,t,he,hv⟩ := ih (next s b) hv
      exact ⟨b::stem,c,t,by simp only [List.cons_append,he],hv⟩

 

lemma collision_port_not_first (s : State) (b : Bool) (l : List Bool)
    (hn : (visited Prod.fst next s (b::l)).Nodup)
    (hc : (terminal next s (b::l)).1=s.1) :
    (terminal next s (b::l)).2 ≠ outgoing s.2 b := by
  intro hp
  have he : (back (terminal next s (b::l))).1=(next s b).1 := by
    simp only [back,hc,hp,next]
  cases l with
  | nil => exact next_ne s b hc
  | cons c l =>
    cases l with
    | nil =>
      have h := next_not_back (next s b) c
      rw [next_back] at h
      exact h hc
    | cons d l =>
      have hmem := lastVisited_mem (next (next s b) c) (d::l) (by simp)
      change (back (terminal next s (b::c::d::l))).1 ∈ _ at hmem
      rw [he] at hmem
      exact (List.nodup_cons.mp hn.tail).1 hmem

 

lemma collision_port_not_stem (D : Finset Vertex) (s : State) (stem : List Bool)
    (b : Bool) (l : List Bool) (hs : (back s).1 ∉ D)
    (hl : stem++b::l ∈ words D s)
    (hc : (terminal next s (stem++b::l)).1=(terminal next s stem).1) :
    (terminal next s (stem++b::l)).2 ≠ (terminal next s stem).2 := by
  intro hp
  have he : (back (terminal next s (stem++b::l))).1=(back (terminal next s stem)).1 := by
    simp only [back,hc,hp]
  have hm := lastVisited_mem (terminal next s stem) (b::l) (by simp)
  rw [←terminal_append,he] at hm
  have hfull := visited_nodup Prod.fst next hl
  have hdom := visited_mem_domain Prod.fst next hl
  cases stem with
  | nil => exact hs (hdom _ hm)
  | cons a stem =>
    have hh := lastVisited_mem s (a::stem) (by simp)
    rw [visited_append] at hfull
    exact List.disjoint_left.mp hfull.disjoint hh hm

 
lemma collision_index_eq (s : State) (stem : List Bool) (b : Bool) (l : List Bool)
    (hn : (visited Prod.fst next s (stem++b::l)).Nodup) :
    (visited Prod.fst next s (stem++b::l)).idxOf (terminal next s stem).1=stem.length := by
  rw [visited_append] at hn ⊢
  have hnot : (terminal next s stem).1 ∉ visited Prod.fst next s stem := by
    intro h
    exact List.disjoint_left.mp hn.disjoint h (List.mem_cons_self)
  rw [List.idxOf_append_of_notMem hnot]
  simp only [visited,List.idxOf_cons_self,add_zero,visited_length]

 
def collisionIndex (s : State) (l : List Bool) : ℕ :=
  (visited Prod.fst next s l).idxOf (terminal next s l).1

def collisionReverse (s : State) (l : List Bool) : List Bool :=
  l.take (collisionIndex s l) ++ reverseCycle (l.drop (collisionIndex s l))

lemma collisionReverse_split (s : State) (stem : List Bool) (b : Bool) (tail : List Bool)
    (hn : (visited Prod.fst next s (stem++b::tail)).Nodup)
    (hc : (terminal next s (stem++b::tail)).1=(terminal next s stem).1) :
    collisionReverse s (stem++b::tail)=stem++reverseCycle (b::tail) := by
  have hx : collisionIndex s (stem++b::tail)=stem.length := by
    rw [collisionIndex,hc,collision_index_eq s stem b tail hn]
  simp only [collisionReverse,hx,List.take_left,List.drop_left]

lemma collision_split (D : Finset Vertex) (s : State) (l : List Bool)
    (hl : l ∈ words D s) (ht : (terminal next s l).1 ∈ D) :
    ∃ stem b tail, l=stem++b::tail ∧
      (terminal next s (stem++b::tail)).1=(terminal next s stem).1 := by
  obtain ⟨stem,b,t,he,hc⟩ := exists_split_visit s l (terminal next s l).1
    ((terminal_mem_domain_iff_collision Prod.fst next hl).mp ht)
  refine ⟨stem,b,t,he,?_⟩
  rw [←he]
  exact hc.symm

lemma collisionReverse_mem (D : Finset Vertex) (s : State) (l : List Bool)
    (hs : (back s).1 ∉ D) (hl : l ∈ words D s) (ht : (terminal next s l).1 ∈ D) :
    collisionReverse s l ∈ words D s ∧
      (terminal next s (collisionReverse s l)).1=(terminal next s l).1 := by
  obtain ⟨stem,b,t,rfl,hc⟩ := collision_split D s l hl ht
  have hn := visited_nodup Prod.fst next hl
  have h₀ := collision_port_not_stem D s stem b t hs hl hc
  have hn' : (visited Prod.fst next (terminal next s stem) (b::t)).Nodup := by
    rw [visited_append] at hn
    exact hn.of_append_right
  have hc' := hc
  rw [terminal_append] at hc'
  have h₁ := collision_port_not_first (terminal next s stem) b t hn' hc'
  rw [collisionReverse_split s stem b t hn hc]
  refine ⟨prefix_reverseCycle_mem D s stem b t hl hc h₀ (by simpa only [terminal_append] using h₁),?_⟩
  rw [terminal_append,terminal_reverseCycle _ b t hc' (by simpa only [terminal_append] using h₀) h₁]
  exact hc.symm

lemma collisionReverse_involutive (D : Finset Vertex) (s : State) (l : List Bool)
    (hs : (back s).1 ∉ D) (hl : l ∈ words D s) (ht : (terminal next s l).1 ∈ D) :
    collisionReverse s (collisionReverse s l)=l := by
  obtain ⟨stem,b,t,rfl,hc⟩ := collision_split D s l hl ht
  have he := collisionReverse_split s stem b t (visited_nodup Prod.fst next hl) hc
  obtain ⟨hm,hv⟩ := collisionReverse_mem D s (stem++b::t) hs hl ht
  rw [he] at hm hv ⊢
  change stem++(!b)::reverseTurns t ∈ words D s at hm
  have hc' : (terminal next s (stem++(!b)::reverseTurns t)).1=(terminal next s stem).1 :=
    hv.trans hc
  change collisionReverse s (stem++(!b)::reverseTurns t) = stem++b::t
  rw [collisionReverse_split s stem (!b) (reverseTurns t) (visited_nodup Prod.fst next hm) hc']
  simp only [reverseCycle,reverseTurns_involutive,Bool.not_not]

lemma collisionReverse_weight (D : Finset Vertex) (s : State) (l : List Bool)
    (hl : l ∈ words D s) (ht : (terminal next s l).1 ∈ D)
    (hturn : turn (l.drop (collisionIndex s l)) % 8 = 4) :
    wordWeight factor l + wordWeight factor (collisionReverse s l) = 0 := by
  obtain ⟨stem,b,t,rfl,hc⟩ := collision_split D s l hl ht
  have hn := visited_nodup Prod.fst next hl
  have hx : collisionIndex s (stem++b::t)=stem.length := by
    rw [collisionIndex,hc,collision_index_eq s stem b t hn]
  rw [hx,List.drop_left] at hturn
  rw [collisionReverse_split s stem b t hn hc]
  exact cycle_weight_cancel stem (b::t) hturn

 

theorem collisionMass_zero_of_turns (D : Finset Vertex) (s : State)
    (hs : (back s).1 ∉ D)
    (hturn : ∀ l ∈ words D s, (terminal next s l).1 ∈ D →
      turn (l.drop (collisionIndex s l)) % 8 = 4) :
    collisionMass Prod.fst next factor D s=0 := by
  let F := (words D s).filter (fun l => (terminal next s l).1 ∈ D)
  have hf : ∀ l∈F, collisionReverse s l ∈ F := by
    intro l hl
    obtain ⟨hl,ht⟩ := Finset.mem_filter.mp hl
    obtain ⟨hm,he⟩ := collisionReverse_mem D s l hs hl ht
    exact Finset.mem_filter.mpr ⟨hm,he ▸ ht⟩
  have hrev : ∀ l∈F,collisionReverse s (collisionReverse s l)=l := by
    intro l hl
    obtain ⟨hl,ht⟩ := Finset.mem_filter.mp hl
    exact collisionReverse_involutive D s l hs hl ht
  have hsum : (∑ l∈F,wordWeight factor (collisionReverse s l)) =
      ∑ l∈F,wordWeight factor l := by
    apply Finset.sum_bij (fun l _ => collisionReverse s l) hf
    · intro a ha b hb he
      have hh := congrArg (collisionReverse s) he
      rwa [hrev a ha,hrev b hb] at hh
    · intro b hb
      exact ⟨collisionReverse s b,hf b hb,hrev b hb⟩
    · intro l hl
      rfl
  have hz : (∑ l∈F,wordWeight factor l) + (∑ l∈F,wordWeight factor (collisionReverse s l)) = 0 := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro l hl
    obtain ⟨hl,ht⟩ := Finset.mem_filter.mp hl
    exact collisionReverse_weight D s l hl ht (hturn l hl ht)
  rw [hsum] at hz
  change (∑ l∈F,wordWeight factor l)=0
  linear_combination (1/2:ℂ)*hz

end
end CriticalStrip.HoneycombBranch

 

 

 

namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

namespace Pairing

def turnOrder {n : ℕ} (i j : Fin n) : ℤ :=
  if i < j then 1 else if j < i then -1 else 0

def arcTurn {n : ℕ} (g : Fin n → ℤ) (i j : Fin n) : ℤ :=
  g j - g i - 3 * turnOrder i j

lemma turnOrder_self {n : ℕ} (i : Fin n) : turnOrder i i=0 := by
  simp [turnOrder]

lemma turnOrder_reverse {n : ℕ} (i j : Fin n) : turnOrder j i= -turnOrder i j := by
  unfold turnOrder
  split_ifs <;> omega

lemma arcTurn_reverse {n : ℕ} (g : Fin n → ℤ) (i j : Fin n) :
    arcTurn g j i= -arcTurn g i j := by
  unfold arcTurn
  rw [turnOrder_reverse i j]
  ring

 
def turnPotential {n : ℕ} (p : Pairing n) (g : Fin n → ℤ) (i : Fin n) : ℤ :=
  g i - if p.Occupied i ∧ p.partnerOrSelf i < i then 3 else 0

lemma turnPotential_of_adj {n : ℕ} {p : Pairing n} (g : Fin n → ℤ)
    {i j : Fin n} (h : p.Adj i j) :
    p.turnPotential g j-p.turnPotential g i=arcTurn g i j := by
  have hi : p.Occupied i := ⟨j,h⟩
  have hj : p.Occupied j := ⟨i,h.symm⟩
  have hpi := (p.adj_partnerOrSelf i j).mp h
  have hpj := (p.adj_partnerOrSelf j i).mp h.symm
  have hn : i≠j := fun he=>p.adj_irrefl _ (he ▸ h)
  simp only [turnPotential,hi,hj,true_and,←hpi.2,←hpj.2,arcTurn,turnOrder]
  split_ifs <;> omega

 

lemma cap_partner_orders {n : ℕ} {p : Pairing n} {a b x y : Fin n}
    (hab : a.val+1=b.val) (hx : p.Adj a x) (hy : p.Adj b y)
    (hn : ¬p.Adj a b) :
    (x<a ∧ b<y) ∨ (b<y ∧ y<x) ∨ (y<x ∧ x<a) := by
  have he:=adjacent_partners hab hx hy hn
  have hc:=not_cross hx hy
  simp only [Cross] at hc
  simp only [Fin.lt_def,Fin.ne_iff_vne] at he ⊢
  omega

lemma cap_turn_order {n : ℕ} {p : Pairing n} {a b x y : Fin n}
    (hab : a.val+1=b.val) (hx : p.Adj a x) (hy : p.Adj b y)
    (hn : ¬p.Adj a b) :
    turnOrder x a + turnOrder b y - 1 = turnOrder x y := by
  have ho:=cap_partner_orders hab hx hy hn
  simp only [turnOrder]
  split_ifs <;> rcases ho with ⟨_,_⟩|⟨_,_⟩|⟨_,_⟩ <;> omega

 

lemma cap_arcTurn {n : ℕ} {p : Pairing n} {a b x y : Fin n}
    (g : Fin n → ℤ) (hab : a.val+1=b.val) (hg : g b=g a-2)
    (hx : p.Adj a x) (hy : p.Adj b y) (hn : ¬p.Adj a b) :
    arcTurn g x a+1+arcTurn g b y=arcTurn g x y := by
  have hc:=cap_turn_order hab hx hy hn
  simp only [arcTurn,hg]
  omega

 

lemma cap_loop_turn {n : ℕ} (g : Fin n → ℤ) {a b : Fin n}
    (hab : a.val+1=b.val) (hg : g b=g a-2) :
    arcTurn g a b-1= -6 := by
  have hlt : a<b := by omega
  simp only [arcTurn,hg,turnOrder,hlt,ite_true]
  omega

 

def swapGauge {n : ℕ} (g : Fin n → ℤ) (a b : Fin n) : Fin n → ℤ :=
  fun i=>g (Equiv.swap a b i)

lemma swapGauge_left {n : ℕ} (g : Fin n → ℤ) (a b : Fin n) :
    swapGauge g a b a=g b := by simp [swapGauge]
lemma swapGauge_right {n : ℕ} (g : Fin n → ℤ) (a b : Fin n) :
    swapGauge g a b b=g a := by simp [swapGauge]
lemma swapGauge_other {n : ℕ} (g : Fin n → ℤ) (a b i : Fin n)
    (ha : i≠a) (hb : i≠b) : swapGauge g a b i=g i := by
  simp [swapGauge,Equiv.swap_apply_of_ne_of_ne ha hb]

lemma cup_arcTurn {n : ℕ} (g : Fin n → ℤ) {a b : Fin n}
    (hab : a.val+1=b.val) (hg : g b=g a-2) :
    arcTurn (swapGauge g a b) a b = -1 := by
  have hlt : a<b := by omega
  simp only [arcTurn,swapGauge_left,swapGauge_right,hg,turnOrder,hlt,ite_true]
  omega

lemma adjacent_turnOrder {n : ℕ} {a b x : Fin n} (hab : a.val+1=b.val)
    (ha : x≠a) (hb : x≠b) : turnOrder a x=turnOrder b x := by
  simp only [turnOrder]
  split_ifs <;> simp only [Fin.lt_def,Fin.ne_iff_vne] at * <;> omega

lemma diagonal_lower_arcTurn {n : ℕ} (g : Fin n → ℤ) {a b x : Fin n}
    (hab : a.val+1=b.val) (ha : x≠a) (hb : x≠b) :
    arcTurn g x a = arcTurn (swapGauge g a b) x b := by
  have ho:=adjacent_turnOrder hab ha hb
  have ho' : turnOrder x a=turnOrder x b := by
    rw [turnOrder_reverse a x,turnOrder_reverse b x,ho]
  simp only [arcTurn,swapGauge_right,swapGauge_other g a b x ha hb,ho']

lemma diagonal_upper_arcTurn {n : ℕ} (g : Fin n → ℤ) {a b x : Fin n}
    (hab : a.val+1=b.val) (ha : x≠a) (hb : x≠b) :
    arcTurn g x b = arcTurn (swapGauge g a b) x a := by
  have ho:=adjacent_turnOrder hab ha hb
  have ho' : turnOrder x a=turnOrder x b := by
    rw [turnOrder_reverse a x,turnOrder_reverse b x,ho]
  simp only [arcTurn,swapGauge_left,swapGauge_other g a b x ha hb,ho']

lemma vertical_lower_arcTurn {n : ℕ} (g : Fin n → ℤ) {a b x : Fin n}
    (hg : g b=g a-2) (ha : x≠a) (hb : x≠b) :
    arcTurn g x a-2=arcTurn (swapGauge g a b) x a := by
  simp only [arcTurn,swapGauge_left,swapGauge_other g a b x ha hb,hg]
  ring

lemma vertical_upper_arcTurn {n : ℕ} (g : Fin n → ℤ) {a b x : Fin n}
    (hg : g b=g a-2) (ha : x≠a) (hb : x≠b) :
    arcTurn g x b+2=arcTurn (swapGauge g a b) x b := by
  simp only [arcTurn,swapGauge_right,swapGauge_other g a b x ha hb,hg]
  ring

end Pairing

 

 

 


namespace Graph

variable {V : Type*} {n : ℕ} {r : V → V → Prop} [Std.Symm r]
  {b : Fin n → V} {p : Pairing n}

def boundaryConstant (b : Fin n → V) (r : V → V → Prop) (f : Fin n → ℤ) (v : V) : ℤ :=
  if h : ∃ i, Relation.ReflTransGen r v (b i) then f (Classical.choose h) else 0

lemma boundaryConstant_eq (h : GraphRealizes r b p) (f : Fin n → ℤ)
    (hf : ∀ i j, p.Adj i j → f i=f j) {v : V} {i : Fin n}
    (hi : Relation.ReflTransGen r v (b i)) : boundaryConstant b r f v=f i := by
  have he : ∃ j,Relation.ReflTransGen r v (b j) := ⟨i,hi⟩
  rw [boundaryConstant,dite_eq_left he]
  have hj := Classical.choose_spec he
  have hc := (h.reach (Classical.choose he) i).mp ((symm hj).trans hi)
  exact hc.elim (fun hh=>congrArg f hh) (hf _ _)

lemma boundaryConstant_boundary (h : GraphRealizes r b p) (f : Fin n → ℤ)
    (hf : ∀ i j,p.Adj i j → f i=f j) (i : Fin n) :
    boundaryConstant b r f (b i)=f i :=
  boundaryConstant_eq h f hf .refl

lemma boundaryConstant_edge (h : GraphRealizes r b p) (f : Fin n → ℤ)
    (hf : ∀ i j,p.Adj i j → f i=f j) {v w : V} (hv : r v w) :
    boundaryConstant b r f v=boundaryConstant b r f w := by
  obtain ⟨i,_,hi⟩ := h.no_loop v w hv
  rw [boundaryConstant_eq h f hf hi,
    boundaryConstant_eq h f hf ((Relation.ReflTransGen.single (symm hv)).trans hi)]

 

lemma renormalize_potential (h : GraphRealizes r b p) (P : V → ℤ)
    (f : Fin n → ℤ)
    (hf : ∀ i j,p.Adj i j → f j-f i=P (b j)-P (b i)) :
    ∃ Q : V → ℤ, (∀ i,Q (b i)=f i) ∧
      ∀ v w,r v w → Q w-Q v=P w-P v := by
  let d : Fin n → ℤ := fun i=>f i-P (b i)
  have hd : ∀ i j,p.Adj i j → d i=d j := by
    intro i j hij
    have hh := hf i j hij
    dsimp only [d]
    omega
  refine ⟨fun v=>P v+boundaryConstant b r d v,?_,?_⟩
  · intro i
    dsimp only
    rw [boundaryConstant_boundary h d hd]
    simp [d]
  · intro v w hvw
    dsimp only
    rw [boundaryConstant_edge h d hd hvw]
    omega

end Graph
end
end CriticalStrip.Diagram

end OAI
