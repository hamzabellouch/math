import Mathlib
import OAI.Combinatorics.StripMass.ScalarBridge

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram.PathGraph
noncomputable section
open scoped Classical

 
def AtMostTwo {V : Type*} (r : V → V → Prop) : Prop :=
  ∀ ⦃v x y z⦄, r v x → r v y → r v z → x ≠ y → z = x ∨ z = y

def AtMostOne {V : Type*} (r : V → V → Prop) (v : V) : Prop :=
  ∀ ⦃x y⦄, r v x → r v y → x = y

 
def Trace {V : Type*} (r : V → V → Prop) (a b : V) (p : List V) : Prop :=
  p.head? = some a ∧ p.getLast? = some b ∧ p.Nodup ∧ p.IsChain r

 
def Consecutive {V : Type*} (p : List V) (v w : V) : Prop :=
  ∃ (i : ℕ) (hi : i+1 < p.length),
    (p[i] = v ∧ p[i+1] = w) ∨ (p[i] = w ∧ p[i+1] = v)

lemma consecutive_symm {V : Type*} {p : List V} {v w : V} :
    Consecutive p v w → Consecutive p w v := by
  rintro ⟨i,hi,h⟩
  exact ⟨i,hi,h.symm⟩

lemma consecutive_mem {V : Type*} {p : List V} {v w : V}
    (h : Consecutive p v w) : v ∈ p ∧ w ∈ p := by
  obtain ⟨i,hi,h⟩ := h
  rcases h with ⟨hv,hw⟩ | ⟨hw,hv⟩ <;>
    exact ⟨List.mem_of_getElem hv,List.mem_of_getElem hw⟩

lemma Trace.length_two_le {V : Type*} {r : V → V → Prop} {a b : V} {p : List V}
    (h : Trace r a b p) (hab : a ≠ b) : 2 ≤ p.length := by
  rcases p with _ | ⟨x,p⟩
  · simp [Trace] at h
  · cases p with
    | nil => simp [Trace] at h; exact (hab (h.1.symm.trans h.2)).elim
    | cons => simp

lemma Trace.first {V : Type*} {r : V → V → Prop} {a b : V} {p : List V}
    (h : Trace r a b p) (hi : 0 < p.length) : p[0] = a := by
  have hh := h.1
  simpa only [List.head?_eq_getElem?,List.getElem?_eq_getElem hi,Option.some.injEq] using hh

lemma Trace.last {V : Type*} {r : V → V → Prop} {a b : V} {p : List V}
    (h : Trace r a b p) (hi : p.length-1 < p.length) : p[p.length-1] = b := by
  have hh := h.2.1
  simpa only [List.getLast?_eq_getElem?,List.getElem?_eq_getElem hi,Option.some.injEq] using hh

 

theorem Trace.edge_consecutive {V : Type*} {r : V → V → Prop}
    (hs : Std.Symm r) (h₂ : AtMostTwo r) {a b : V}
    (ha : AtMostOne r a) (hb : AtMostOne r b) {p : List V}
    (hp : Trace r a b p) (hab : a ≠ b) {v w : V}
    (hv : v ∈ p) (hvw : r v w) : Consecutive p v w := by
  obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hv
  have hlen := hp.length_two_le hab
  have hc := List.isChain_iff_getElem.mp hp.2.2.2
  by_cases hz : i=0
  · subst i
    have he : p[1] = w := ha (by simpa only [hp.first (by omega)] using hc 0 (by omega))
      (by simpa only [hp.first (by omega)] using hvw)
    exact ⟨0,by omega,Or.inl ⟨rfl,he⟩⟩
  · by_cases ht : i+1=p.length
    · have hi' : i=p.length-1 := by omega
      have hpi : p[i] = b := by simpa only [hi'] using hp.last (by omega)
      have hw : p[i-1] = w := hb
        (by have hh := hs.symm _ _ (hc (i-1) (by omega));
            have he : i-1+1=i := by omega
            simpa only [he,hpi] using hh)
        (by simpa only [hpi] using hvw)
      refine ⟨i-1,by omega,Or.inr ⟨hw,?_⟩⟩
      have he : i-1+1=i := by omega
      simp only [he]
    · have he : i-1+1=i := by omega
      have hm : r p[i] p[i-1] := by
        have hh := hs.symm _ _ (hc (i-1) (by omega))
        simpa only [he] using hh
      have hp' : r p[i] p[i+1] := hc i (by omega)
      have hne : p[i-1] ≠ p[i+1] := by
        intro hh
        have hi' := hp.2.2.1.getElem_inj_iff.mp hh
        omega
      rcases h₂ hm hp' hvw hne with hw | hw
      · exact ⟨i-1,by omega,Or.inr ⟨hw.symm,by simp only [he]⟩⟩
      · exact ⟨i,by omega,Or.inl ⟨rfl,hw.symm⟩⟩

lemma Trace.reach_mem {V : Type*} {r : V → V → Prop}
    (hs : Std.Symm r) (h₂ : AtMostTwo r) {a b : V}
    (ha : AtMostOne r a) (hb : AtMostOne r b) {p : List V}
    (hp : Trace r a b p) (hab : a ≠ b) {v : V}
    (hr : Relation.ReflTransGen r v a) : v ∈ p := by
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl =>
    have hl := hp.length_two_le hab
    exact List.mem_of_getElem (hp.first (by omega))
  | @head v w hvw hr ih =>
    exact (consecutive_mem (hp.edge_consecutive hs h₂ ha hb hab ih (hs.symm _ _ hvw))).2

 

theorem Trace.edges_iff {V : Type*} {r : V → V → Prop}
    (hs : Std.Symm r) (h₂ : AtMostTwo r) {a b : V}
    (ha : AtMostOne r a) (hb : AtMostOne r b) {p : List V}
    (hp : Trace r a b p) (hab : a ≠ b)
    (hd : ∀ v w, r v w → Relation.ReflTransGen r v a) (v w : V) :
    r v w ↔ Consecutive p v w := by
  constructor
  · intro hvw
    exact hp.edge_consecutive hs h₂ ha hb hab (hp.reach_mem hs h₂ ha hb hab (hd v w hvw)) hvw
  · rintro ⟨i,hi,he⟩
    have hc := List.isChain_iff_getElem.mp hp.2.2.2 i hi
    rcases he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact hc
    · exact hs.symm _ _ hc

lemma exists_trace {V : Type*} {r : V → V → Prop} (hs : Std.Symm r)
    (hirr : ∀ v, ¬r v v) {a b : V} (hr : Relation.ReflTransGen r a b) :
    ∃ p : List V, Trace r a b p := by
  let G : SimpleGraph V := ⟨r,hs,⟨hirr⟩⟩
  obtain ⟨w,hw⟩ := ((SimpleGraph.reachable_iff_reflTransGen (G := G) a b).mpr hr).exists_isPath
  refine ⟨w.support,?_,?_,hw.support_nodup,w.isChain_adj_support⟩
  · rw [List.head?_eq_some_head w.support_ne_nil]; simp
  · rw [List.getLast?_eq_some_getLast w.support_ne_nil]; simp

lemma Trace.eq_singleton {V : Type*} {r : V → V → Prop} {a : V} {p : List V}
    (hp : Trace r a a p) : p = [a] := by
  have hpos : 0 < p.length := by
    cases p with
    | nil => simp [Trace] at hp
    | cons => simp
  have hf := hp.first hpos
  have hl := hp.last (by omega)
  have he : 0 = p.length-1 := hp.2.2.1.getElem_inj_iff.mp (hf.trans hl.symm)
  obtain ⟨l,rfl⟩ := List.head?_eq_some_iff.mp hp.1
  have hlen : l.length=0 := by simp only [List.length_cons] at he; omega
  simp only [List.length_eq_zero_iff.mp hlen]

lemma Trace.avoid {V : Type*} {r : V → V → Prop} {x a b : V} {p : List V}
    (hp : Trace r a b p) (hx : x ∉ p) :
    Trace (fun v w => r v w ∧ v ≠ x ∧ w ≠ x) a b p := by
  refine ⟨hp.1,hp.2.1,hp.2.2.1,?_⟩
  rw [List.isChain_iff_getElem]
  intro i hi
  exact ⟨List.isChain_iff_getElem.mp hp.2.2.2 i hi,
    fun he => hx (List.mem_of_getElem he), fun he => hx (List.mem_of_getElem he)⟩

 

theorem Trace.unique {V : Type*} {r : V → V → Prop}
    (hs : Std.Symm r) (h₂ : AtMostTwo r) {a b : V}
    (ha : AtMostOne r a) {p q : List V}
    (hp : Trace r a b p) (hq : Trace r a b q) : p = q := by
  induction p generalizing r a b q with
  | nil => simp [Trace] at hp
  | cons x p ih =>
    have hxa : x=a := by simpa using hp.1
    subst x
    by_cases hab : a=b
    · subst b
      exact hp.eq_singleton.trans hq.eq_singleton.symm
    have hl := hp.length_two_le hab
    obtain ⟨q,rfl⟩ := List.head?_eq_some_iff.mp hq.1
    have hlq := hq.length_two_le hab
    cases p with
    | nil => simp at hl
    | cons v p =>
      cases q with
      | nil => simp at hlq
      | cons w q =>
        have hav : r a v := (List.isChain_cons_cons.mp hp.2.2.2).1
        have haw : r a w := (List.isChain_cons_cons.mp hq.2.2.2).1
        have hvw := ha hav haw
        subst w
        let s : V → V → Prop := fun v w => r v w ∧ v ≠ a ∧ w ≠ a
        have hsp : Trace s v b (v::p) := by
          apply Trace.avoid (r := r)
          · refine ⟨rfl,?_,hp.2.2.1.of_cons,(List.isChain_cons_cons.mp hp.2.2.2).2⟩
            simpa only [List.getLast?_cons_cons] using hp.2.1
          · exact (List.nodup_cons.mp hp.2.2.1).1
        have hsq : Trace s v b (v::q) := by
          apply Trace.avoid (r := r)
          · refine ⟨rfl,?_,hq.2.2.1.of_cons,(List.isChain_cons_cons.mp hq.2.2.2).2⟩
            simpa only [List.getLast?_cons_cons] using hq.2.1
          · exact (List.nodup_cons.mp hq.2.2.1).1
        have hss : Std.Symm s := ⟨fun x y h => ⟨hs.symm _ _ h.1,h.2.2,h.2.1⟩⟩
        have hs₂ : AtMostTwo s := by
          intro v x y z hx hy hz hn
          exact h₂ hx.1 hy.1 hz.1 hn
        have hs₁ : AtMostOne s v := by
          intro x y hx hy
          rcases h₂ (hs.symm _ _ hav) hx.1 hy.1 hx.2.2.symm with hy' | hy'
          · exact (hy.2.2 hy').elim
          · exact hy'.symm
        exact congrArg (List.cons a) (ih hss hs₂ hs₁ hsp hsq)

 

theorem existsUnique_trace {V : Type*} {r : V → V → Prop}
    (hs : Std.Symm r) (hirr : ∀ v, ¬r v v) (h₂ : AtMostTwo r) {a b : V}
    (ha : AtMostOne r a) (hr : Relation.ReflTransGen r a b) :
    ∃! p : List V, Trace r a b p := by
  obtain ⟨p,hp⟩ := exists_trace hs hirr hr
  exact ⟨p,hp,fun q hq => hq.unique hs h₂ ha hp⟩

lemma consecutive_iff_neighbors {V : Type*} {p : List V} (hp : p.Nodup)
    (i : ℕ) (hi : i < p.length) (v : V) :
    Consecutive p p[i] v ↔
      (∃ h : 0 < i, v = p[i-1]) ∨ (∃ h : i+1 < p.length, v = p[i+1]) := by
  constructor
  · rintro ⟨j,hj,⟨he,hv⟩ | ⟨hv,he⟩⟩
    · have hji : j=i := hp.getElem_inj_iff.mp he
      subst j
      exact Or.inr ⟨hj,hv.symm⟩
    · have hji : j+1=i := hp.getElem_inj_iff.mp he
      have hj' : j=i-1 := by omega
      exact Or.inl ⟨by omega,by simpa only [hj'] using hv.symm⟩
  · rintro (⟨_,hv⟩ | ⟨hv,hv'⟩)
    · refine ⟨i-1,by omega,Or.inr ⟨hv.symm,?_⟩⟩
      have he : i-1+1=i := by omega
      simp only [he]
    · exact ⟨i,hv,Or.inl ⟨rfl,hv'.symm⟩⟩

lemma consecutive_irrefl {V : Type*} {p : List V} (hp : p.Nodup) (v : V) :
    ¬Consecutive p v v := by
  rintro ⟨i,hi,⟨h₁,h₂⟩ | ⟨h₂,h₁⟩⟩ <;>
    have hh := hp.getElem_inj_iff.mp (h₁.trans h₂.symm) <;> omega

lemma consecutive_two {V : Type*} {p : List V} (hp : p.Nodup) :
    AtMostTwo (Consecutive p) := by
  intro v x y z hx hy hz hxy
  obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem (consecutive_mem hx).1
  rw [consecutive_iff_neighbors hp i hi] at hx hy hz
  rcases hx with ⟨hx,rfl⟩ | ⟨hx,rfl⟩ <;>
    rcases hy with ⟨hy,rfl⟩ | ⟨hy,rfl⟩ <;>
    rcases hz with ⟨hz,rfl⟩ | ⟨hz,rfl⟩ <;> simp_all

lemma consecutive_first_one {V : Type*} {p : List V} (hp : p.Nodup)
    (hpos : 0 < p.length) : AtMostOne (Consecutive p) p[0] := by
  intro x y hx hy
  rw [consecutive_iff_neighbors hp 0 hpos] at hx hy
  simpa only [Nat.lt_irrefl,exists_false,exists_prop,and_true,false_or,exists_and_left] using
    (show x=y from by rcases hx with ⟨h,h'⟩ | ⟨h,rfl⟩; · omega
                      rcases hy with ⟨h,h'⟩ | ⟨h,rfl⟩; · omega
                      rfl)

lemma consecutive_last_one {V : Type*} {p : List V} (hp : p.Nodup)
    (hpos : 0 < p.length) : AtMostOne (Consecutive p) p[p.length-1] := by
  intro x y hx hy
  rw [consecutive_iff_neighbors hp (p.length-1) (by omega)] at hx hy
  rcases hx with ⟨h,rfl⟩ | ⟨h,h'⟩
  · rcases hy with ⟨h,rfl⟩ | ⟨h,h'⟩
    · rfl
    · omega
  · omega

lemma consecutive_chain {V : Type*} (p : List V) : p.IsChain (Consecutive p) := by
  rw [List.isChain_iff_getElem]
  intro i hi
  exact ⟨i,hi,Or.inl ⟨rfl,rfl⟩⟩

lemma Trace.used_of_mem {V : Type*} {r : V → V → Prop}
    (hs : Std.Symm r) {a b : V} {p : List V} (hp : Trace r a b p)
    (hab : a ≠ b) {v : V} (hv : v ∈ p) : ∃ w, r v w := by
  obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hv
  have hl := hp.length_two_le hab
  have hc := List.isChain_iff_getElem.mp hp.2.2.2
  by_cases hi' : i+1 < p.length
  · exact ⟨p[i+1],hc i hi'⟩
  · have hi0 : 0 < i := by omega
    have he : i-1+1=i := by omega
    exact ⟨p[i-1],by simpa only [he] using hs.symm _ _ (hc (i-1) (by omega))⟩

lemma Trace.reach_of_mem {V : Type*} {r : V → V → Prop} {a b : V}
    {p : List V} (hp : Trace r a b p) {v : V} (hv : v ∈ p) :
    Relation.ReflTransGen r a v := by
  obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hv
  induction i with
  | zero => rw [hp.first (by omega)]
  | succ i ih =>
    exact (ih (by omega) (by simp)).tail (List.isChain_iff_getElem.mp hp.2.2.2 i hi)

end
end CriticalStrip.Diagram.PathGraph

 

 

namespace CriticalStrip
noncomputable section
open scoped Classical BigOperators
open Diagram.PathGraph

 

structure WireConfiguration (N : ℕ) (finish : Triangle) where
  graph : SimpleGraph Triangle
  allowed : ∀ v w, graph.Adj v w → adjacent v w ∧ v.2.1 < N ∧ w.2.1 < N
  two : AtMostTwo graph.Adj
  source_one : AtMostOne graph.Adj (up 0 0)
  finish_one : AtMostOne graph.Adj finish
  source_used : ∃ w, graph.Adj (up 0 0) w
  finish_used : ∃ w, graph.Adj finish w
  drains : ∀ v w, graph.Adj v w → Relation.ReflTransGen graph.Adj v (up 0 0)

namespace WireConfiguration
variable {N : ℕ} {finish : Triangle}

@[ext] theorem ext {x y : WireConfiguration N finish} (h : x.graph = y.graph) : x=y := by
  cases x; cases y; cases h; rfl

lemma reach (D : WireConfiguration N finish) :
    Relation.ReflTransGen D.graph.Adj (up 0 0) finish := by
  obtain ⟨w,hw⟩ := D.finish_used
  have : Std.Symm D.graph.Adj := D.graph.symm
  exact symm (D.drains finish w hw)

lemma existsUniqueTrace (D : WireConfiguration N finish) :
    ∃! p : List Triangle, Trace D.graph.Adj (up 0 0) finish p :=
  existsUnique_trace D.graph.symm (fun v => D.graph.loopless.irrefl v) D.two D.source_one D.reach

 

def path (D : WireConfiguration N finish) : List Triangle :=
  Classical.choose D.existsUniqueTrace

lemma path_trace (D : WireConfiguration N finish) :
    Trace D.graph.Adj (up 0 0) finish D.path :=
  (Classical.choose_spec D.existsUniqueTrace).1

lemma path_isPath (D : WireConfiguration N finish) (hf : finish ≠ up 0 0) :
    IsPath N finish D.path := by
  have h := D.path_trace
  refine ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.imp (fun {_ _} hvw => (D.allowed _ _ hvw).1),?_⟩
  intro v hv
  obtain ⟨w,hw⟩ := h.used_of_mem D.graph.symm hf.symm hv
  exact (D.allowed _ _ hw).2.1

lemma edges_iff (D : WireConfiguration N finish) (hf : finish ≠ up 0 0) (v w : Triangle) :
    D.graph.Adj v w ↔ Consecutive D.path v w :=
  D.path_trace.edges_iff D.graph.symm D.two D.source_one D.finish_one hf.symm D.drains v w

 
lemma support_eq (D : WireConfiguration N finish) (hf : finish ≠ up 0 0) :
    D.graph.support = {v | v ∈ D.path} := by
  ext v
  change (∃ w,D.graph.Adj v w) ↔ v ∈ D.path
  constructor
  · rintro ⟨w,hw⟩
    exact (consecutive_mem ((D.edges_iff hf v w).mp hw)).1
  · exact D.path_trace.used_of_mem D.graph.symm hf.symm

lemma support_finite (D : WireConfiguration N finish) (hf : finish ≠ up 0 0) :
    D.graph.support.Finite := by
  rw [D.support_eq hf]
  exact List.finite_toSet _

lemma support_ncard (D : WireConfiguration N finish) (hf : finish ≠ up 0 0) :
    D.graph.support.ncard = D.path.length := by
  rw [D.support_eq hf]
  have he : {v | v ∈ D.path} = (↑D.path.toFinset : Set Triangle) := by ext; simp
  rw [he,Set.ncard_coe_finset,List.toFinset_card_of_nodup D.path_trace.2.2.1]

 
def weight (D : WireConfiguration N finish) : ℝ := rho ^ D.graph.support.ncard

lemma weight_eq (D : WireConfiguration N finish) (hf : finish ≠ up 0 0) :
    D.weight = rho ^ D.path.length := by rw [weight,D.support_ncard hf]

lemma ofPath_trace {p : List Triangle} (hp : IsPath N finish p) :
    Trace (Consecutive p) (up 0 0) finish p :=
  ⟨hp.1,hp.2.1,hp.2.2.1,consecutive_chain p⟩

 

def ofPath {p : List Triangle} (hf : finish ≠ up 0 0) (hp : IsPath N finish p) :
    WireConfiguration N finish := by
  have h : Trace (Consecutive p) (up 0 0) finish p := ofPath_trace hp
  have hs : Std.Symm (Consecutive p) := ⟨fun _ _ => consecutive_symm⟩
  have hl : 0 < p.length := lt_of_lt_of_le (by omega) (h.length_two_le hf.symm)
  refine ⟨⟨Consecutive p,hs,⟨consecutive_irrefl hp.2.2.1⟩⟩,?_,consecutive_two hp.2.2.1,?_,?_,?_,?_,?_⟩
  · intro v w hvw
    obtain ⟨hv,hw⟩ := consecutive_mem hvw
    refine ⟨?_,hp.2.2.2.2 v hv,hp.2.2.2.2 w hw⟩
    obtain ⟨i,hi,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := hvw
    · exact List.isChain_iff_getElem.mp hp.2.2.2.1 i hi
    · exact adjacent_symmetric.symm _ _ (List.isChain_iff_getElem.mp hp.2.2.2.1 i hi)
  · simpa only [h.first hl] using consecutive_first_one hp.2.2.1 hl
  · simpa only [h.last (by omega)] using consecutive_last_one hp.2.2.1 hl
  · exact h.used_of_mem hs hf.symm (List.mem_of_getElem (h.first hl))
  · exact h.used_of_mem hs hf.symm (List.mem_of_getElem (h.last (by omega)))
  · intro v w hvw
    have : Std.Symm (Consecutive p) := hs
    exact symm (h.reach_of_mem (consecutive_mem hvw).1)

@[simp] lemma ofPath_graph {p : List Triangle} (hf : finish ≠ up 0 0)
    (hp : IsPath N finish p) (v w : Triangle) :
    (ofPath hf hp).graph.Adj v w ↔ Consecutive p v w := Iff.rfl

@[simp] theorem ofPath_path {p : List Triangle} (hf : finish ≠ up 0 0)
    (hp : IsPath N finish p) : (ofPath hf hp).path = p := by
  exact (ofPath hf hp).path_trace.unique (ofPath hf hp).graph.symm
    (ofPath hf hp).two (ofPath hf hp).source_one (ofPath_trace hp)

@[simp] theorem ofPath_path_isPath (D : WireConfiguration N finish) (hf : finish ≠ up 0 0) :
    ofPath hf (D.path_isPath hf) = D := by
  apply ext
  apply SimpleGraph.ext
  funext v w
  exact propext (D.edges_iff hf v w).symm

 

def equivPaths (N : ℕ) (finish : Triangle) (hf : finish ≠ up 0 0) :
    WireConfiguration N finish ≃ {p : List Triangle // IsPath N finish p} where
  toFun D := ⟨D.path,D.path_isPath hf⟩
  invFun p := ofPath hf p.property
  left_inv D := ofPath_path_isPath D hf
  right_inv p := Subtype.ext (ofPath_path hf p.property)

end WireConfiguration
end

 

 

noncomputable section
open scoped Classical BigOperators

namespace WireConfiguration

lemma countable (N : ℕ) (finish : Triangle) (hf : finish ≠ up 0 0) :
    Countable (WireConfiguration N finish) :=
  (equivPaths N finish hf).countable_iff.mpr inferInstance

lemma summable_weight_iff (N : ℕ) (finish : Triangle) (hf : finish ≠ up 0 0) :
    Summable (weight (N := N) (finish := finish)) ↔
      Summable (fun p : List Triangle => if IsPath N finish p then rho ^ p.length else 0) := by
  have he := (equivPaths N finish hf).summable_iff
    (f := fun p : {p : List Triangle // IsPath N finish p} => rho ^ p.val.length)
  have hs := summable_subtype_iff_indicator
    (f := fun p : List Triangle => rho ^ p.length)
    (s := {p | IsPath N finish p})
  have hw : (fun p : {p : List Triangle // IsPath N finish p} => rho ^ p.val.length) ∘
      (equivPaths N finish hf) = weight := by
    funext D
    exact (D.weight_eq hf).symm
  rw [hw] at he
  exact he.trans hs

lemma tsum_weight (N : ℕ) (finish : Triangle) (hf : finish ≠ up 0 0) :
    ∑' D : WireConfiguration N finish, D.weight =
      ∑' p : List Triangle, if IsPath N finish p then rho ^ p.length else 0 := by
  calc
    _ = ∑' D : WireConfiguration N finish, rho ^ D.path.length :=
      tsum_congr (fun D => D.weight_eq hf)
    _ = ∑' p : {p : List Triangle // IsPath N finish p}, rho ^ p.val.length :=
      (equivPaths N finish hf).tsum_eq (fun p => rho ^ p.val.length)
    _ = _ := tsum_subtype {p | IsPath N finish p} (fun p => rho ^ p.length)

 

theorem arch_sum (N : ℕ) (k : ℤ) (hk : k ≠ 0) :
    K N k = ∑' D : WireConfiguration N (up k 0), D.weight := by
  have hf : up k 0 ≠ up 0 0 := by simpa [up] using hk
  rw [tsum_weight N (up k 0) hf]
  apply tsum_congr
  intro p
  simp [archWeight,hk]

theorem arch_summable (N : ℕ) (k : ℤ) (hk : k ≠ 0) :
    Summable (archWeight N k) ↔ Summable (weight (N := N) (finish := up k 0)) := by
  have hf : up k 0 ≠ up 0 0 := by simpa [up] using hk
  rw [show archWeight N k = (fun p => if IsPath N (up k 0) p then rho ^ p.length else 0) from
    funext (fun p => by simp [archWeight,hk])]
  exact (summable_weight_iff N (up k 0) hf).symm

theorem bridge_sum (N : ℕ) (hN : 1 ≤ N) (k : ℤ) :
    bridgeKernel N k = ∑' D : WireConfiguration N (down k (N-1)), D.weight := by
  have hf : down k (N-1) ≠ up 0 0 := by simp [down,up]
  rw [tsum_weight N (down k (N-1)) hf]
  apply tsum_congr
  intro p
  simp [bridgeWeight,show 0<N by omega]

theorem bridge_summable (N : ℕ) (hN : 1 ≤ N) (k : ℤ) :
    Summable (bridgeWeight N k) ↔
      Summable (weight (N := N) (finish := down k (N-1))) := by
  have hf : down k (N-1) ≠ up 0 0 := by simp [down,up]
  rw [show bridgeWeight N k = (fun p => if IsPath N (down k (N-1)) p then rho ^ p.length else 0) from
    funext (fun p => by simp [bridgeWeight,show 0<N by omega])]
  exact (summable_weight_iff N (down k (N-1)) hf).symm

end WireConfiguration
end

 

 

noncomputable section
open scoped Classical BigOperators
open Diagram.PathGraph

lemma Diagram.PathGraph.Trace.two_neighbors {V : Type*} {r : V → V → Prop} (hs : Std.Symm r)
    {a b : V} {p : List V} (hp : Trace r a b p) {v : V}
    (hv : v ∈ p) (ha : v ≠ a) (hb : v ≠ b) :
    ∃ x y, r v x ∧ r v y ∧ x ≠ y := by
  obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hv
  have hz : 0 < i := by
    by_contra h
    have he : i=0 := by omega
    exact ha (by simpa only [he] using hp.first (by omega))
  have ht : i+1 < p.length := by
    by_contra h
    have he : i=p.length-1 := by omega
    exact hb (by simpa only [he] using hp.last (by omega))
  have hc := List.isChain_iff_getElem.mp hp.2.2.2
  refine ⟨p[i-1],p[i+1],?_,hc i ht,?_⟩
  · have he : i-1+1=i := by omega
    simpa only [he] using hs.symm _ _ (hc (i-1) (by omega))
  · intro he
    have := hp.2.2.1.getElem_inj_iff.mp he
    omega

namespace WireConfiguration
variable {N : ℕ} {finish : Triangle}

lemma another_neighbor (D : WireConfiguration N finish) (hf : finish ≠ up 0 0)
    {v w : Triangle} (hvw : D.graph.Adj v w) (ha : v ≠ up 0 0) (hb : v ≠ finish) :
    ∃ z, D.graph.Adj v z ∧ z ≠ w := by
  obtain ⟨x,y,hx,hy,hxy⟩ := D.path_trace.two_neighbors D.graph.symm
    (consecutive_mem ((D.edges_iff hf v w).mp hvw)).1 ha hb
  by_cases h : x=w
  · exact ⟨y,hy,by simpa only [←h] using hxy.symm⟩
  · exact ⟨x,hx,h⟩

end WireConfiguration

lemma adjacent_up_iff (i : ℤ) (j : ℕ) (w : Triangle) :
    adjacent (up i j) w ↔ w=down i j ∨ w=down (i-1) j ∨
      (0<j ∧ w=down i (j-1)) := by
  rcases w with ⟨k,l,b⟩
  cases b <;> simp only [adjacent,upDownAdjacent,up,down,Prod.mk.injEq,Bool.false_eq_true,
    Bool.true_eq_false,true_and,false_and,or_false,and_true,and_false]
  all_goals omega

lemma adjacent_down_iff (i : ℤ) (j : ℕ) (w : Triangle) :
    adjacent (down i j) w ↔ w=up i j ∨ w=up (i+1) j ∨ w=up i (j+1) := by
  rcases w with ⟨k,l,b⟩
  cases b <;> simp only [adjacent,upDownAdjacent,up,down,Prod.mk.injEq,Bool.false_eq_true,
    Bool.true_eq_false,true_and,false_and,false_or,or_false,and_true,and_false]
  all_goals omega

end
end CriticalStrip

end OAI
