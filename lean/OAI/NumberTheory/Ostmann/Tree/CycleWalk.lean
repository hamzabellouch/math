import OAI.NumberTheory.Ostmann.Tree.CycleExistence
import OAI.NumberTheory.Ostmann.Tree.CycleSigned

namespace OAI

namespace Ostmann.Tree

lemma cyclic_edge_injective {E V W I : Type*} (left : E → V) (right : E → W)
    (next : Equiv.Perm I) (vertex : I → V ⊕ W) (edge : I → E)
    (hv : Function.Injective vertex) (hn : ∀ i, next (next i) ≠ i)
    (hi : ∀ i,
      (vertex i=Sum.inl (left (edge i)) ∧ vertex (next i)=Sum.inr (right (edge i))) ∨
      (vertex i=Sum.inr (right (edge i)) ∧ vertex (next i)=Sum.inl (left (edge i)))) :
    Function.Injective edge := by
  intro i j he
  rcases hi i with h | h <;> rcases hi j with h' | h'
  · apply hv
    rw [h.1,h'.1,he]
  · have hij : i=next j := hv (by rw [h.1,h'.2,he])
    have hji : next i=j := hv (by rw [h.2,h'.1,he])
    exact False.elim (hn i (by rw [hji,← hij]))
  · have hij : i=next j := hv (by rw [h.1,h'.2,he])
    have hji : next i=j := hv (by rw [h.2,h'.1,he])
    exact False.elim (hn i (by rw [hji,← hij]))
  · apply hv
    rw [h.1,h'.1,he]

lemma zmod_add_one_twice_ne {n : ℕ} (hn : 3 ≤ n) (i : ZMod n) :
    i+1+1 ≠ i := by
  intro he
  have hz : (2:ZMod n)=0 := by linear_combination he
  have hv := congrArg ZMod.val hz
  rw [ZMod.val_two_eq_two_mod,Nat.mod_eq_of_lt (by omega : 2<n)] at hv
  simp at hv

lemma cycle_adj_next {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) [NeZero p.length] (i : ZMod p.length) :
    G.Adj (p.getVert i.val) (p.getVert (i+1).val) := by
  have hn := hp.three_le_length
  have hval := ZMod.val_lt i
  have hone : (1:ZMod p.length).val=1 := ZMod.val_one'' (by omega)
  by_cases h : i.val+1 < p.length
  · rw [ZMod.val_add_of_lt (by rwa [hone]),hone]
    exact p.adj_getVert_succ hval
  · have he : i.val+1=p.length := by omega
    have hz : (i+1).val=0 := by
      rw [ZMod.val_add_of_le (by rw [hone]; omega),hone,he,Nat.sub_self]
    rw [hz,p.getVert_zero]
    have ha := p.adj_getVert_succ hval
    simpa only [he,p.getVert_length] using ha

noncomputable def CyclicIncidence.ofWalk {E V W : Type*}
    (left : E → V) (right : E → W) {v : V ⊕ W}
    (p : (incidenceGraph left right).Walk v v) (hp : p.IsCycle)
    [NeZero p.length] : CyclicIncidence (I := ZMod p.length) left right := by
  classical
  let vertex : ZMod p.length → V ⊕ W := fun i => p.getVert i.val
  have hv : Function.Injective vertex := by
    intro i j h
    apply ZMod.val_injective p.length
    apply hp.getVert_injOn' _ _ h
    · have := ZMod.val_lt i
      simp only [Set.mem_ofPred_eq]
      omega
    · have := ZMod.val_lt j
      simp only [Set.mem_ofPred_eq]
      omega
  have hex : ∀ i : ZMod p.length, ∃ e : E,
      (vertex i=Sum.inl (left e) ∧ vertex (i+1)=Sum.inr (right e)) ∨
      (vertex i=Sum.inr (right e) ∧ vertex (i+1)=Sum.inl (left e)) := by
    intro i
    have ha := cycle_adj_next p hp i
    change (incidenceGraph left right).Adj (vertex i) (vertex (i+1)) at ha
    cases h : vertex i with
    | inl a =>
      cases h' : vertex (i+1) with
      | inl b =>
        rw [h,h'] at ha
        exact False.elim ha
      | inr b =>
        rw [h,h'] at ha
        obtain ⟨e,he,he'⟩ : ∃e,left e=a ∧ right e=b := ha
        exact ⟨e,Or.inl ⟨by simp [he],by simp [he']⟩⟩
    | inr b =>
      cases h' : vertex (i+1) with
      | inl a =>
        rw [h,h'] at ha
        obtain ⟨e,he,he'⟩ : ∃e,left e=a ∧ right e=b := ha
        exact ⟨e,Or.inr ⟨by simp [he'],by simp [he]⟩⟩
      | inr a =>
        rw [h,h'] at ha
        exact False.elim ha
  let edge := fun i => Classical.choose (hex i)
  have hi := fun i => Classical.choose_spec (hex i)
  refine ⟨Equiv.addRight 1,vertex,hv,edge,?_,hi⟩
  apply cyclic_edge_injective left right (Equiv.addRight 1) vertex edge hv
  · exact zmod_add_one_twice_ne hp.three_le_length
  · exact hi

theorem exists_balanced_selection {E V W : Type*}
    [Fintype E] [Fintype V] [Fintype W] [Nonempty E]
    [DecidableEq E] [DecidableEq V] [DecidableEq W]
    (left : E → V) (right : E → W)
    (hcard : Fintype.card V+Fintype.card W ≤ Fintype.card E) :
    Nonempty (BalancedSelection left right) := by
  classical
  rcases incidence_cycle_or_parallel left right hcard with h | ⟨v,p,hp⟩
  · obtain ⟨e,f,hef,hl,hr⟩ := h
    exact ⟨BalancedSelection.of_parallel e f hef hl hr⟩
  · let : NeZero p.length := ⟨by have := hp.three_le_length; omega⟩
    exact ⟨(CyclicIncidence.ofWalk left right p hp).toBalanced⟩

end Ostmann.Tree

end OAI
