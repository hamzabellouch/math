import OAI.NumberTheory.Ostmann.Tree.CycleSelection

namespace OAI

namespace Ostmann.Tree
open Finset

structure CyclicIncidence {E V W I : Type*} (left : E → V) (right : E → W) where
  next : Equiv.Perm I
  vertex : I → V ⊕ W
  vertex_injective : Function.Injective vertex
  edge : I → E
  edge_injective : Function.Injective edge
  incidence : ∀ i,
    (vertex i=Sum.inl (left (edge i)) ∧ vertex (next i)=Sum.inr (right (edge i))) ∨
    (vertex i=Sum.inr (right (edge i)) ∧ vertex (next i)=Sum.inl (left (edge i)))

namespace CyclicIncidence
variable {E V W I : Type*} [Fintype I] [Nonempty I]
  [DecidableEq E] [DecidableEq V] [DecidableEq W]
  {left : E → V} {right : E → W}
variable (c : CyclicIncidence (I := I) left right)

noncomputable def positive : Finset E :=
  (univ.filter (fun i => (c.vertex i).isLeft)).image c.edge
noncomputable def negative : Finset E :=
  (univ.filter (fun i => (c.vertex i).isRight)).image c.edge

omit [Fintype I] [Nonempty I] [DecidableEq E] [DecidableEq V] [DecidableEq W] in
lemma left_positive_iff (i : I) (v : V) :
    ((c.vertex i).isLeft ∧ left (c.edge i)=v) ↔ c.vertex i=Sum.inl v := by
  rcases c.incidence i with h | h <;> simp [h.1]
omit [Fintype I] [Nonempty I] [DecidableEq E] [DecidableEq V] [DecidableEq W] in
lemma left_negative_iff (i : I) (v : V) :
    ((c.vertex i).isRight ∧ left (c.edge i)=v) ↔ c.vertex (c.next i)=Sum.inl v := by
  rcases c.incidence i with h | h <;> simp [h.1,h.2]
omit [Fintype I] [Nonempty I] [DecidableEq E] [DecidableEq V] [DecidableEq W] in
lemma right_positive_iff (i : I) (w : W) :
    ((c.vertex i).isLeft ∧ right (c.edge i)=w) ↔ c.vertex (c.next i)=Sum.inr w := by
  rcases c.incidence i with h | h <;> simp [h.1,h.2]
omit [Fintype I] [Nonempty I] [DecidableEq E] [DecidableEq V] [DecidableEq W] in
lemma right_negative_iff (i : I) (w : W) :
    ((c.vertex i).isRight ∧ right (c.edge i)=w) ↔ c.vertex i=Sum.inr w := by
  rcases c.incidence i with h | h <;> simp [h.1]

omit [Fintype I] [Nonempty I] [DecidableEq V] [DecidableEq W] in
lemma filter_image_card (s : Finset I) (p : E → Prop) [DecidablePred p] :
    ((s.image c.edge).filter p).card = (s.filter (fun i => p (c.edge i))).card := by
  rw [filter_image, card_image_of_injective _ c.edge_injective]

omit [Nonempty I] in
lemma left_positive_card (v : V) :
    (c.positive.filter (fun e => left e=v)).card =
      (univ.filter (fun i => c.vertex i=Sum.inl v)).card := by
  classical
  rw [positive,c.filter_image_card,filter_filter]
  congr 1
  ext i
  simp only [mem_filter,mem_univ,true_and,c.left_positive_iff]

omit [Nonempty I] in
lemma left_negative_card (v : V) :
    (c.negative.filter (fun e => left e=v)).card =
      (univ.filter (fun i => c.vertex (c.next i)=Sum.inl v)).card := by
  classical
  rw [negative,c.filter_image_card,filter_filter]
  congr 1
  ext i
  simp only [mem_filter,mem_univ,true_and,c.left_negative_iff]

omit [Nonempty I] in
lemma right_positive_card (w : W) :
    (c.positive.filter (fun e => right e=w)).card =
      (univ.filter (fun i => c.vertex (c.next i)=Sum.inr w)).card := by
  classical
  rw [positive,c.filter_image_card,filter_filter]
  congr 1
  ext i
  simp only [mem_filter,mem_univ,true_and,c.right_positive_iff]

omit [Nonempty I] in
lemma right_negative_card (w : W) :
    (c.negative.filter (fun e => right e=w)).card =
      (univ.filter (fun i => c.vertex i=Sum.inr w)).card := by
  classical
  rw [negative,c.filter_image_card,filter_filter]
  congr 1
  ext i
  simp only [mem_filter,mem_univ,true_and,c.right_negative_iff]

omit [Nonempty I] [DecidableEq E] in
lemma next_vertex_card (v : V ⊕ W) :
    (univ.filter (fun i => c.vertex (c.next i)=v)).card =
      (univ.filter (fun i => c.vertex i=v)).card := by
  classical
  apply card_bij (fun i _ => c.next i)
  · intro i hi
    simpa only [mem_filter,mem_univ,true_and] using hi
  · intro i hi j hj he
    exact c.next.injective he
  · intro j hj
    refine ⟨c.next.symm j, ?_, by simp⟩
    simpa only [mem_filter,mem_univ,true_and,Equiv.apply_symm_apply] using hj

omit [Nonempty I] [DecidableEq E] in
lemma vertex_fiber_card (v : V ⊕ W) :
    (univ.filter (fun i => c.vertex i=v)).card ≤ 1 := by
  classical
  apply card_le_one.mpr
  intro i hi j hj
  exact c.vertex_injective ((mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm)

omit [Nonempty I] [DecidableEq V] [DecidableEq W] in
lemma signs_disjoint : Disjoint c.positive c.negative := by
  classical
  apply disjoint_left.mpr
  intro e he hn
  obtain ⟨i,hi,hie⟩ := mem_image.mp he
  obtain ⟨j,hj,hje⟩ := mem_image.mp hn
  have hij := c.edge_injective (hie.trans hje.symm)
  subst j
  have hleft := (mem_filter.mp hi).2
  have hright := (mem_filter.mp hj).2
  cases h : c.vertex i <;> simp [h] at hleft hright

omit [DecidableEq V] [DecidableEq W] in
lemma positive_nonempty : c.positive.Nonempty := by
  classical
  let i : I := Classical.choice (inferInstance : Nonempty I)
  rcases c.incidence i with h | h
  · exact ⟨c.edge i,mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,by simp [h.1]⟩,rfl⟩⟩
  · exact ⟨c.edge (c.next i),mem_image.mpr
      ⟨c.next i,mem_filter.mpr ⟨mem_univ _,by simp [h.2]⟩,rfl⟩⟩

noncomputable def toBalanced : BalancedSelection left right where
  positive := c.positive
  negative := c.negative
  disjoint := c.signs_disjoint
  nonempty := c.positive_nonempty
  left_balance := by intro v; rw [c.left_positive_card,c.left_negative_card,c.next_vertex_card]
  left_bound := by intro v; rw [c.left_positive_card]; exact c.vertex_fiber_card _
  right_balance := by intro w; rw [c.right_positive_card,c.right_negative_card,c.next_vertex_card]
  right_bound := by intro w; rw [c.right_positive_card,c.next_vertex_card]; exact c.vertex_fiber_card _

end CyclicIncidence
end Ostmann.Tree

end OAI
