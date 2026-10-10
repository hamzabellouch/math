import Mathlib
import OAI.Combinatorics.ThinTrees.Continuation.Interior

namespace OAI

/-! Rooted orientation. -/

section

namespace AlgorithmicThinTrees.Orientations
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical
variable {n m : ℕ}

def adjacency (G : MultiGraph n m) (T : Finset (Fin m)) : SimpleGraph (Fin n) where
  Adj a b := ∃e ∈ T, (G.left e=a ∧ G.right e=b) ∨ (G.right e=a ∧ G.left e=b)
  symm := ⟨by rintro a b ⟨e,he,h|h⟩ <;> exact ⟨e,he,by tauto⟩⟩
  loopless := ⟨by
    intro a
    rintro ⟨e,he,h|h⟩
    · exact G.loopless e (h.1.trans h.2.symm)
    · exact G.loopless e (h.2.trans h.1.symm)⟩

lemma reachable (G : MultiGraph n m) {T : Finset (Fin m)} (hT : G.Connected T)
    (v root : Fin n) : (adjacency G T).Reachable v root := by
  let S : Finset (Fin n) := univ.filter (fun w => (adjacency G T).Reachable w root)
  have hr : root ∈ S := by simp only [S,mem_filter,mem_univ,true_and]; exact .refl root
  by_contra hv
  have hv' : v ∉ S := by simpa only [S,mem_filter,mem_univ,true_and] using hv
  have hSne : S ≠ univ := by intro he; exact hv' (he ▸ mem_univ v)
  obtain ⟨e,he⟩ := hT S ⟨root,hr⟩ hSne
  obtain ⟨heT,hecut⟩ := mem_filter.mp he
  have hadj : (adjacency G T).Adj (G.left e) (G.right e) := ⟨e,heT,Or.inl ⟨rfl,rfl⟩⟩
  rcases hecut with ⟨hl,hr⟩ | ⟨hr,hl⟩
  · have h := hadj.reachable.symm.trans ((mem_filter.mp hl).2)
    exact hr (mem_filter.mpr ⟨mem_univ _,h⟩)
  · have h := hadj.reachable.trans ((mem_filter.mp hr).2)
    exact hl (mem_filter.mpr ⟨mem_univ _,h⟩)

lemma parent_exists (G : MultiGraph n m) {T : Finset (Fin m)} (hT : G.Connected T)
    (root : Fin n) (v : Fin n) (hv : v ≠ root) :
    ∃e ∈ T,
      (G.left e=v ∧ (adjacency G T).dist (G.right e) root < (adjacency G T).dist v root) ∨
      (G.right e=v ∧ (adjacency G T).dist (G.left e) root < (adjacency G T).dist v root) := by
  obtain ⟨p,hp⟩ := (reachable G hT v root).exists_walk_length_eq_dist
  cases p with
  | nil => exact (hv rfl).elim
  | @cons v w root h p =>
    obtain ⟨e,he,h|h⟩ := h
    · refine ⟨e,he,Or.inl ⟨h.1,?_⟩⟩
      rw [h.2]
      exact lt_of_le_of_lt (SimpleGraph.dist_le p) (by simpa using hp.symm ▸ Nat.lt_succ_self p.length)
    · refine ⟨e,he,Or.inr ⟨h.1,?_⟩⟩
      rw [h.2]
      exact lt_of_le_of_lt (SimpleGraph.dist_le p) (by simpa using hp.symm ▸ Nat.lt_succ_self p.length)

structure Rooted (G : MultiGraph n m) (T : Finset (Fin m)) (root : Fin n) where
  tail : T ≃ {v : Fin n // v ≠ root}
  endpoint : ∀e : T, (tail e).val=G.left e ∨ (tail e).val=G.right e

lemma rooted_exists (G : MultiGraph n m) {T : Finset (Fin m)} (hT : G.SpanningTree T)
    (root : Fin n) : Nonempty (Rooted G T root) := by
  choose f hf using fun v : {v : Fin n // v ≠ root} => parent_exists G hT.1 root v v.property
  let F : {v : Fin n // v ≠ root} → T := fun v => ⟨f v,(hf v).1⟩
  have hi : Function.Injective F := by
    intro v w he
    have he' : f v=f w := congrArg Subtype.val he
    obtain hvl|hvr := (hf v).2
    obtain hwl|hwr := (hf w).2
    · apply Subtype.ext
      exact hvl.1.symm.trans (he' ▸ hwl.1)
    · have h1 := hvl.2
      have h2 := hwr.2
      rw [he',hwr.1] at h1
      rw [←he',hvl.1] at h2
      omega
    obtain hwl|hwr := (hf w).2
    · have h1 := hvr.2
      have h2 := hwl.2
      rw [he',hwl.1] at h1
      rw [←he',hvr.1] at h2
      omega
    · apply Subtype.ext
      exact hvr.1.symm.trans (he' ▸ hwr.1)
  have hc : Fintype.card {v : Fin n // v ≠ root}=Fintype.card T := by
    rw [Fintype.card_subtype_compl,Fintype.card_fin,Fintype.card_subtype_eq root,
      Fintype.card_coe,G.spanningTree_card (Fin.pos root) hT]
  let E := Equiv.ofBijective F ⟨hi,(Fintype.bijective_iff_injective_and_card F).mpr ⟨hi,hc⟩ |>.2⟩
  refine ⟨⟨E.symm,fun e => ?_⟩⟩
  have he : f (E.symm e)=e := congrArg Subtype.val (E.apply_symm_apply e)
  obtain h|h := (hf (E.symm e)).2
  · exact Or.inl (h.1.symm.trans (congrArg G.left he))
  · exact Or.inr (h.1.symm.trans (congrArg G.right he))

end
end AlgorithmicThinTrees.Orientations
end

end OAI
