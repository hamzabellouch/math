import Mathlib

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PlanarRecursion
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*}

lemma exists_distance_parent (G : SimpleGraph V) (hG : G.Connected)
    (root v : V) (hv : v ≠ root) :
    ∃ w, G.Adj v w ∧ G.dist root w + 1 = G.dist root v := by
  obtain ⟨p,hp⟩ := hG.exists_walk_length_eq_dist v root
  cases p with
  | nil => exact (hv rfl).elim
  | @cons v w root h p =>
    refine ⟨w,h,?_⟩
    have hh := dist_le p
    have hd := h.diff_dist_adj (u := root)
    rw [G.dist_comm (u := w) (v := root)] at hh
    rw [G.dist_comm (u := v) (v := root)] at hp
    simp only [Walk.length_cons] at hp
    omega

variable [Fintype V]

/-- A literal shortest-path spanning tree of a finite connected graph.
Root distances are preserved exactly, not merely bounded by the number of
vertices. This is the radius-control input for the planar separator. -/
theorem exists_bfs_tree (G : SimpleGraph V) (hG : G.Connected) (root : V) :
    ∃ T : SimpleGraph V, T ≤ G ∧ T.IsTree ∧ ∀ v, T.dist root v = G.dist root v := by
  classical
  have : Nonempty V := ⟨root⟩
  let parent : V → V := fun v => if h : v = root then root else
    (exists_distance_parent G hG root v h).choose
  have hp : ∀ v, v ≠ root → G.Adj v (parent v) ∧
      G.dist root (parent v)+1 = G.dist root v := by
    intro v hv
    dsimp only [parent]
    rw [dite_eq_right hv]
    exact (exists_distance_parent G hG root v hv).choose_spec
  let T : SimpleGraph V := {
    Adj := fun v w => (v ≠ root ∧ parent v = w) ∨ (w ≠ root ∧ parent w = v)
    symm := ⟨by intro v w h; exact h.elim Or.inr Or.inl⟩
    loopless := ⟨by
      intro v h
      rcases h with ⟨hv,he⟩ | ⟨hv,he⟩ <;>
        exact (hp v hv).1.ne he.symm⟩ }
  have hle : T ≤ G := by
    intro v w h
    rcases h with ⟨hv,rfl⟩ | ⟨hw,rfl⟩
    · exact (hp v hv).1
    · exact (hp w hw).1.symm
  have hpaths : ∀ v, ∃ p : T.Walk v root, p.length = G.dist root v := by
    intro v
    generalize hn : G.dist root v = n
    induction n using Nat.strong_induction_on generalizing v with
    | h n ih =>
      by_cases hv : v = root
      · subst v
        exact ⟨.nil,by simpa only [Walk.length_nil,SimpleGraph.dist_self] using hn⟩
      · have hd := (hp v hv).2
        obtain ⟨p,hp'⟩ := ih (G.dist root (parent v)) (by omega) (parent v) rfl
        exact ⟨p.cons (Or.inl ⟨hv,rfl⟩),by simp only [Walk.length_cons,hp']; omega⟩
  have hconn : T.Connected := by
    apply Connected.mk
    intro v w
    exact (show T.Reachable v root from ⟨(hpaths v).choose⟩).trans
      (show T.Reachable w root from ⟨(hpaths w).choose⟩).symm
  have hcard : Nat.card T.edgeSet + 1 ≤ Nat.card V := by
    let E := (Finset.univ.erase root).image (fun v => s(v,parent v))
    have hsub : T.edgeFinset ⊆ E := by
      intro e he
      induction e using Sym2.inductionOn with
      | hf v w =>
        have hadj : T.Adj v w := by simpa using he
        rcases hadj with ⟨hv,rfl⟩ | ⟨hw,rfl⟩
        · exact Finset.mem_image.mpr ⟨v,Finset.mem_erase.mpr ⟨hv,Finset.mem_univ _⟩,rfl⟩
        · exact Finset.mem_image.mpr ⟨w,Finset.mem_erase.mpr ⟨hw,Finset.mem_univ _⟩,Sym2.eq_swap⟩
    have hh := (Finset.card_le_card hsub).trans (Finset.card_image_le (s := Finset.univ.erase root)
      (f := fun v => s(v,parent v)))
    have he : (Finset.univ.erase root).card + 1 = Fintype.card V := by
      have hh : 0 < Fintype.card V := Fintype.card_pos
      simp only [Finset.card_erase_of_mem (Finset.mem_univ root),Finset.card_univ]
      omega
    rw [edgeFinset_card] at hh
    simp only [Nat.card_eq_fintype_card]
    omega
  have hT : T.IsTree := by
    apply isTree_iff_connected_and_card.mpr
    exact ⟨hconn,Nat.le_antisymm hcard hconn.card_vert_le_card_edgeSet_add_one⟩
  refine ⟨T,hle,hT,?_⟩
  intro v
  apply le_antisymm
  · obtain ⟨p,hp'⟩ := hpaths v
    simpa only [T.dist_comm (u := v) (v := root),hp'] using dist_le p
  · exact (hconn root v).dist_anti hle

end HyperbolicObstruction.PlanarRecursion
end
end

section

end
end

end OAI
