import OAI.NumberTheory.TwoPoint.Bounds.LabeledForest
import OAI.NumberTheory.TwoPoint.Walks.ForestLeaves

namespace OAI

/-! Every finite acyclic graph has a labeled ordered-forest representation. -/

namespace TwoPointCorrelations

open SimpleGraph BinaryTree

universe u

/-- The labels are a permutation of the vertices and adjacency is exactly
parent/child incidence in the ordered forest. -/
theorem exists_forest_representation {V : Type u} [Fintype V]
    (G : SimpleGraph V) (hG : G.IsAcyclic) :
    ∃ t : BinaryTree V, (forestNodes t).Nodup ∧ (∀ v, v ∈ forestNodes t) ∧
      ∀ a b, forestAdjacent t a b ↔ G.Adj a b := by
  classical
  suffices h : ∀ n : ℕ, ∀ (V : Type u) [Fintype V], Fintype.card V = n →
      ∀ (G : SimpleGraph V), G.IsAcyclic →
        ∃ t : BinaryTree V, (forestNodes t).Nodup ∧ (∀ v, v ∈ forestNodes t) ∧
          ∀ a b, forestAdjacent t a b ↔ G.Adj a b by
    exact h _ V rfl G hG
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V inst hcard G hG
    by_cases hn : n = 0
    · let : IsEmpty V := Fintype.card_eq_zero_iff.mp (hcard.trans hn)
      exact ⟨.nil, by simp [forestNodes], isEmptyElim, fun a => isEmptyElim a⟩
    · let : Nonempty V := Fintype.card_pos_iff.mp (by omega)
      obtain ⟨x, hx⟩ := finite_forest_has_leaf G hG
      let W := {v : V // v ≠ x}
      let H : SimpleGraph W := G.comap Subtype.val
      have hW : Fintype.card W < n := by
        rw [← hcard]
        exact Fintype.card_subtype_lt (x := x) (by simp)
      have hH : H.IsAcyclic := hG.of_comap ⟨Subtype.val, Subtype.val_injective⟩
      obtain ⟨t, ht, hcover, hadj⟩ := ih (Fintype.card W) hW W rfl H hH
      let u := t.map (Subtype.val : W → V)
      have hu : (forestNodes u).Nodup := by
        rw [forestNodes_map]
        exact ht.map Subtype.val_injective
      have hnx : x ∉ forestNodes u := by
        rw [forestNodes_map, List.mem_map]
        rintro ⟨v, _, hv⟩
        exact v.property hv
      have hcov (v : V) (hv : v ≠ x) : v ∈ forestNodes u := by
        rw [forestNodes_map]
        exact List.mem_map.mpr ⟨⟨v, hv⟩, hcover _, rfl⟩
      have hOld (a b : V) : forestAdjacent u a b ↔ a ≠ x ∧ b ≠ x ∧ G.Adj a b := by
        constructor
        · intro h
          have hm := forestAdjacent_mem u h
          have ha : a ≠ x := by intro hax; subst a; exact hnx hm.1
          have hb : b ≠ x := by intro hbx; subst b; exact hnx hm.2
          refine ⟨ha, hb, ?_⟩
          have hh := (forestAdjacent_map (Subtype.val : W → V) Subtype.val_injective t
            (⟨a, ha⟩ : W) (⟨b, hb⟩ : W)).mp h
          exact (hadj _ _).mp hh
        · rintro ⟨ha, hb, h⟩
          exact (forestAdjacent_map (Subtype.val : W → V) Subtype.val_injective t
            (⟨a, ha⟩ : W) (⟨b, hb⟩ : W)).mpr ((hadj _ _).mpr h)
      by_cases hneigh : ∃ p, G.Adj x p
      · obtain ⟨p, hxp⟩ := hneigh
        have hp : p ≠ x := hxp.ne.symm
        let s := attachForestLeaf p x u
        have hsperm := attachForestLeaf_nodes_perm p x u hu (hcov p hp)
        refine ⟨s, attachForestLeaf_nodup p x u hu (hcov p hp) hnx, ?_, ?_⟩
        · intro v
          apply hsperm.mem_iff.mpr
          by_cases hv : v = x
          · simp [hv]
          · simp [hcov v hv]
        · intro a b
          rw [attachForestLeaf_adjacent p x u hu (hcov p hp), hOld]
          constructor
          · rintro (⟨_, _, hab⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
            · exact hab
            · exact hxp.symm
            · exact hxp
          · intro hab
            by_cases ha : a = x
            · right; right
              subst a
              exact ⟨(hx b p hab hxp), rfl⟩
            · by_cases hb : b = x
              · right; left
                subst b
                exact ⟨hx a p hab.symm hxp, rfl⟩
              · exact Or.inl ⟨ha, hb, hab⟩
      · refine ⟨.node x .nil u, ?_, ?_, ?_⟩
        · simpa only [forestNodes, List.nil_append] using List.nodup_cons.mpr ⟨hnx, hu⟩
        · intro v
          by_cases hv : v = x
          · simp [forestNodes, hv]
          · simp [forestNodes, hcov v hv]
        · intro a b
          simp only [forestAdjacent, forestRoots, List.not_mem_nil, and_false, false_or]
          rw [hOld]
          constructor
          · exact And.right ∘ And.right
          · intro hab
            have ha : a ≠ x := by intro heq; subst a; exact hneigh ⟨b, hab⟩
            have hb : b ≠ x := by intro heq; subst b; exact hneigh ⟨a, hab.symm⟩
            exact ⟨ha, hb, hab⟩

lemma forest_representation_numNodes {V : Type*} [Fintype V] (t : BinaryTree V)
    (ht : (forestNodes t).Nodup) (hcover : ∀ v, v ∈ forestNodes t) :
    t.numNodes = Fintype.card V := by
  rw [← forestNodes_length]
  apply le_antisymm ht.length_le_card
  have hsurj : Function.Surjective (fun i : Fin (forestNodes t).length => (forestNodes t).get i) := by
    intro v
    exact List.mem_iff_get.mp (hcover v)
  simpa only [Fintype.card_fin] using Fintype.card_le_of_surjective _ hsurj

end TwoPointCorrelations

end OAI
