import OAI.NumberTheory.Ostmann.Tree.ArrangementGraph

namespace OAI

/-! # Transporting actual overlap graphs along a leaf enumeration -/

namespace Ostmann

noncomputable def reindexArrangement {L L' : Type*} (f : L ≃ L') {m : ℕ}
    (e : Equiv.Perm (L × Fin m)) : Equiv.Perm (L' × Fin m) :=
  ((f.symm.prodCongr (Equiv.refl _)).trans e).trans (f.prodCongr (Equiv.refl _))

@[simp] theorem reindexArrangement_eq_iff {L L' : Type*} (f : L ≃ L') {m : ℕ}
    (e : Equiv.Perm (L × Fin m)) (a b : L) (i j : Fin m) :
    reindexArrangement f e (f a, i) = (f b, j) ↔ e (a, i) = (b, j) := by
  change (f.prodCongr (Equiv.refl _)) (e (f.symm (f a), i)) =
    (f.prodCongr (Equiv.refl _)) (b, j) ↔ _
  rw [f.symm_apply_apply, Equiv.apply_eq_iff_eq]

noncomputable def arrangementGraphReindex {L L' : Type*} (f : L ≃ L') {m : ℕ}
    (e : Equiv.Perm (L × Fin m)) :
    arrangementGraph m e ≃g arrangementGraph m (reindexArrangement f e) where
  toEquiv := f.sumCongr f
  map_rel_iff' := by
    intro x y
    cases x with
    | inl a =>
      cases y with
      | inl b => rfl
      | inr b =>
        change (∃ i j, reindexArrangement f e (f a, i) = (f b, j)) ↔
          ∃ i j, e (a, i) = (b, j)
        simp only [reindexArrangement_eq_iff]
    | inr b =>
      cases y with
      | inl a =>
        change (∃ i j, reindexArrangement f e (f a, i) = (f b, j)) ↔
          ∃ i j, e (a, i) = (b, j)
        simp only [reindexArrangement_eq_iff]
      | inr a => rfl

theorem arrangement_component_count_reindex {L L' : Type*} [Fintype L] [Fintype L']
    (f : L ≃ L') {m : ℕ} (e : Equiv.Perm (L × Fin m)) :
    Fintype.card (arrangementGraph m (reindexArrangement f e)).ConnectedComponent =
      Fintype.card (arrangementGraph m e).ConnectedComponent :=
  (Fintype.card_congr (arrangementGraphReindex f e).connectedComponentEquiv).symm

end Ostmann

end OAI
