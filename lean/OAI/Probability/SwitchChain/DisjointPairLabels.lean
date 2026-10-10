import Mathlib

namespace OAI

noncomputable section

namespace Problem315.DisjointPairLabels

variable {V : Type*} [DecidableEq V]

theorem embedding_pairs (e : Fin 4 ↪ V) :
    ({e 0, e 1} : Finset V).card = 2 ∧
    ({e 2, e 3} : Finset V).card = 2 ∧
    Disjoint ({e 0, e 1} : Finset V) {e 2, e 3} := by
  have he : ∀ i j : Fin 4, e i = e j ↔ i = j := fun i j => e.injective.eq_iff
  constructor
  · simp [he]
  constructor
  · simp [he]
  · simp [Finset.disjoint_left, he]

theorem exists_embedding (a b : Finset V) (ha : a.card = 2)
    (hb : b.card = 2) (hab : Disjoint a b) :
    ∃ e : Fin 4 ↪ V, a = {e 0, e 1} ∧ b = {e 2, e 3} := by
  classical
  obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp ha
  obtain ⟨k, l, hkl, rfl⟩ := Finset.card_eq_two.mp hb
  have hd : ∀ x ∈ ({i, j} : Finset V), x ∉ ({k, l} : Finset V) :=
    Finset.disjoint_left.mp hab
  have hik : i ≠ k := fun h => hd i (by simp) (by simp [h])
  have hil : i ≠ l := fun h => hd i (by simp) (by simp [h])
  have hjk : j ≠ k := fun h => hd j (by simp) (by simp [h])
  have hjl : j ≠ l := fun h => hd j (by simp) (by simp [h])
  let e : Fin 4 ↪ V :=
    ⟨![i, j, k, l], by
      intro x y hxy
      fin_cases x <;> fin_cases y <;>
        simp_all [Ne.symm hij, Ne.symm hik, Ne.symm hil,
          Ne.symm hjk, Ne.symm hjl, Ne.symm hkl]⟩
  exact ⟨e, rfl, rfl⟩

theorem forall_pairs_iff_embeddings (P : Finset V → Finset V → Prop) :
    (∀ a b : Finset V, a.card = 2 → b.card = 2 → Disjoint a b → P a b) ↔
      ∀ e : Fin 4 ↪ V, P {e 0, e 1} {e 2, e 3} := by
  constructor
  · intro h e
    obtain ⟨ha, hb, hab⟩ := embedding_pairs e
    exact h _ _ ha hb hab
  · intro h a b ha hb hab
    obtain ⟨e, rfl, rfl⟩ := exists_embedding a b ha hb hab
    exact h e

end Problem315.DisjointPairLabels

end

end OAI
