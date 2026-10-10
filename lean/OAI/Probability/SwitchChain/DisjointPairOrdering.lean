import OAI.Probability.SwitchChain.DisjointProjectionCell

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.DisjointEncoding

theorem exists_pair_ordering {V : Type*} [DecidableEq V]
    (a b : Finset V) (ha : a.card = 2) (hb : b.card = 2) (hab : Disjoint a b) :
    ∃ e : Fin 4 ↪ V, ({e 0, e 1} : Finset V) = a ∧ {e 2, e 3} = b := by
  obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp ha
  obtain ⟨k,l,hkl,rfl⟩ := Finset.card_eq_two.mp hb
  have hik : i ≠ k := fun h => Finset.disjoint_left.mp hab (by simp : i ∈ ({i,j} : Finset V)) (by simp [h])
  have hil : i ≠ l := fun h => Finset.disjoint_left.mp hab (by simp : i ∈ ({i,j} : Finset V)) (by simp [h])
  have hjk : j ≠ k := fun h => Finset.disjoint_left.mp hab (by simp : j ∈ ({i,j} : Finset V)) (by simp [h])
  have hjl : j ≠ l := fun h => Finset.disjoint_left.mp hab (by simp : j ∈ ({i,j} : Finset V)) (by simp [h])
  let f : Fin 4 → V := ![i,j,k,l]
  have hf : Function.Injective f := by
    intro u v huv
    fin_cases u <;> fin_cases v <;>
      simp_all [f, Ne.symm]
  exact ⟨⟨f,hf⟩, rfl, rfl⟩

end Problem315.DisjointEncoding

end

end OAI
