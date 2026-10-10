import Mathlib
import OAI.Combinatorics.Chromatic.QuantumTorus.OrderedIndependentProduct
import OAI.Combinatorics.Chromatic.Walls.SquarefreeBlocks

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open scoped BigOperators
open Classical
noncomputable section
variable {M V:Type*} [AddCommGroup M] [Fintype V] [DecidableEq V]
variable (Ω:M →+ M →+ ℤ) (u:V → M)
variable {n r:ℕ} (b:Fin n ↪ V) (κ:Fin n → Fin r)

omit [Fintype V] [DecidableEq V] in
lemma wordEnergy_blocks :
    wordEnergy Ω (blockLabels u (SquarefreeBlocks.blocks b κ))=
      ∑i:Fin n,∑j:Fin n,if κ i<κ j then Ω (u (b i)) (u (b j)) else 0 := by
  have hb:∀c d:Fin r,Ω (blockLabels u (SquarefreeBlocks.blocks b κ) c)
      (blockLabels u (SquarefreeBlocks.blocks b κ) d)=
      ∑i∈Finset.univ.filter (fun i=>κ i=c),∑j∈Finset.univ.filter (fun j=>κ j=d),Ω (u (b i)) (u (b j)) := by
    intro c d
    simp only [blockLabels,SquarefreeBlocks.blocks,Finset.sum_map,map_sum,AddMonoidHom.finsetSum_apply]
    rw [Finset.sum_comm]
  rw [wordEnergy_eq_pairs]
  simp only [hb]
  calc
    (∑c:Fin r,∑d:Fin r,if c<d then
      ∑i∈Finset.univ.filter (fun i=>κ i=c),∑j∈Finset.univ.filter (fun j=>κ j=d),Ω (u (b i)) (u (b j)) else 0)=
      ∑c:Fin r,∑d:Fin r,∑i:Fin n,∑j:Fin n,
        if κ i=c ∧ κ j=d ∧ c<d then Ω (u (b i)) (u (b j)) else 0 := by
          apply Finset.sum_congr rfl
          intro c hc
          apply Finset.sum_congr rfl
          intro d hd
          by_cases h:c<d
          · simp only [h,ite_true,Finset.sum_filter,ite_and]
            apply Finset.sum_congr rfl
            intro i hi
            by_cases hh:κ i=c <;> simp [hh]
          · simp [h]
    _ = ∑i:Fin n,∑j:Fin n,∑c:Fin r,∑d:Fin r,
        if κ i=c ∧ κ j=d ∧ c<d then Ω (u (b i)) (u (b j)) else 0 := by
          calc
            _ = ∑c:Fin r,∑i:Fin n,∑d:Fin r,∑j:Fin n,
                if κ i=c ∧ κ j=d ∧ c<d then Ω (u (b i)) (u (b j)) else 0 := by
                  apply Finset.sum_congr rfl
                  intro c hc
                  rw [Finset.sum_comm]
            _ = ∑i:Fin n,∑c:Fin r,∑d:Fin r,∑j:Fin n,
                if κ i=c ∧ κ j=d ∧ c<d then Ω (u (b i)) (u (b j)) else 0 :=
                  Finset.sum_comm
            _ = _ := by
              apply Finset.sum_congr rfl
              intro i hi
              calc
                _ = ∑c:Fin r,∑j:Fin n,∑d:Fin r,
                    if κ i=c ∧ κ j=d ∧ c<d then Ω (u (b i)) (u (b j)) else 0 := by
                      apply Finset.sum_congr rfl
                      intro c hc
                      rw [Finset.sum_comm]
                _ = _ := Finset.sum_comm
    _ = _ := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          simp [ite_and,Finset.sum_ite_irrel]
end
end ElementaryPositivity.QuantumTorus

end

end OAI
