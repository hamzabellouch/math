import Mathlib
import OAI.Probability.CriticalPercolation.Nilpotent.NilpotentSubgroupFG
import OAI.Probability.CriticalPercolation.Nilpotent.NilpotentAlternatives
import OAI.Probability.CriticalPercolation.Nilpotent.NilpotentCyclicConstruction
import OAI.Probability.CriticalPercolation.Nilpotent.FiniteCyclicInheritance

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation

private theorem nilpotent_descent_by_construction (n : ℕ) :
    ∀ (G : Type*) [Group G] [Group.FG G] [Group.IsNilpotent G],
      FiniteCyclicConstruction G n → AlgebraicDescent G := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G _ _ _ hG
    rcases nilpotent_alternatives G with h | ⟨φ,hφ,hk⟩ | ⟨φ,hφ⟩
    · let _ := h
      exact .finite G
    · exact .cyclic G φ hφ hk
    · apply AlgebraicDescent.plane G φ hφ
      intro J hJ
      obtain ⟨m,hm,hC,hi⟩ := hG.subgroup J
      have hlt : m<n := by
        by_contra! hge
        have he : m=n := by omega
        let _ := hi he
        have hker : φ.ker.FiniteIndex := Subgroup.finiteIndex_of_le hJ
        apply hker.index_ne_zero
        rw [Subgroup.index_ker,φ.range_eq_top_of_surjective hφ]
        rw [Nat.card_congr (Subgroup.topEquiv :
          (⊤ : Subgroup (Multiplicative (ℤ×ℤ))) ≃* Multiplicative (ℤ×ℤ)).toEquiv]
        exact Nat.card_eq_zero_of_infinite
      let _ : Group.FG J := nilpotent_subgroup_fg G J
      exact ih m hlt J hC

theorem nilpotent_descent (G : Type*) [Group G] [Group.FG G] [Group.IsNilpotent G] :
    AlgebraicDescent G := by
  obtain ⟨n,hn⟩ := nilpotent_finite_cyclic_construction G
  exact nilpotent_descent_by_construction n G hn

end CriticalPercolation
end
end
end

end OAI
