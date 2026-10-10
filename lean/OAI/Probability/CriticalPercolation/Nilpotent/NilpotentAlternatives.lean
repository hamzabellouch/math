import Mathlib
import OAI.Probability.CriticalPercolation.Nilpotent.NilpotentFinite
import OAI.Probability.CriticalPercolation.Nilpotent.NilpotentRankOne
import OAI.Probability.CriticalPercolation.Nilpotent.AbelianAlternatives
import OAI.Probability.CriticalPercolation.GraphGeometry.FiniteKernelDescent

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation

theorem nilpotent_alternatives (G : Type*) [Group G] [Group.FG G]
    [Group.IsNilpotent G] :
    Finite G ∨
      (∃ φ : G →* Multiplicative ℤ, Surjective φ ∧ (φ.ker : Set G).Finite) ∨
      (∃ φ : G →* Multiplicative (ℤ×ℤ), Surjective φ) := by
  let q : G →* Abelianization G := Abelianization.of
  have hq : Surjective q := QuotientGroup.mk_surjective
  let _ : Group.FG (Abelianization G) := Group.fg_of_surjective hq
  rcases abelian_alternatives (Abelianization G) with h | ⟨φ,hφ,hk⟩ | ⟨φ,hφ⟩
  · let _ := h
    exact Or.inl (nilpotent_finite_of_finite_abelianization G)
  · refine Or.inr (Or.inl ⟨φ.comp q,hφ.comp hq,?_⟩)
    apply hom_finite_composite_kernel q φ ?_ hk
    have hf := nilpotent_commutator_finite_of_cyclic_abelianization G φ hφ hk
    simpa only [q,Abelianization.ker_of] using hf
  · exact Or.inr (Or.inr ⟨φ.comp q,hφ.comp hq⟩)

theorem nilpotent_descent_of_no_planar_quotient (G : Type*)
    [Group G] [Group.FG G] [Group.IsNilpotent G]
    (hplane : ¬ ∃ φ : G →* Multiplicative (ℤ×ℤ), Surjective φ) : AlgebraicDescent G := by
  rcases nilpotent_alternatives G with h | ⟨φ,hφ,hk⟩ | h
  · let _ := h
    exact AlgebraicDescent.finite G
  · exact AlgebraicDescent.cyclic G φ hφ hk
  · exact (hplane h).elim

end CriticalPercolation
end
end
end

end OAI
