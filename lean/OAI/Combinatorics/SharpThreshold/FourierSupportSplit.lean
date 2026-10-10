import Mathlib

namespace OAI

universe u v w

noncomputable section
open scoped BigOperators

namespace Problem313.BiasedFourier

variable {ι : Type u} {κ : Type v} {M : Type w} [Fintype ι] [Fintype κ] [AddCommMonoid M]

/-- Reindex all Fourier supports on a sum coordinate set by their two parts. -/
theorem sum_support_disjSum (a : Finset (ι ⊕ κ) → M) :
    (∑ S : Finset (ι ⊕ κ), a S) =
      ∑ A : Finset ι, ∑ D : Finset κ, a (A.disjSum D) := by
  classical
  rw [← Fintype.sum_prod_type (fun AD : Finset ι × Finset κ => a (AD.1.disjSum AD.2))]
  exact ((Finset.sumEquiv (α := ι) (β := κ)).toEquiv.symm.sum_comp a).symm

/-- Restricting the free-coordinate support commutes with the support split. -/
theorem sum_support_condition_disjSum (a : Finset (ι ⊕ κ) → M)
    (P : Finset ι → Prop) [DecidablePred P] :
    (∑ S : Finset (ι ⊕ κ), if P S.toLeft then a S else 0) =
      ∑ A : Finset ι, if P A then
        ∑ D : Finset κ, a (A.disjSum D) else 0 := by
  classical
  rw [sum_support_disjSum]
  simp only [Finset.toLeft_disjSum, Finset.sum_ite_irrel, Finset.sum_const_zero]

/-- Filter formulation of the same identity, useful for degree cutoffs. -/
theorem sum_support_filter_disjSum (a : Finset (ι ⊕ κ) → M)
    (P : Finset ι → Prop) [DecidablePred P] :
    (∑ S ∈ Finset.univ.filter (fun S : Finset (ι ⊕ κ) => P S.toLeft), a S) =
      ∑ A ∈ Finset.univ.filter P, ∑ D : Finset κ, a (A.disjSum D) := by
  classical
  simp only [Finset.sum_filter]
  exact sum_support_condition_disjSum a P

end Problem313.BiasedFourier

end

end OAI
