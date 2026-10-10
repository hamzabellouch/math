import OAI.NumberTheory.Ostmann.Construction.CopiedPriorFubini

namespace OAI

/-! # Finite reordering of the two branch priors and three frequency indices -/

namespace Ostmann

open scoped BigOperators Classical

theorem copiedFrequency_sum {D : Type*} [Fintype D] (S : Finset ℤ)
    (F : ℤ → D → D → ℂ) :
    (∑ a : S × (D × D), F a.1 a.2.1 a.2.2) = ∑ s ∈ S, ∑ d, ∑ e, F s d e := by
  simp only [Fintype.sum_prod_type]
  exact Finset.sum_coe_sort S (fun s => ∑ d, ∑ e, F s d e)

theorem copied_prior_sum_reorder {H D : Type*} [Fintype H] [Fintype D]
    (S : Finset ℤ) (w : H → ℂ) (F : ℤ → H → D → H → D → ℂ) :
    (∑ l, w l * ∑ r, w r * ∑ s ∈ S, ∑ d, ∑ e, F s l d r e) =
      ∑ s ∈ S, ∑ l, ∑ d, ∑ r, ∑ e, w l * (w r * F s l d r e) := by
  symm
  calc
    _ = ∑ l, ∑ s ∈ S, ∑ d, ∑ r, ∑ e, w l * (w r * F s l d r e) := Finset.sum_comm
    _ = ∑ l, ∑ r, ∑ s ∈ S, ∑ d, ∑ e, w l * (w r * F s l d r e) := by
      apply Finset.sum_congr rfl
      intro l _
      calc
        _ = ∑ s ∈ S, ∑ r, ∑ d, ∑ e, w l * (w r * F s l d r e) := by
          apply Finset.sum_congr rfl
          intro s _
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = _ := by simp only [Finset.mul_sum]

end Ostmann

end OAI
