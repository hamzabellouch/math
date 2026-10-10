import Mathlib.Data.Finset.Max
import Mathlib.Basic.Real.Basic

namespace OAI

/-! A common positive radius for finitely many local estimates. -/
noncomputable section
namespace CircleDomainRigidity

 theorem finite_positive_lower_bound {ι : Type*} [Fintype ι]
    (δ : ι → ℝ) (hδ : ∀ j, 0 < δ j) : ∃ ε > 0, ∀ j, ε ≤ δ j := by
  classical
  let S : Finset ℝ := insert 1 (Finset.univ.image δ)
  have hS : S.Nonempty := ⟨1,Finset.mem_insert_self _ _⟩
  refine ⟨S.min' hS,?_,?_⟩
  · have hm := Finset.min'_mem S hS
    rcases Finset.mem_insert.mp hm with he | he
    · rw [he]; exact zero_lt_one
    · obtain ⟨j,_,he⟩ := Finset.mem_image.mp he
      rw [← he]
      exact hδ j
  · intro j
    exact Finset.min'_le S _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩))

end CircleDomainRigidity

end

end OAI
