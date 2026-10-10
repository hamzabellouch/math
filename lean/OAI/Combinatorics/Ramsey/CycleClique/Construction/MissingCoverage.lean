import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Lemmas
import Mathlib.Tactic

namespace OAI

/-! The two targets cover a finite set when its cardinality is at most
the number of those distinct targets that lie in it. -/

namespace CycleClique.Construction
open scoped Classical

variable {V : Type*}

theorem subset_pair_of_card_le_indicators (M : Finset V) {x y : V} (hne : x ≠ y)
    (hcard : M.card ≤ (if x ∈ M then 1 else 0) + (if y ∈ M then 1 else 0)) :
    M ⊆ {x, y} := by
  classical
  by_cases hx : x ∈ M
  · by_cases hy : y ∈ M
    · have hsub : ({x, y} : Finset V) ⊆ M := by
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact hx
        · obtain rfl := Finset.mem_singleton.mp hz
          exact hy
      have heq : ({x, y} : Finset V) = M := Finset.eq_of_subset_of_card_le hsub (by
        have hh : M.card ≤ 2 := by simpa [hx, hy] using hcard
        simpa [hne] using hh)
      rw [← heq]
    · have hsub : ({x} : Finset V) ⊆ M := by simp [hx]
      have heq : ({x} : Finset V) = M := Finset.eq_of_subset_of_card_le hsub (by
        simpa [hx, hy] using hcard)
      rw [← heq]
      simp
  · by_cases hy : y ∈ M
    · have hsub : ({y} : Finset V) ⊆ M := by simp [hy]
      have heq : ({y} : Finset V) = M := Finset.eq_of_subset_of_card_le hsub (by
        simpa [hx, hy] using hcard)
      rw [← heq]
      simp
    · have he : M = ∅ := Finset.card_eq_zero.mp (by simpa [hx, hy] using hcard)
      simp [he]

end CycleClique.Construction

end OAI
