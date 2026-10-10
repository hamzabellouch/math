import OAI.Combinatorics.Crossing.DrawingDeletion

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators Classical
variable {m n : ℕ}

theorem delete_crossing_finset (D : AdmissibleDrawing m (n+1)) (v : Fin (n+1)) :
    (deleteRightVertex D v).crossings_finite.toFinset =
      D.crossings_finite.toFinset.filter
        (fun x => x ∈ crossingPoints (deleteRightVertex D v).toContinuousDrawing) := by
  ext x
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
  exact ⟨fun h => ⟨restrict_crossingPoints_subset D.toContinuousDrawing _ h,h⟩, And.right⟩

theorem sum_delete_crossingCount (D : AdmissibleDrawing m (n+1))
    (hnorm : NoAdjacentCrossings D) :
    (∑ v : Fin (n+1), crossingCount (deleteRightVertex D v)) = ((n+1)-2)*crossingCount D := by
  simp only [crossingCount, delete_crossing_finset, Finset.card_filter]
  rw [Finset.sum_comm]
  have he : ∀ x ∈ D.crossings_finite.toFinset,
      (∑ v : Fin (n+1), if x ∈ crossingPoints (deleteRightVertex D v).toContinuousDrawing
        then (1 : ℕ) else 0) = (n+1)-2 := by
    intro x hx
    exact crossing_deletion_multiplicity D hnorm x (by simpa using hx)
  rw [Finset.sum_congr rfl he]
  simp [Nat.mul_comm]

theorem even_deletion_floor (s : ℕ) :
    (2*s)*axisPairs (2*s-1) = (2*s-2)*axisPairs (2*s) := by
  cases s with
  | zero => simp
  | succ s =>
    have h₁ : 2*(s+1)-1 = 2*s+1 := by omega
    have h₂ : 2*(s+1)-2 = 2*s := by omega
    rw [h₁, h₂, axisPairs_odd, axisPairs_even, Nat.add_sub_cancel]
    ring

end Zarankiewicz

end

end OAI
