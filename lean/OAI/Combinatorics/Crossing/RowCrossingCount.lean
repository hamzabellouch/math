import OAI.Combinatorics.Crossing.CrossingIncidence

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators Classical
variable {m n : ℕ}

def NoAdjacentCrossings (D : AdmissibleDrawing m n) : Prop :=
  ∀ e f : BipartiteEdge m n, e ≠ f → (e.1 = f.1 ∨ e.2 = f.2) →
    edgeInterior D.toContinuousDrawing e ∩ edgeInterior D.toContinuousDrawing f = ∅

theorem pairCrossings_eq_empty_of_adjacent (D : AdmissibleDrawing m n)
    (hnorm : NoAdjacentCrossings D) (e f : BipartiteEdge m n)
    (hadj : e.1 = f.1 ∨ e.2 = f.2) : pairCrossings D e f = ∅ := by
  by_cases hef : e = f
  · subst f
    exact pairCrossings_self D e
  · apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hmem := (Finset.mem_filter.mp hx).2
    have hi : x ∈ edgeInterior D.toContinuousDrawing e ∩ edgeInterior D.toContinuousDrawing f :=
      ⟨hmem.2.1,hmem.2.2⟩
    rw [hnorm e f hef hadj] at hi
    exact hi

def rowCrossingCount (D : AdmissibleDrawing m n) (i k : Fin m) : ℕ :=
  ∑ p : Fin n, ∑ q : Fin n, (pairCrossings D (i,p) (k,q)).card

theorem rowCrossingCount_self (D : AdmissibleDrawing m n) (hnorm : NoAdjacentCrossings D)
    (i : Fin m) : rowCrossingCount D i i = 0 := by
  unfold rowCrossingCount
  apply Finset.sum_eq_zero
  intro p hp
  apply Finset.sum_eq_zero
  intro q hq
  rw [pairCrossings_eq_empty_of_adjacent D hnorm (i,p) (i,q) (Or.inl rfl), Finset.card_empty]

theorem sum_rowCrossingCount (D : AdmissibleDrawing m n) :
    (∑ i : Fin m, ∑ k : Fin m, rowCrossingCount D i k) = 2*crossingCount D := by
  have h := sum_pairCrossings_card D
  change (∑ e : Fin m × Fin n, ∑ f : Fin m × Fin n, (pairCrossings D e f).card) = _ at h
  simp only [Fintype.sum_prod_type] at h
  calc
    _ = ∑ i : Fin m, ∑ p : Fin n, ∑ k : Fin m, ∑ q : Fin n,
        (pairCrossings D (i,p) (k,q)).card := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = _ := h

theorem sum_offDiagonal_rowCrossingCount (D : AdmissibleDrawing m n)
    (hnorm : NoAdjacentCrossings D) :
    (∑ i : Fin m, ∑ k ∈ Finset.univ.erase i, rowCrossingCount D i k) = 2*crossingCount D := by
  rw [← sum_rowCrossingCount D]
  apply Finset.sum_congr rfl
  intro i hi
  have he := Finset.sum_erase_add Finset.univ (rowCrossingCount D i) (Finset.mem_univ i)
  simpa only [rowCrossingCount_self D hnorm, add_zero] using he

end Zarankiewicz

end

end OAI
