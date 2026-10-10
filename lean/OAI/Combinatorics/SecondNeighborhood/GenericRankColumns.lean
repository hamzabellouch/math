import Mathlib.LinearAlgebra.Matrix.Rank

namespace OAI

namespace SeymourSecondNeighborhood

open scoped Matrix

variable {I J K κ : Type*} [Fintype I] [Fintype J] [Field K]
variable [Fintype κ] [DecidableEq κ]

omit [Fintype I] [Fintype J] in
theorem selectedColumns_linearIndependent_of_det_ne_zero
    (M : Matrix I J K) (r : κ → I) (c : κ → J)
    (hdet : (M.submatrix r c).det ≠ 0) :
    LinearIndependent K (M.submatrix id c).col := by
  apply LinearIndependent.of_comp (LinearMap.funLeft K K r)
  change LinearIndependent K (M.submatrix r c).col
  exact Matrix.linearIndependent_cols_of_det_ne_zero hdet

theorem selectedColumns_span_eq_of_det_ne_zero
    (M : Matrix I J K) (r : κ → I) (c : κ → J)
    (hdet : (M.submatrix r c).det ≠ 0) (hrank : M.rank ≤ Fintype.card κ) :
    Submodule.span K (Set.range (M.submatrix id c).col) =
      Submodule.span K (Set.range M.col) := by
  apply Submodule.eq_of_le_of_finrank_le
  · apply Submodule.span_mono
    rintro _ ⟨j, rfl⟩
    exact ⟨c j, rfl⟩
  · calc
      Module.finrank K (Submodule.span K (Set.range M.col)) = M.rank :=
        (Matrix.rank_eq_finrank_span_cols M).symm
      _ ≤ Fintype.card κ := hrank
      _ = Module.finrank K (Submodule.span K (Set.range (M.submatrix id c).col)) :=
        (finrank_span_eq_card
          (selectedColumns_linearIndependent_of_det_ne_zero M r c hdet)).symm

theorem selectedColumns_range_eq_of_det_ne_zero
    (M : Matrix I J K) (r : κ → I) (c : κ → J)
    (hdet : (M.submatrix r c).det ≠ 0) (hrank : M.rank ≤ Fintype.card κ) :
    LinearMap.range (M.submatrix id c).mulVecLin = LinearMap.range M.mulVecLin := by
  rw [Matrix.range_mulVecLin, Matrix.range_mulVecLin]
  exact selectedColumns_span_eq_of_det_ne_zero M r c hdet hrank

theorem exists_selectedColumns_mulVec
    (M : Matrix I J K) (r : κ → I) (c : κ → J)
    (hdet : (M.submatrix r c).det ≠ 0) (hrank : M.rank ≤ Fintype.card κ)
    (x : J → K) :
    ∃ y : κ → K, M *ᵥ x = (M.submatrix id c) *ᵥ y := by
  have hx : M *ᵥ x ∈ LinearMap.range M.mulVecLin := ⟨x, rfl⟩
  rw [← selectedColumns_range_eq_of_det_ne_zero M r c hdet hrank] at hx
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, hy.symm⟩

end SeymourSecondNeighborhood

end OAI
