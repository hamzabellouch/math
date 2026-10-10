import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Logic.Equiv.Fintype

namespace OAI

noncomputable section
open scoped BigOperators Matrix
open Matrix Module
namespace MatrixSelection
variable {K m : Type*} [Field K] [Fintype m]

lemma exists_row_minor {k : ℕ} (M : Matrix m (Fin k) K) (h : M.rank = k) :
    ∃ j : Fin k → m, Function.Injective j ∧ IsUnit (M.submatrix j id) := by
  classical
  have ht : Submodule.span K (Set.range M.row) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    simpa only [← M.rank_eq_finrank_span_row, Module.finrank_pi, Module.finrank_self,
      Fintype.card_fin, mul_one] using h
  let s := (linearIndepOn_empty K id).extend (Set.empty_subset (Set.range M.row))
  let b : Basis s K (Fin k → K) := Basis.ofSpan (le_of_eq ht.symm)
  let := Fintype.ofFinite s
  have hb : Fintype.card s = k := by
    simpa using (Module.finrank_eq_card_basis b).symm
  have he : Nonempty (Fin k ≃ s) := Fintype.card_eq.mp (by simpa using hb.symm)
  let e : Fin k ≃ s := Classical.choice he
  have hc (i : Fin k) : ∃ j, M.row j = b (e i) := by
    exact Basis.ofSpan_subset (le_of_eq ht.symm) (Set.mem_range_self (e i))
  choose j hj using hc
  have hli : LinearIndependent K (fun i => M.row (j i)) := by
    simpa only [hj, Function.comp_def] using b.linearIndependent.comp e e.injective
  refine ⟨j, ?_, ?_⟩
  · intro i i' hh
    exact hli.injective (congrArg M.row hh)
  · exact Matrix.linearIndependent_rows_iff_isUnit.mp hli

lemma rank_lt_of_all_row_minors_zero {k : ℕ} (M : Matrix m (Fin k) K)
    (h : ∀ j : Fin k → m, Function.Injective j → (M.submatrix j id).det = 0) :
    M.rank < k := by
  by_contra hh
  have he : M.rank = k := le_antisymm (by simpa using M.rank_le_card_width) (by omega)
  obtain ⟨j,hj,hu⟩ := exists_row_minor M he
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero (h j hj)

lemma all_row_minors_units {k : ℕ} (M : Matrix m (Fin k) K) (h : M.rank = k)
    (ha : ∀ π : Equiv.Perm m, ∃ σ : K ≃+* K, ∀ i j, σ (M i j) = M (π i) j) :
    ∀ j : Fin k → m, Function.Injective j → IsUnit (M.submatrix j id) := by
  classical
  obtain ⟨j₀,hj₀,hu⟩ := exists_row_minor M h
  intro j hj
  obtain ⟨π,hπ⟩ := Equiv.Perm.exists_extending_pair j₀ j hj₀ hj
  obtain ⟨σ,hσ⟩ := ha π
  have hM : (M.submatrix j₀ id).map σ.toRingHom = M.submatrix j id := by
    ext i a
    exact (hσ (j₀ i) a).trans (congrArg (fun x => M x a) (hπ i))
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [← hM]
  have hd := σ.map_det (M.submatrix j₀ id)
  change σ (M.submatrix j₀ id).det = ((M.submatrix j₀ id).map σ.toRingHom).det at hd
  rw [← hd]
  exact IsUnit.map σ.toRingHom ((Matrix.isUnit_iff_isUnit_det _).mp hu)

lemma first_columns_rank {n k : ℕ} (S : Matrix (Fin n) (Fin n) K) (hS : IsUnit S)
    (e : Fin k → Fin n) (he : Function.Injective e) : (S.submatrix id e).rank = k := by
  have hi := Matrix.linearIndependent_cols_iff_isUnit.mpr hS
  have hh : LinearIndependent K (S.submatrix id e).transpose.row := hi.comp e he
  simpa only [Matrix.rank_transpose, Fintype.card_fin] using hh.rank_matrix

end MatrixSelection

end

end OAI
