import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.Rank

namespace OAI

namespace SiegelZeros


namespace SiegelZerosAwei.W30

open Matrix Module

variable {K L : Type*} [Field K] [Field L]
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem det_ne_zero_of_independent_rows (rows : n → n → K)
    (hrows : LinearIndependent K rows) : Matrix.det rows ≠ 0 := by
  exact isUnit_iff_ne_zero.mp
    ((Matrix.isUnit_iff_isUnit_det rows).mp
      (Matrix.linearIndependent_rows_iff_isUnit.mp hrows))

theorem det_map_ne_zero_iff (f : K →+* L) (A : Matrix n n K) :
    (A.map f).det ≠ 0 ↔ A.det ≠ 0 := by
  change (f.mapMatrix A).det ≠ 0 ↔ A.det ≠ 0
  rw [← f.map_det]
  exact map_ne_zero f

theorem independent_rows_map_iff (f : K →+* L) (A : Matrix n n K) :
    LinearIndependent L (A.map f).row ↔ LinearIndependent K A.row := by
  constructor
  · intro h
    exact Matrix.linearIndependent_rows_of_det_ne_zero
      ((det_map_ne_zero_iff f A).mp (det_ne_zero_of_independent_rows _ h))
  · intro h
    exact Matrix.linearIndependent_rows_of_det_ne_zero
      ((det_map_ne_zero_iff f A).mpr (det_ne_zero_of_independent_rows _ h))

theorem rank_map_eq_of_independent_rows (f : K →+* L) (A : Matrix n n K)
    (hA : LinearIndependent K A.row) :
    (A.map f).rank = A.rank := by
  rw [hA.rank_matrix, ((independent_rows_map_iff f A).mpr hA).rank_matrix]

theorem basis_det_ne_zero (b : Basis n K (n → K)) :
    Matrix.det (fun i j => b i j) ≠ 0 :=
  det_ne_zero_of_independent_rows _ b.linearIndependent

theorem exists_selected_rows_det_ne_zero {ι : Type*} (rows : ι → n → K)
    (hspan : Submodule.span K (Set.range rows) = ⊤) :
    ∃ select : n → ι, Function.Injective select ∧
      Matrix.det (fun i j => rows (select i) j) ≠ 0 := by
  classical
  let b := Basis.ofSpan (show ⊤ ≤ Submodule.span K (Set.range rows) from hspan.ge)
  let basisIndexFintype := FiniteDimensional.fintypeBasisIndex b
  have hc := (Module.finrank_eq_card_basis b).symm.trans
    (Module.finrank_pi K (ι := n))
  let e := Fintype.equivOfCardEq hc
  let b' : Basis n K (n → K) := b.reindex e
  have hb : ∀ i : n, ∃ a : ι, rows a = b' i := by
    intro i
    have hmem : b' i ∈ Set.range b :=
      ⟨e.symm i, (b.reindex_apply e i).symm⟩
    exact Basis.ofSpan_subset (K := K) (s := Set.range rows) hspan.ge hmem
  choose select hselect using hb
  have hrows : (fun i => rows (select i)) = b' := funext hselect
  refine ⟨select, ?_, ?_⟩
  · intro i j hij
    apply b'.injective
    rw [← hselect i, ← hselect j, hij]
  · simpa only [hrows] using basis_det_ne_zero b'

end SiegelZerosAwei.W30


end SiegelZeros

end OAI
