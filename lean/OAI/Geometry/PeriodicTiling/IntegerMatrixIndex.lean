import OAI.Geometry.PeriodicTiling.EuclideanBasic
import OAI.Geometry.PeriodicTiling.MarkedTile
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Determinant

namespace OAI

noncomputable section

namespace PeriodicTilingThree

open Matrix
open scoped BigOperators

theorem integer_mulVec_mem_of_columns
    (L : AddSubgroup (Lattice 3)) (M : Matrix (Fin 3) (Fin 3) ℤ)
    (hM : ∀ j, M.col j ∈ L) (z : Lattice 3) : M *ᵥ z ∈ L := by
  have hs : (∑ j : Fin 3, z j • M.col j) ∈ L := by
    apply L.sum_mem
    intro j _hj
    exact L.zsmul_mem (hM j) (z j)
  have he : M *ᵥ z = ∑ j : Fin 3, z j • M.col j := by
    ext i
    simp [Matrix.mulVec, dotProduct, Matrix.col, mul_comm]
  rwa [he]

theorem determinant_smul_mem_of_columns
    (L : AddSubgroup (Lattice 3)) (M : Matrix (Fin 3) (Fin 3) ℤ)
    (hM : ∀ j, M.col j ∈ L) (z : Lattice 3) : M.det • z ∈ L := by
  have h := integer_mulVec_mem_of_columns L M hM (M.adjugate *ᵥ z)
  simpa only [Matrix.mulVec_mulVec, Matrix.mul_adjugate,
    Matrix.smul_mulVec, Matrix.one_mulVec] using h

theorem finiteIndex_of_integer_columns
    (L : AddSubgroup (Lattice 3)) (M : Matrix (Fin 3) (Fin 3) ℤ)
    (hdet : M.det ≠ 0) (hM : ∀ j, M.col j ∈ L) : L.FiniteIndex := by
  let d : ℕ := M.det.natAbs
  have hd : d ≠ 0 := (Int.natAbs_pos.mpr hdet).ne'
  let : NeZero d := ⟨hd⟩
  have hker : (MarkedTile.residue d).ker ≤ L := by
    intro x hx
    obtain ⟨z, hz⟩ := MarkedTile.exists_scale_of_residue_eq_zero d hx
    have habs : (d : ℤ) • z ∈ L := by
      have h := determinant_smul_mem_of_columns L M hM z
      change (M.det.natAbs : ℤ) • z ∈ L
      rw [Int.natCast_natAbs]
      by_cases hsign : 0 ≤ M.det
      · simpa only [abs_of_nonneg hsign] using h
      · simpa only [abs_of_nonpos (le_of_not_ge hsign), neg_smul] using L.neg_mem h
    have he : MarkedTile.scale d z = (d : ℤ) • z := by
      ext i
      simp only [MarkedTile.scale_apply, Pi.smul_apply, smul_eq_mul]
    rw [← hz, he]
    exact habs
  let : (MarkedTile.residue d).ker.FiniteIndex := inferInstance
  exact AddSubgroup.finiteIndex_of_le hker

theorem det_ne_zero_of_scaled_columns_basis (m : ℕ)
    (b : Module.Basis (Fin 3) ℝ (Space 3)) (z : Fin 3 → Lattice 3)
    (hz : ∀ j, scaledCast m (z j) = b j) :
    Matrix.det (fun i j : Fin 3 => z j i) ≠ 0 := by
  let M : Matrix (Fin 3) (Fin 3) ℤ := fun i j => z j i
  let e := Pi.basisFun ℝ (Fin 3)
  have hreal : (e.toMatrix b).det ≠ 0 := (e.isUnit_det b).ne_zero
  have hmatrix : e.toMatrix b = (m : ℝ) • (M.map fun a => (a : ℝ)) := by
    ext i j
    change (e.repr (b j)) i = (m : ℝ) * (z j i : ℝ)
    rw [Pi.basisFun_repr]
    exact (congrFun (hz j) i).symm
  change M.det ≠ 0
  intro hzero
  have hcast : (M.map fun a => (a : ℝ)).det = 0 := by
    rw [← Int.cast_det, hzero, Int.cast_zero]
  apply hreal
  rw [hmatrix, Matrix.det_smul, hcast, mul_zero]

theorem lattice_pullback_finiteIndex (m : ℕ)
    (b : Module.Basis (Fin 3) ℝ (Space 3))
    (hb : latticeOfBasis b ≤ scaledGrid m) :
    ((latticeOfBasis b).comap (scaledCast m)).FiniteIndex := by
  have hbmem : ∀ j : Fin 3, b j ∈ latticeOfBasis b := by
    intro j
    exact Submodule.subset_span ⟨j, rfl⟩
  have hex : ∀ j : Fin 3, ∃ z : Lattice 3, scaledCast m z = b j := by
    intro j
    exact hb (hbmem j)
  choose z hz using hex
  let M : Matrix (Fin 3) (Fin 3) ℤ := fun i j => z j i
  apply finiteIndex_of_integer_columns _ M
    (det_ne_zero_of_scaled_columns_basis m b z hz)
  intro j
  change scaledCast m (z j) ∈ latticeOfBasis b
  rw [hz j]
  exact hbmem j

end PeriodicTilingThree

end

end OAI
