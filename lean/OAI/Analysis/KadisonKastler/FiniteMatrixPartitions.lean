import OAI.Analysis.KadisonKastler.TracialMatrixVariance
import OAI.Analysis.KadisonKastler.MatrixCommutant

namespace OAI

/-! # Coordinate block projections for the growing matrix product -/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

local instance : PartialOrder ℂ := CStarAlgebra.spectralOrder _
local instance : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing _

variable {m : ℕ}

def scalarDiagonalProjection (s : Finset (Fin m)) : CStarMatrix (Fin m) (Fin m) ℂ :=
  CStarMatrix.ofMatrix (Matrix.diagonal (fun i => if i ∈ s then 1 else 0))

theorem scalarDiagonalProjection_isProjection (s : Finset (Fin m)) :
    IsStarProjection (scalarDiagonalProjection s) := by
  constructor
  · change CStarMatrix.ofMatrix
      ((Matrix.diagonal (fun i : Fin m => if i ∈ s then (1 : ℂ) else 0)) *
        Matrix.diagonal (fun i : Fin m => if i ∈ s then (1 : ℂ) else 0)) = _
    rw [Matrix.diagonal_mul_diagonal]
    congr 2
    funext i
    split <;> simp
  · apply CStarMatrix.ext
    intro i j
    by_cases h : i = j
    · subst j
      simp [scalarDiagonalProjection, CStarMatrix.star_apply, Matrix.diagonal]
    · simp [scalarDiagonalProjection, CStarMatrix.star_apply, Matrix.diagonal, h, Ne.symm h]

theorem scalarDiagonalProjection_mul_of_disjoint (s t : Finset (Fin m))
    (hst : Disjoint s t) : scalarDiagonalProjection s * scalarDiagonalProjection t = 0 := by
  change CStarMatrix.ofMatrix
    ((Matrix.diagonal (fun i : Fin m => if i ∈ s then (1 : ℂ) else 0)) *
      Matrix.diagonal (fun i : Fin m => if i ∈ t then (1 : ℂ) else 0)) = _
  rw [Matrix.diagonal_mul_diagonal]
  apply CStarMatrix.ext
  intro i j
  have hi : ¬ (i ∈ s ∧ i ∈ t) := fun h => Finset.disjoint_left.mp hst h.1 h.2
  simp [Matrix.diagonal]
  intro _ hit his
  exact hi ⟨his, hit⟩

theorem scalarDiagonalProjection_trace [NeZero m] (s : Finset (Fin m)) :
    (matrixTrace scalarTrace).toLinearMap (scalarDiagonalProjection s) =
      (m : ℂ)⁻¹ * s.card := by
  simp [matrixTrace_apply, scalarDiagonalProjection, scalarTrace, Matrix.diagonal]

def finiteBlockProjection (n j : ℕ) (s : Finset (Fin (j + 1))) : FiniteMatrixModel n j :=
  matrixScalarHom (scalarDiagonalProjection s)

theorem finiteBlockProjection_isProjection (n j : ℕ) (s : Finset (Fin (j + 1))) :
    IsStarProjection (finiteBlockProjection n j s) :=
  (scalarDiagonalProjection_isProjection s).map matrixScalarHom

theorem finiteBlockProjection_norm_le (n j : ℕ) [NeZero n]
    (s : Finset (Fin (j + 1))) : ‖finiteBlockProjection n j s‖ ≤ 1 :=
  IsStarProjection.norm_le _ (finiteBlockProjection_isProjection n j s)

theorem finiteBlockProjection_mul_of_disjoint (n j : ℕ)
    (s t : Finset (Fin (j + 1))) (hst : Disjoint s t) :
    finiteBlockProjection n j s * finiteBlockProjection n j t = 0 := by
  rw [finiteBlockProjection, finiteBlockProjection, ← map_mul,
    scalarDiagonalProjection_mul_of_disjoint s t hst, map_zero]

theorem finiteBlockProjection_trace (n j : ℕ) [NeZero n]
    (s : Finset (Fin (j + 1))) :
    (finiteMatrixModelTrace n j).toLinearMap (finiteBlockProjection n j s) =
      (j + 1 : ℂ)⁻¹ * s.card := by
  simp only [finiteBlockProjection, finiteMatrixModelTrace, matrixTrace_apply,
    matrixScalarHom_apply, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Complex.ofReal_inv, Complex.ofReal_natCast]
  rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne n)), one_mul]
  simpa only [matrixTrace_apply, Fintype.card_fin, Complex.ofReal_inv,
    Complex.ofReal_natCast, Nat.cast_add, Nat.cast_one, Complex.ofReal_add,
    Complex.ofReal_one] using scalarDiagonalProjection_trace s

end

end KadisonKastler

end OAI
