import OAI.Algebra.FormulaHitting.RationalTransfer
import OAI.Algebra.FormulaHitting.Minors
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace OAI

noncomputable section
namespace NCHitting

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_rational_coefficient_minor (a : ι → PowerSeries ℚ)
    (ha : LinearIndependent ℚ a) :
    ∃ rows : ι → ℕ,
      Matrix.det (fun r i => PowerSeries.coeff (rows r) (a i) : Matrix ι ι ℚ) ≠ 0 := by
  obtain ⟨d, hd⟩ := exists_independent_jet a ha
  let L := Fintype.linearCombination ℚ (fun i => jet d (a i))
  have hL : LinearMap.ker L = ⊥ :=
    LinearMap.ker_eq_bot.mpr hd.fintypeLinearCombination_injective
  obtain ⟨K, hK⟩ := L.exists_leftInverse_of_injective hL
  let A := LinearMap.toMatrix' L
  let B := LinearMap.toMatrix' K
  have hBA : B * A = 1 := by
    rw [← LinearMap.toMatrix'_comp, hK, LinearMap.toMatrix'_id]
  have hAB : A.transpose * B.transpose = 1 := by
    rw [← Matrix.transpose_mul, hBA, Matrix.transpose_one]
  obtain ⟨rows, hrows⟩ := exists_minor_ne_zero_of_mul_det_ne_zero A.transpose B.transpose
    (by rw [hAB, Matrix.det_one]; exact one_ne_zero)
  refine ⟨fun i => (rows i).val, ?_⟩
  have hm : (A.transpose.submatrix id rows).transpose =
      (fun r i => PowerSeries.coeff (rows r).val (a i) : Matrix ι ι ℚ) := by
    ext r i
    simp [A, L, LinearMap.toMatrix'_apply, Matrix.transpose_apply,
      Matrix.submatrix_apply]
  rw [← hm, Matrix.det_transpose]
  exact hrows

theorem rational_minor_transfer {F : Type*} [Field F] [CharZero F]
    (a : ι → PowerSeries ℚ) (ha : LinearIndependent ℚ a) :
    LinearIndependent F (fun i => PowerSeries.map (algebraMap ℚ F) (a i)) := by
  obtain ⟨rows, hrows⟩ := exists_rational_coefficient_minor a ha
  exact independent_of_rational_minor a rows hrows

end NCHitting

end

end OAI
