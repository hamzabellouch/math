import OAI.Geometry.EinsteinFour.HighestSquare
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace OAI

/-! The Casimir lower bound with arbitrary symmetric matrix coefficients.
Positive semidefiniteness is applied to each actual tensor coordinate. -/

namespace PositiveEinsteinFour.HighestHessian

open scoped BigOperators
open Bianchi TraceHessian

noncomputable section

/-- The matrix-weighted Gram form of three actual Hessian arrays. -/
def hessianGram (A : Mat) (F : Fin 3 → Hessian) : ℝ :=
  ∑ r, ∑ s, A r s * hessianPairing (F r) (F s)

/-- A positive semidefinite coefficient matrix gives a nonnegative
Gram form on the entire four-slot tensor space. -/
theorem hessianGram_nonneg (A : Mat) (hA : A.PosSemidef) (F : Fin 3 → Hessian) :
    0 ≤ hessianGram A F := by
  have hp (p : TensorIndex) :
      0 ≤ ∑ r, ∑ s, A r s * tensorCoordinates (F r) p * tensorCoordinates (F s) p := by
    have h := hA.dotProduct_mulVec_nonneg (fun r => tensorCoordinates (F r) p)
    simp only [dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum] at h
    convert h using 1
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    ring
  have he : hessianGram A F = ∑ p : TensorIndex,
      ∑ r, ∑ s, A r s * tensorCoordinates (F r) p * tensorCoordinates (F s) p := by
    unfold hessianGram
    simp_rw [← tensorCoordinates_pairing]
    simp only [Finset.mul_sum]
    calc
      _ = ∑ r, ∑ p : TensorIndex, ∑ s,
          A r s * (tensorCoordinates (F r) p * tensorCoordinates (F s) p) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.sum_comm]
      _ = ∑ p : TensorIndex, ∑ r, ∑ s,
          A r s * (tensorCoordinates (F r) p * tensorCoordinates (F s) p) := Finset.sum_comm
      _ = _ := by simp only [mul_assoc]
  rw [he]
  exact Finset.sum_nonneg fun p _ => hp p

/-- Adding a scalar identity adds that scalar times the total energy. -/
theorem hessianGram_shift (A : Mat) (x : ℝ) (F : Fin 3 → Hessian) :
    hessianGram (A + x • (1 : Mat)) F =
      hessianGram A F + x * ∑ r, hessianNormSq (F r) := by
  simp only [hessianGram, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul, add_mul, Finset.sum_add_distrib, mul_ite, mul_zero, mul_one,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    hessianPairing_self, Finset.mul_sum]

/-- The same local Casimir expression accepts complete Weyl matrices. -/
def generalCasimirCurvatureForm (A U : Mat) (X : Hessian) : ℝ :=
  4 * hessianNormSq X + hessianGram A (fun r => totalPlus r X) / 24 +
    hessianGram U (fun r => totalMinus r X) / 4

/-- The sharp lower constant follows from the two proved Casimir energies
and positive semidefinite shifted Weyl matrices; no eigenframe is used. -/
theorem generalCasimirCurvatureForm_lower (A U : Mat) (X : Hessian)
    (hX : condition X) (x y : ℝ)
    (hA : (A + x • (1 : Mat)).PosSemidef)
    (hU : (U + y • (1 : Mat)).PosSemidef) :
    (4 - 2 * x - 2 * y) * hessianNormSq X ≤ generalCasimirCurvatureForm A U X := by
  have hp := hessianGram_nonneg _ hA (fun r => totalPlus r X)
  have hm := hessianGram_nonneg _ hU (fun r => totalMinus r X)
  rw [hessianGram_shift] at hp hm
  have hplus := totalPlus_energy_of_condition X hX
  have hminus := totalMinus_energy_of_condition X hX
  simp only [Fin.sum_univ_three] at hp hm
  rw [hplus] at hp
  rw [hminus] at hm
  unfold generalCasimirCurvatureForm
  nlinarith only [hp, hm]

/-- Positivity includes the closed sectional boundary. -/
theorem generalCasimirCurvatureForm_nonneg (A U : Mat) (X : Hessian)
    (hX : condition X) (x y : ℝ)
    (hA : (A + x • (1 : Mat)).PosSemidef)
    (hU : (U + y • (1 : Mat)).PosSemidef) (hxy : x + y ≤ 2) :
    0 ≤ generalCasimirCurvatureForm A U X := by
  have h := generalCasimirCurvatureForm_lower A U X hX x y hA hU
  have hn : 0 ≤ hessianNormSq X := by
    unfold hessianNormSq
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  exact (mul_nonneg (by linarith) hn).trans h

end
end PositiveEinsteinFour.HighestHessian

end OAI
