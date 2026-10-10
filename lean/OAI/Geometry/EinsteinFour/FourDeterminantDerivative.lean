import Mathlib.Analysis.Calculus.FDeriv.ContinuousAlternatingMap
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Ring

namespace OAI

/-! Determinant differentiation in the four-dimensional coordinates used
for the metric volume density. The proof uses the alternating determinant
and its row-replacement formula, without a matrix inverse. -/

namespace PositiveEinsteinFour.Geometry

open Matrix
open scoped BigOperators

noncomputable section

private def determinantForm :
    (Fin 4 → ℝ) [⋀^Fin 4]→L[ℝ] ℝ :=
  { (Matrix.detRowAlternating : (Fin 4 → ℝ) [⋀^Fin 4]→ₗ[ℝ] ℝ) with
    cont := continuous_id.matrix_det }

def determinantDifferential (G : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ →L[ℝ] ℝ :=
  determinantForm.toContinuousMultilinearMap.linearDeriv G

theorem determinantDifferential_apply (G H : Matrix (Fin 4) (Fin 4) ℝ) :
    determinantDifferential G H = ∑ i, (G.updateRow i (H i)).det := by
  calc
    _ = ∑ i, determinantForm (Function.update G i (H i)) :=
      ContinuousMultilinearMap.linearDeriv_apply
        determinantForm.toContinuousMultilinearMap G H
    _ = _ := by
      simp only [Matrix.updateRow]
      rfl

theorem hasDerivAt_det_of_components
    (G : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (H : Matrix (Fin 4) (Fin 4) ℝ) (t : ℝ)
    (h : ∀ i j, HasDerivAt (fun s => G s i j) (H i j) t) :
    HasDerivAt (fun s => (G s).det) (determinantDifferential (G t) H) t := by
  have hG : HasDerivAt G H t :=
    hasDerivAt_pi.mpr (fun i => hasDerivAt_pi.mpr (h i))
  exact (determinantForm.hasFDerivAt (G t)).comp_hasDerivAt t hG

theorem determinantDifferential_left (G C : Matrix (Fin 4) (Fin 4) ℝ) :
    determinantDifferential G (C * G) = C.trace * G.det := by
  rw [determinantDifferential_apply]
  have hrow (i : Fin 4) : (C * G) i = ∑ r, C i r • G r := by
    ext j
    simp only [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [hrow, Matrix.det_updateRow_sum, smul_eq_mul]
  exact (Finset.sum_mul _ _ _).symm

theorem determinantDifferential_transpose (G H : Matrix (Fin 4) (Fin 4) ℝ) :
    determinantDifferential Gᵀ Hᵀ = determinantDifferential G H := by
  have h (i j : Fin 4) :
      HasDerivAt (fun s : ℝ => (G + s • H) i j) (H i j) 0 := by
    change HasDerivAt (fun s : ℝ => G i j + s * H i j) (H i j) 0
    exact (hasDerivAt_mul_const (H i j)).const_add (G i j)
  have h₁ := hasDerivAt_det_of_components (fun s => G + s • H) H 0 h
  have h₂ := hasDerivAt_det_of_components (fun s => (G + s • H)ᵀ) Hᵀ 0
    (fun i j => h j i)
  simp only [zero_smul, add_zero, Matrix.det_transpose] at h₁ h₂
  exact h₂.unique h₁

theorem determinantDifferential_right (G C : Matrix (Fin 4) (Fin 4) ℝ) :
    determinantDifferential G (G * C) = C.trace * G.det := by
  rw [← determinantDifferential_transpose, Matrix.transpose_mul,
    determinantDifferential_left, Matrix.trace_transpose, Matrix.det_transpose]

/-- The determinant of a metric Gram matrix has twice the connection trace
as its logarithmic derivative. -/
theorem determinantDifferential_congruence (G C : Matrix (Fin 4) (Fin 4) ℝ) :
    determinantDifferential G (Cᵀ * G + G * C) = 2 * C.trace * G.det := by
  rw [map_add, determinantDifferential_left, determinantDifferential_right,
    Matrix.trace_transpose]
  ring

end
end PositiveEinsteinFour.Geometry

end OAI
