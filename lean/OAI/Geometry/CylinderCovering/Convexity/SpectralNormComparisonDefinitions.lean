import Mathlib

namespace OAI

noncomputable section
namespace SpectralNormComparison

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def offDiagonalLinear (a b : ℝ) : Plane →ₗ[ℝ] Plane where
  toFun x := !₂[a * x 1, b * x 0]
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' r x := by ext i; fin_cases i <;> simp <;> ring

def offDiagonal (a b : ℝ) : Plane →L[ℝ] Plane :=
  (offDiagonalLinear a b).toContinuousLinearMap

def physicalScale (h : ℝ) (hh : h ≠ 0) : Plane ≃ₗ[ℝ] Plane where
  toFun x := !₂[x 0, h * x 1]
  invFun x := !₂[x 0, x 1 / h]
  map_add' x y := by ext i; fin_cases i <;> simp; ring
  map_smul' r x := by ext i; fin_cases i <;> simp; ring
  left_inv x := by ext i; fin_cases i <;> simp [hh]
  right_inv x := by
    ext i
    fin_cases i
    · simp
    · simp; field_simp

end SpectralNormComparison

end

end OAI
