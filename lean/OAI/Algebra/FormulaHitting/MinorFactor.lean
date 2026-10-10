import OAI.Algebra.FormulaHitting.Minors
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace OAI

noncomputable section

namespace NCHitting

open Matrix

variable {R : Type*} [CommRing R] [IsDomain R]
variable {K I : Type*} [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I]

theorem exists_nonzero_divisible_minor
    (Z H : Matrix K I R) (G : Matrix I I R) (D W : Matrix K K R)
    (C : Matrix K I R) (E : Matrix I K R)
    (hG : IsUnit G) (hD : D.det ≠ 0) (hW : W.det ≠ 0)
    (hZG : Z * G = D * H) (hHC : H = W * C) (hHE : W = H * E) :
    ∃ f : K → I, (Z.submatrix id f).det ≠ 0 ∧ W.det ∣ (Z.submatrix id f).det := by
  classical
  have hprod : Z * (G * E) = D * W := by
    rw [← Matrix.mul_assoc, hZG, Matrix.mul_assoc, ← hHE]
  have hprod0 : (Z * (G * E)).det ≠ 0 := by
    rw [hprod, Matrix.det_mul]
    exact mul_ne_zero hD hW
  obtain ⟨f, hf⟩ := exists_minor_ne_zero_of_mul_det_ne_zero Z (G * E) hprod0
  refine ⟨f, hf, ?_⟩
  have hGdet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hG
  have hZ : Z = (D * W) * (C * G⁻¹) := by
    calc
      Z = (Z * G) * G⁻¹ := (Matrix.mul_nonsing_inv_cancel_right G Z hGdet).symm
      _ = (D * W) * (C * G⁻¹) := by rw [hZG, hHC]; simp only [Matrix.mul_assoc]
  have hsub : Z.submatrix id f = (D * W) * ((C * G⁻¹).submatrix id f) := by
    rw [hZ]
    rfl
  rw [hsub, Matrix.det_mul, Matrix.det_mul]
  exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _

end NCHitting

end

end OAI
