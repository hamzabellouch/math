import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Factorial.Basic

namespace OAI

namespace Laughlin.Certificate.MatrixCompute

def copyLabel {D : ℕ} (i : Fin ((D+1)/2)) : ℕ := 2*i.val+1

def copyWeight (D : ℕ) (i : Fin ((D+1)/2)) : ℚ :=
  1 / ((copyLabel i).factorial * (D-copyLabel i).factorial : ℕ)

def middle (D : ℕ) (Y : Matrix (Fin ((D+1)/2)) (Fin ((D+1)/2)) ℚ) :
    Matrix (Fin ((D+1)/2)) (Fin ((D+1)/2)) ℚ :=
  Matrix.diagonal (fun i => ((if copyLabel i = 1 then 2 else 0) + (3/10^6 : ℚ)) *
    copyWeight D i) - Matrix.diagonal (copyWeight D) * Y * Matrix.diagonal (copyWeight D)

def compressed (D : ℕ) (Y Z : Matrix (Fin ((D+1)/2)) (Fin ((D+1)/2)) ℚ) :
    Matrix (Fin ((D+1)/2)) (Fin ((D+1)/2)) ℚ := Z * middle D Y * Z

open scoped BigOperators

theorem middle_apply (D : ℕ) (Y : Matrix (Fin ((D+1)/2)) (Fin ((D+1)/2)) ℚ)
    (i j : Fin ((D+1)/2)) :
    middle D Y i j =
      (if i = j then ((if copyLabel i = 1 then 2 else 0) + (3/10^6 : ℚ)) * copyWeight D i else 0) -
        copyWeight D i * Y i j * copyWeight D j := by
  simp only [middle, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.diagonal_apply]

theorem compressed_apply (D : ℕ) (Y Z : Matrix (Fin ((D+1)/2)) (Fin ((D+1)/2)) ℚ)
    (i j : Fin ((D+1)/2)) :
    compressed D Y Z i j =
      ∑ k, (∑ l, Z i l *
        ((if l = k then ((if copyLabel l = 1 then 2 else 0) + (3/10^6 : ℚ)) * copyWeight D l else 0) -
          copyWeight D l * Y l k * copyWeight D k)) * Z k j := by
  simp only [compressed, Matrix.mul_apply, middle_apply]

theorem ldl_apply {n : ℕ} (L : Matrix (Fin n) (Fin n) ℚ) (d : Fin n → ℚ)
    (i j : Fin n) :
    (L * Matrix.diagonal d * L.transpose) i j = ∑ k, L i k * d k * L j k := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]

end Laughlin.Certificate.MatrixCompute

end OAI
