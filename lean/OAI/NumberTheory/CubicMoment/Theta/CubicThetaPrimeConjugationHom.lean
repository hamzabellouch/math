import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeConjugation

namespace OAI

/-! The integral prime correspondence is multiplicative. Its relation
with the diagonal matrix is proved over the original Eisenstein ring. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaPrimeDiagonal (p : Eisenstein) : Matrix (Fin 2) (Fin 2) Eisenstein :=
  Matrix.diagonal ![p,1]

private lemma primeDiagonal_right_injective {p : Eisenstein} (hp : p≠0) :
    Function.Injective (fun A : Matrix (Fin 2) (Fin 2) Eisenstein => A*cubicThetaPrimeDiagonal p) := by
  intro A B he
  apply Matrix.ext
  intro i j
  have h := congrFun (congrFun he i) j
  simp only [cubicThetaPrimeDiagonal,Matrix.mul_diagonal] at h
  fin_cases j
  · norm_num at h
    exact h.resolve_right hp
  · simpa using h

lemma cubicThetaPrimeConjugatedMatrix_intertwines {p : Eisenstein} (hp : p≠0)
    (g : cubicThetaPrimeIwahori p) :
    (cubicThetaPrimeConjugatedMatrix hp g:Matrix (Fin 2) (Fin 2) Eisenstein)*cubicThetaPrimeDiagonal p=
      cubicThetaPrimeDiagonal p*(g.val.val:Matrix (Fin 2) (Fin 2) Eisenstein) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  · simp [cubicThetaPrimeDiagonal,Matrix.mul_diagonal,Matrix.diagonal_mul,cubicThetaPrimeConjugatedMatrix,mul_comm]
  · simp [cubicThetaPrimeDiagonal,Matrix.mul_diagonal,Matrix.diagonal_mul,cubicThetaPrimeConjugatedMatrix]
  · simpa [cubicThetaPrimeDiagonal,Matrix.mul_diagonal,Matrix.diagonal_mul,cubicThetaPrimeConjugatedMatrix,mul_comm]
      using cubicThetaPrimeIwahori_division hp g
  · simp [cubicThetaPrimeDiagonal,Matrix.mul_diagonal,Matrix.diagonal_mul,cubicThetaPrimeConjugatedMatrix]

def cubicThetaPrimeConjugateHom {p : Eisenstein} (hp : primary p) :
    cubicThetaPrimeIwahori p →* cubicThetaPrincipalGroup where
  toFun := cubicThetaPrimeConjugate hp
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [cubicThetaPrimeConjugate,cubicThetaPrimeConjugatedMatrix]
  map_mul' g h := by
    apply Subtype.ext
    apply Subtype.ext
    apply primeDiagonal_right_injective (primary_ne_zero hp)
    change (cubicThetaPrimeConjugatedMatrix (primary_ne_zero hp) (g*h):Matrix (Fin 2) (Fin 2) Eisenstein)*cubicThetaPrimeDiagonal p=
      ((cubicThetaPrimeConjugatedMatrix (primary_ne_zero hp) g:Matrix (Fin 2) (Fin 2) Eisenstein)*
        (cubicThetaPrimeConjugatedMatrix (primary_ne_zero hp) h:Matrix (Fin 2) (Fin 2) Eisenstein))*cubicThetaPrimeDiagonal p
    rw [cubicThetaPrimeConjugatedMatrix_intertwines,Matrix.mul_assoc,
      cubicThetaPrimeConjugatedMatrix_intertwines,←Matrix.mul_assoc,
      cubicThetaPrimeConjugatedMatrix_intertwines,Matrix.mul_assoc]
    rfl

end CubicFirstMoment

end

end OAI
