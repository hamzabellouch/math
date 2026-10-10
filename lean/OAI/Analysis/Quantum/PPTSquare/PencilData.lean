import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import OAI.Analysis.Quantum.PPTSquare.Recurrence

namespace OAI

noncomputable section
open scoped BigOperators
open Matrix
namespace ExplicitPencil

def data : Fin 4 → Matrix (Fin 6) (Fin 4) ℤ :=
  ![!![6,0,0,0;0,6,0,0;0,0,6,0;0,0,0,6;0,0,0,0;0,0,0,0],
    !![-12,0,0,0;0,-6,0,0;0,0,6,0;0,0,0,12;-6,0,6,6;-6,-6,6,0],
    !![0,6,-2,0;6,6,0,2;-2,0,10,0;0,2,0,24;0,0,0,6;0,-6,6,-6],
    !![0,0,-4,-3;0,-2,-3,-4;-4,-3,11,6;-3,-4,6,25;6,6,0,0;0,-6,6,6]]

end ExplicitPencil
namespace PencilAlgebra
variable {K : Type*} [CommRing K]
def pencil (x : Fin 4 → K) : Matrix (Fin 6) (Fin 4) K :=
  ∑ i, x i • (ExplicitPencil.data i).map (Int.castRingHom K)
def minors (x : Fin 4 → K) : Fin 15 → K :=
  fun r => ((pencil x).submatrix (rows r) id).det
lemma det4 (A : Matrix (Fin 4) (Fin 4) K) : A.det =
    A 0 0 * (A 1 1*A 2 2*A 3 3-A 1 1*A 2 3*A 3 2-A 1 2*A 2 1*A 3 3+A 1 2*A 2 3*A 3 1+A 1 3*A 2 1*A 3 2-A 1 3*A 2 2*A 3 1)
  - A 0 1 * (A 1 0*A 2 2*A 3 3-A 1 0*A 2 3*A 3 2-A 1 2*A 2 0*A 3 3+A 1 2*A 2 3*A 3 0+A 1 3*A 2 0*A 3 2-A 1 3*A 2 2*A 3 0)
  + A 0 2 * (A 1 0*A 2 1*A 3 3-A 1 0*A 2 3*A 3 1-A 1 1*A 2 0*A 3 3+A 1 1*A 2 3*A 3 0+A 1 3*A 2 0*A 3 1-A 1 3*A 2 1*A 3 0)
  - A 0 3 * (A 1 0*A 2 1*A 3 2-A 1 0*A 2 2*A 3 1-A 1 1*A 2 0*A 3 2+A 1 1*A 2 2*A 3 0+A 1 2*A 2 0*A 3 1-A 1 2*A 2 1*A 3 0) := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succAbove]
  ring

lemma pencil_affine (t : Fin 3 → K) : pencil ![1,t 0,t 1,t 2] =
  !![6-12*t 0,6*t 1,-2*t 1-4*t 2,-3*t 2;
    6*t 1,6-6*t 0+6*t 1-2*t 2,-3*t 2,2*t 1-4*t 2;
    -2*t 1-4*t 2,-3*t 2,6+6*t 0+10*t 1+11*t 2,6*t 2;
    -3*t 2,2*t 1-4*t 2,6*t 2,6+12*t 0+24*t 1+25*t 2;
    -6*t 0+6*t 2,6*t 2,6*t 0,6*t 0+6*t 1;
    -6*t 0,-6*t 0-6*t 1-6*t 2,6*t 0+6*t 1+6*t 2,-6*t 1+6*t 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pencil, ExplicitPencil.data, Fin.sum_univ_succ] <;> ring

end PencilAlgebra

end

end OAI
