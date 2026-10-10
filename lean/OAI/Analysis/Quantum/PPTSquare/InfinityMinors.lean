import OAI.Analysis.Quantum.PPTSquare.AffineMinors

namespace OAI

noncomputable section
open scoped BigOperators
open Matrix
namespace PencilAlgebra
variable {K : Type*} [CommRing K]
lemma pencil_infinity (t : Fin 3 → K) : pencil ![0,t 0,t 1,t 2] =
  !![-12*t 0,6*t 1,-2*t 1-4*t 2,-3*t 2;
    6*t 1,-6*t 0+6*t 1-2*t 2,-3*t 2,2*t 1-4*t 2;
    -2*t 1-4*t 2,-3*t 2,6*t 0+10*t 1+11*t 2,6*t 2;
    -3*t 2,2*t 1-4*t 2,6*t 2,12*t 0+24*t 1+25*t 2;
    -6*t 0+6*t 2,6*t 2,6*t 0,6*t 0+6*t 1;
    -6*t 0,-6*t 0-6*t 1-6*t 2,6*t 0+6*t 1+6*t 2,-6*t 1+6*t 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pencil, ExplicitPencil.data, Fin.sum_univ_succ] <;> ring

lemma minor_infinity0 (t : Fin 3 → K) :
    minors ![0,t 0,t 1,t 2] 0 =
       ((H.map (Int.castRingHom K)).mulVec (w t)) 0 := by
  unfold minors
  rw [pencil_infinity, det4]
  norm_num [rows, H, w, highExp, Matrix.submatrix_apply, Matrix.map_apply,
    Matrix.of_apply, Fin.prod_univ_succ, Fin.sum_univ_succ, Matrix.mulVec, dotProduct]
  ring
lemma minor_infinity1 (t : Fin 3 → K) :
    minors ![0,t 0,t 1,t 2] 1 =
       ((H.map (Int.castRingHom K)).mulVec (w t)) 1 := by
  unfold minors
  rw [pencil_infinity, det4]
  norm_num [rows, H, w, highExp, Matrix.submatrix_apply, Matrix.map_apply,
    Matrix.of_apply, Fin.prod_univ_succ, Fin.sum_univ_succ, Matrix.mulVec, dotProduct]
  ring
lemma minor_infinity2 (t : Fin 3 → K) :
    minors ![0,t 0,t 1,t 2] 2 =
       ((H.map (Int.castRingHom K)).mulVec (w t)) 2 := by
  unfold minors
  rw [pencil_infinity, det4]
  norm_num [rows, H, w, highExp, Matrix.submatrix_apply, Matrix.map_apply,
    Matrix.of_apply, Fin.prod_univ_succ, Fin.sum_univ_succ, Matrix.mulVec, dotProduct]
  ring
lemma minor_infinity3 (t : Fin 3 → K) :
    minors ![0,t 0,t 1,t 2] 3 =
       ((H.map (Int.castRingHom K)).mulVec (w t)) 3 := by
  unfold minors
  rw [pencil_infinity, det4]
  norm_num [rows, H, w, highExp, Matrix.submatrix_apply, Matrix.map_apply,
    Matrix.of_apply, Fin.prod_univ_succ, Fin.sum_univ_succ, Matrix.mulVec, dotProduct]
  ring
lemma minor_infinity4 (t : Fin 3 → K) :
    minors ![0,t 0,t 1,t 2] 4 =
       ((H.map (Int.castRingHom K)).mulVec (w t)) 4 := by
  unfold minors
  rw [pencil_infinity, det4]
  norm_num [rows, H, w, highExp, Matrix.submatrix_apply, Matrix.map_apply,
    Matrix.of_apply, Fin.prod_univ_succ, Fin.sum_univ_succ, Matrix.mulVec, dotProduct]
  ring
lemma minor_infinity5 (t : Fin 3 → K) :
    minors ![0,t 0,t 1,t 2] 5 =
       ((H.map (Int.castRingHom K)).mulVec (w t)) 5 := by
  unfold minors
  rw [pencil_infinity, det4]
  norm_num [rows, H, w, highExp, Matrix.submatrix_apply, Matrix.map_apply,
    Matrix.of_apply, Fin.prod_univ_succ, Fin.sum_univ_succ, Matrix.mulVec, dotProduct]
  ring
lemma minor_infinity6 (t : Fin 3 → K) :
    minors ![0,t 0,t 1,t 2] 6 =
       ((H.map (Int.castRingHom K)).mulVec (w t)) 6 := by
  unfold minors
  rw [pencil_infinity, det4]
  norm_num [rows, H, w, highExp, Matrix.submatrix_apply, Matrix.map_apply,
    Matrix.of_apply, Fin.prod_univ_succ, Fin.sum_univ_succ, Matrix.mulVec, dotProduct]
  ring
lemma minor_infinity7 (t : Fin 3 → K) :
    minors ![0,t 0,t 1,t 2] 7 =
       ((H.map (Int.castRingHom K)).mulVec (w t)) 7 := by
  unfold minors
  rw [pencil_infinity, det4]
  norm_num [rows, H, w, highExp, Matrix.submatrix_apply, Matrix.map_apply,
    Matrix.of_apply, Fin.prod_univ_succ, Fin.sum_univ_succ, Matrix.mulVec, dotProduct]
  ring
lemma minor_infinity8 (t : Fin 3 → K) :
    minors ![0,t 0,t 1,t 2] 8 =
       ((H.map (Int.castRingHom K)).mulVec (w t)) 8 := by
  unfold minors
  rw [pencil_infinity, det4]
  norm_num [rows, H, w, highExp, Matrix.submatrix_apply, Matrix.map_apply,
    Matrix.of_apply, Fin.prod_univ_succ, Fin.sum_univ_succ, Matrix.mulVec, dotProduct]
  ring
lemma minor_infinity9 (t : Fin 3 → K) :
    minors ![0,t 0,t 1,t 2] 9 =
       ((H.map (Int.castRingHom K)).mulVec (w t)) 9 := by
  unfold minors
  rw [pencil_infinity, det4]
  norm_num [rows, H, w, highExp, Matrix.submatrix_apply, Matrix.map_apply,
    Matrix.of_apply, Fin.prod_univ_succ, Fin.sum_univ_succ, Matrix.mulVec, dotProduct]
  ring
lemma minor_infinity10 (t : Fin 3 → K) :
    minors ![0,t 0,t 1,t 2] 10 =
       ((H.map (Int.castRingHom K)).mulVec (w t)) 10 := by
  unfold minors
  rw [pencil_infinity, det4]
  norm_num [rows, H, w, highExp, Matrix.submatrix_apply, Matrix.map_apply,
    Matrix.of_apply, Fin.prod_univ_succ, Fin.sum_univ_succ, Matrix.mulVec, dotProduct]
  ring
lemma minor_infinity11 (t : Fin 3 → K) :
    minors ![0,t 0,t 1,t 2] 11 =
       ((H.map (Int.castRingHom K)).mulVec (w t)) 11 := by
  unfold minors
  rw [pencil_infinity, det4]
  norm_num [rows, H, w, highExp, Matrix.submatrix_apply, Matrix.map_apply,
    Matrix.of_apply, Fin.prod_univ_succ, Fin.sum_univ_succ, Matrix.mulVec, dotProduct]
  ring
lemma minor_infinity12 (t : Fin 3 → K) :
    minors ![0,t 0,t 1,t 2] 12 =
       ((H.map (Int.castRingHom K)).mulVec (w t)) 12 := by
  unfold minors
  rw [pencil_infinity, det4]
  norm_num [rows, H, w, highExp, Matrix.submatrix_apply, Matrix.map_apply,
    Matrix.of_apply, Fin.prod_univ_succ, Fin.sum_univ_succ, Matrix.mulVec, dotProduct]
  ring
lemma minor_infinity13 (t : Fin 3 → K) :
    minors ![0,t 0,t 1,t 2] 13 =
       ((H.map (Int.castRingHom K)).mulVec (w t)) 13 := by
  unfold minors
  rw [pencil_infinity, det4]
  norm_num [rows, H, w, highExp, Matrix.submatrix_apply, Matrix.map_apply,
    Matrix.of_apply, Fin.prod_univ_succ, Fin.sum_univ_succ, Matrix.mulVec, dotProduct]
  ring
lemma minor_infinity14 (t : Fin 3 → K) :
    minors ![0,t 0,t 1,t 2] 14 =
       ((H.map (Int.castRingHom K)).mulVec (w t)) 14 := by
  unfold minors
  rw [pencil_infinity, det4]
  norm_num [rows, H, w, highExp, Matrix.submatrix_apply, Matrix.map_apply,
    Matrix.of_apply, Fin.prod_univ_succ, Fin.sum_univ_succ, Matrix.mulVec, dotProduct]
  ring
lemma minors_infinity (t : Fin 3 → K) :
    minors ![0,t 0,t 1,t 2] = (H.map (Int.castRingHom K)).mulVec (w t) := by
  ext i
  fin_cases i
  · exact minor_infinity0 t
  · exact minor_infinity1 t
  · exact minor_infinity2 t
  · exact minor_infinity3 t
  · exact minor_infinity4 t
  · exact minor_infinity5 t
  · exact minor_infinity6 t
  · exact minor_infinity7 t
  · exact minor_infinity8 t
  · exact minor_infinity9 t
  · exact minor_infinity10 t
  · exact minor_infinity11 t
  · exact minor_infinity12 t
  · exact minor_infinity13 t
  · exact minor_infinity14 t
end PencilAlgebra

end

end OAI
