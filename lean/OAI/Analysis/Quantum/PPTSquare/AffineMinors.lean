import OAI.Analysis.Quantum.PPTSquare.PencilData

namespace OAI

noncomputable section
open scoped BigOperators
open Matrix
namespace PencilAlgebra
variable {K : Type*} [CommRing K]
lemma minor_affine0 (t : Fin 3 → K) :
    minors ![1,t 0,t 1,t 2] 0 =
      ((D.map (Int.castRingHom K)).mulVec (v t) +
       (H.map (Int.castRingHom K)).mulVec (w t)) 0 := by
  unfold minors
  rw [pencil_affine, det4]
  norm_num [rows, D, H, v, w, lowExp, highExp,
    Matrix.submatrix_apply, Matrix.map_apply, Matrix.of_apply, Fin.prod_univ_succ,
    Fin.sum_univ_succ, Matrix.mulVec, dotProduct]
  ring
lemma minor_affine1 (t : Fin 3 → K) :
    minors ![1,t 0,t 1,t 2] 1 =
      ((D.map (Int.castRingHom K)).mulVec (v t) +
       (H.map (Int.castRingHom K)).mulVec (w t)) 1 := by
  unfold minors
  rw [pencil_affine, det4]
  norm_num [rows, D, H, v, w, lowExp, highExp,
    Matrix.submatrix_apply, Matrix.map_apply, Matrix.of_apply, Fin.prod_univ_succ,
    Fin.sum_univ_succ, Matrix.mulVec, dotProduct]
  ring
lemma minor_affine2 (t : Fin 3 → K) :
    minors ![1,t 0,t 1,t 2] 2 =
      ((D.map (Int.castRingHom K)).mulVec (v t) +
       (H.map (Int.castRingHom K)).mulVec (w t)) 2 := by
  unfold minors
  rw [pencil_affine, det4]
  norm_num [rows, D, H, v, w, lowExp, highExp,
    Matrix.submatrix_apply, Matrix.map_apply, Matrix.of_apply, Fin.prod_univ_succ,
    Fin.sum_univ_succ, Matrix.mulVec, dotProduct]
  ring
lemma minor_affine3 (t : Fin 3 → K) :
    minors ![1,t 0,t 1,t 2] 3 =
      ((D.map (Int.castRingHom K)).mulVec (v t) +
       (H.map (Int.castRingHom K)).mulVec (w t)) 3 := by
  unfold minors
  rw [pencil_affine, det4]
  norm_num [rows, D, H, v, w, lowExp, highExp,
    Matrix.submatrix_apply, Matrix.map_apply, Matrix.of_apply, Fin.prod_univ_succ,
    Fin.sum_univ_succ, Matrix.mulVec, dotProduct]
  ring
lemma minor_affine4 (t : Fin 3 → K) :
    minors ![1,t 0,t 1,t 2] 4 =
      ((D.map (Int.castRingHom K)).mulVec (v t) +
       (H.map (Int.castRingHom K)).mulVec (w t)) 4 := by
  unfold minors
  rw [pencil_affine, det4]
  norm_num [rows, D, H, v, w, lowExp, highExp,
    Matrix.submatrix_apply, Matrix.map_apply, Matrix.of_apply, Fin.prod_univ_succ,
    Fin.sum_univ_succ, Matrix.mulVec, dotProduct]
  ring
lemma minor_affine5 (t : Fin 3 → K) :
    minors ![1,t 0,t 1,t 2] 5 =
      ((D.map (Int.castRingHom K)).mulVec (v t) +
       (H.map (Int.castRingHom K)).mulVec (w t)) 5 := by
  unfold minors
  rw [pencil_affine, det4]
  norm_num [rows, D, H, v, w, lowExp, highExp,
    Matrix.submatrix_apply, Matrix.map_apply, Matrix.of_apply, Fin.prod_univ_succ,
    Fin.sum_univ_succ, Matrix.mulVec, dotProduct]
  ring
lemma minor_affine6 (t : Fin 3 → K) :
    minors ![1,t 0,t 1,t 2] 6 =
      ((D.map (Int.castRingHom K)).mulVec (v t) +
       (H.map (Int.castRingHom K)).mulVec (w t)) 6 := by
  unfold minors
  rw [pencil_affine, det4]
  norm_num [rows, D, H, v, w, lowExp, highExp,
    Matrix.submatrix_apply, Matrix.map_apply, Matrix.of_apply, Fin.prod_univ_succ,
    Fin.sum_univ_succ, Matrix.mulVec, dotProduct]
  ring
lemma minor_affine7 (t : Fin 3 → K) :
    minors ![1,t 0,t 1,t 2] 7 =
      ((D.map (Int.castRingHom K)).mulVec (v t) +
       (H.map (Int.castRingHom K)).mulVec (w t)) 7 := by
  unfold minors
  rw [pencil_affine, det4]
  norm_num [rows, D, H, v, w, lowExp, highExp,
    Matrix.submatrix_apply, Matrix.map_apply, Matrix.of_apply, Fin.prod_univ_succ,
    Fin.sum_univ_succ, Matrix.mulVec, dotProduct]
  ring
lemma minor_affine8 (t : Fin 3 → K) :
    minors ![1,t 0,t 1,t 2] 8 =
      ((D.map (Int.castRingHom K)).mulVec (v t) +
       (H.map (Int.castRingHom K)).mulVec (w t)) 8 := by
  unfold minors
  rw [pencil_affine, det4]
  norm_num [rows, D, H, v, w, lowExp, highExp,
    Matrix.submatrix_apply, Matrix.map_apply, Matrix.of_apply, Fin.prod_univ_succ,
    Fin.sum_univ_succ, Matrix.mulVec, dotProduct]
  ring
lemma minor_affine9 (t : Fin 3 → K) :
    minors ![1,t 0,t 1,t 2] 9 =
      ((D.map (Int.castRingHom K)).mulVec (v t) +
       (H.map (Int.castRingHom K)).mulVec (w t)) 9 := by
  unfold minors
  rw [pencil_affine, det4]
  norm_num [rows, D, H, v, w, lowExp, highExp,
    Matrix.submatrix_apply, Matrix.map_apply, Matrix.of_apply, Fin.prod_univ_succ,
    Fin.sum_univ_succ, Matrix.mulVec, dotProduct]
  ring
lemma minor_affine10 (t : Fin 3 → K) :
    minors ![1,t 0,t 1,t 2] 10 =
      ((D.map (Int.castRingHom K)).mulVec (v t) +
       (H.map (Int.castRingHom K)).mulVec (w t)) 10 := by
  unfold minors
  rw [pencil_affine, det4]
  norm_num [rows, D, H, v, w, lowExp, highExp,
    Matrix.submatrix_apply, Matrix.map_apply, Matrix.of_apply, Fin.prod_univ_succ,
    Fin.sum_univ_succ, Matrix.mulVec, dotProduct]
  ring
lemma minor_affine11 (t : Fin 3 → K) :
    minors ![1,t 0,t 1,t 2] 11 =
      ((D.map (Int.castRingHom K)).mulVec (v t) +
       (H.map (Int.castRingHom K)).mulVec (w t)) 11 := by
  unfold minors
  rw [pencil_affine, det4]
  norm_num [rows, D, H, v, w, lowExp, highExp,
    Matrix.submatrix_apply, Matrix.map_apply, Matrix.of_apply, Fin.prod_univ_succ,
    Fin.sum_univ_succ, Matrix.mulVec, dotProduct]
  ring
lemma minor_affine12 (t : Fin 3 → K) :
    minors ![1,t 0,t 1,t 2] 12 =
      ((D.map (Int.castRingHom K)).mulVec (v t) +
       (H.map (Int.castRingHom K)).mulVec (w t)) 12 := by
  unfold minors
  rw [pencil_affine, det4]
  norm_num [rows, D, H, v, w, lowExp, highExp,
    Matrix.submatrix_apply, Matrix.map_apply, Matrix.of_apply, Fin.prod_univ_succ,
    Fin.sum_univ_succ, Matrix.mulVec, dotProduct]
  ring
lemma minor_affine13 (t : Fin 3 → K) :
    minors ![1,t 0,t 1,t 2] 13 =
      ((D.map (Int.castRingHom K)).mulVec (v t) +
       (H.map (Int.castRingHom K)).mulVec (w t)) 13 := by
  unfold minors
  rw [pencil_affine, det4]
  norm_num [rows, D, H, v, w, lowExp, highExp,
    Matrix.submatrix_apply, Matrix.map_apply, Matrix.of_apply, Fin.prod_univ_succ,
    Fin.sum_univ_succ, Matrix.mulVec, dotProduct]
  ring
lemma minor_affine14 (t : Fin 3 → K) :
    minors ![1,t 0,t 1,t 2] 14 =
      ((D.map (Int.castRingHom K)).mulVec (v t) +
       (H.map (Int.castRingHom K)).mulVec (w t)) 14 := by
  unfold minors
  rw [pencil_affine, det4]
  norm_num [rows, D, H, v, w, lowExp, highExp,
    Matrix.submatrix_apply, Matrix.map_apply, Matrix.of_apply, Fin.prod_univ_succ,
    Fin.sum_univ_succ, Matrix.mulVec, dotProduct]
  ring
lemma minors_affine (t : Fin 3 → K) :
    minors ![1,t 0,t 1,t 2] =
      (D.map (Int.castRingHom K)).mulVec (v t) +
       (H.map (Int.castRingHom K)).mulVec (w t) := by
  ext i
  fin_cases i
  · exact minor_affine0 t
  · exact minor_affine1 t
  · exact minor_affine2 t
  · exact minor_affine3 t
  · exact minor_affine4 t
  · exact minor_affine5 t
  · exact minor_affine6 t
  · exact minor_affine7 t
  · exact minor_affine8 t
  · exact minor_affine9 t
  · exact minor_affine10 t
  · exact minor_affine11 t
  · exact minor_affine12 t
  · exact minor_affine13 t
  · exact minor_affine14 t
end PencilAlgebra

end

end OAI
