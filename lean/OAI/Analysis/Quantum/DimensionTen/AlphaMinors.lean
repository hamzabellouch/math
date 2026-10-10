import OAI.Analysis.Quantum.DimensionTen.BorderRelations
import OAI.Analysis.Quantum.DimensionTen.MinorRelations

namespace OAI

section
noncomputable section
open Matrix
namespace DimensionTen.Border

lemma C_relation : H.map (Int.castRingHom ℚ) * C = -(D.map (Int.castRingHom ℚ)) := by
  have h := congrArg (fun A : Matrix (Fin 15) (Fin 20) ℤ => A.map (Int.castRingHom ℚ)) relation
  have hc : H.map (Int.castRingHom ℚ) * Cnum.map (Int.castRingHom ℚ) =
      -((d : ℚ) • D.map (Int.castRingHom ℚ)) := by
    rw [Matrix.map_mul] at h
    exact h.trans (by ext i j; simp [Matrix.map_apply, smul_eq_mul])
  rw [C, Matrix.mul_smul, hc, smul_neg, smul_smul, inv_mul_cancel₀ dQ_ne_zero, one_smul]

lemma map_int_rat {R m n : Type*} [Ring R] [Algebra ℚ R]
    (A : Matrix m n ℤ) : (A.map (Int.castRingHom ℚ)).map (algebraMap ℚ R) =
      A.map (Int.castRingHom R) := by
  ext i j
  simp

lemma high_alpha : high alpha = C.map (algebraMap ℚ L) *ᵥ low alpha := by
  ext i
  rw [high_relation]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Algebra.smul_def]
  congr 1

lemma minors_alpha : minor (Fin.cons 1 alpha) = 0 := by
  have hc := congrArg (fun A : Matrix (Fin 15) (Fin 20) ℚ => A.map (algebraMap ℚ L)) C_relation
  have hcL : H.map (Int.castRingHom L) * C.map (algebraMap ℚ L) =
      -(D.map (Int.castRingHom L)) := by
    rw [Matrix.map_mul] at hc
    have hr : (-D.map (Int.castRingHom ℚ)).map (algebraMap ℚ L) =
        -(D.map (Int.castRingHom L)) := by ext i j; simp
    rw [map_int_rat, hr] at hc
    exact hc
  rw [minors_eq, homogeneousLow_chart]
  change D.map (Int.castRingHom L) *ᵥ low alpha + H.map (Int.castRingHom L) *ᵥ high alpha = 0
  rw [high_alpha, Matrix.mulVec_mulVec, hcL,
    Matrix.neg_mulVec, add_neg_cancel]

lemma mon_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (t : Fin 3 → R) (i : Fin 35) : f (mon t i) = mon (fun j => f (t j)) i := by
  simp [mon]

lemma low_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (t : Fin 3 → R) (i : Fin 20) : f (low t i) = low (fun j => f (t j)) i := by
  exact mon_map f t _

lemma pencilR_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (x : Fin 4 → R) : (pencilR x).map f = pencilR (fun j => f (x j)) := by
  ext i j
  simp [pencilR, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

lemma minor_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (x : Fin 4 → R) (i : Fin 15) : f (minor x i) = minor (fun j => f (x j)) i := by
  rw [minor, RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.submatrix_map, pencilR_map]
  rfl

lemma minors_embedding {R : Type*} [Field R] [Algebra ℚ R] (σ : L →ₐ[ℚ] R) :
    minor (Fin.cons 1 (fun j => σ (alpha j))) = 0 := by
  ext i
  have h := congrArg σ (congrFun minors_alpha i)
  change σ.toRingHom (minor (Fin.cons 1 alpha) i) = σ.toRingHom 0 at h
  rw [minor_map σ.toRingHom] at h
  have he : (fun j : Fin 4 => σ ((Fin.cons (α := fun _ => L) 1 alpha) j)) = Fin.cons 1 (fun j => σ (alpha j)) := by
    ext j
    refine Fin.cases (by simp) (fun k => rfl) j
  change minor (fun j : Fin 4 => σ ((Fin.cons (α := fun _ => L) 1 alpha) j)) i = σ 0 at h
  rw [he, map_zero] at h
  exact h

end DimensionTen.Border

end
end

end OAI
