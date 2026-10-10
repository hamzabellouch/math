import OAI.Analysis.Quantum.DimensionTen.AlphaMinors
import OAI.Analysis.Quantum.DimensionTen.Cofactors
import OAI.Analysis.Quantum.DimensionTen.EigenAdjoin
import OAI.Analysis.Quantum.DimensionTen.EigenData

namespace OAI

section
noncomputable section
open Matrix Polynomial
namespace DimensionTen.Border

lemma cofactor_last_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (t : Fin 3 → R) :
    f (cofactorKernel (Fin.cons 1 t) 3) =
      cofactorKernel (Fin.cons 1 (fun j => f (t j))) 3 := by
  rw [cofactor_chart_last, cofactor_chart_last, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_mul, map_intCast, low_map]

lemma rank_embedding {R : Type*} [Field R] [Algebra ℚ R] (σ : L →ₐ[ℚ] R) :
    (pencilR (Fin.cons 1 (fun j => σ (alpha j)))).rank < 4 := by
  apply rank_lt_of_kernel _ (cofactorKernel (Fin.cons 1 (fun j => σ (alpha j))))
  · intro h
    have hz := congrFun h 3
    have hc := cofactor_last_map σ.toRingHom alpha
    have hne : σ.toRingHom (cofactorKernel (Fin.cons 1 alpha) 3) ≠ 0 :=
      (map_ne_zero σ.toRingHom).mpr cofactor_alpha_last_ne
    exact hne (hc.trans hz)
  · exact cofactorKernel_eq_zero _ (minors_embedding σ)

lemma root_eq_alpha : AdjoinRoot.root fQ = (d : ℚ) • alpha 0 := by
  change _ = (d : ℚ) • ((d : ℚ)⁻¹ • AdjoinRoot.root fQ)
  rw [smul_smul, mul_inv_cancel₀ dQ_ne_zero, one_smul]

lemma embedding_points_injective {R : Type*} [CommRing R] [Algebra ℚ R] :
    Function.Injective (fun σ : L →ₐ[ℚ] R => fun j : Fin 3 => σ (alpha j)) := by
  intro σ τ h
  apply AdjoinRoot.algHom_ext
  erw [root_eq_alpha, map_smul σ (d : ℚ) (alpha 0), map_smul τ (d : ℚ) (alpha 0)]
  exact congrArg (fun a => (d : ℚ) • a) (congrFun h 0)

end DimensionTen.Border

end
end

section
noncomputable section
open Matrix Polynomial
namespace DimensionTen.Border

lemma C_relation_map {R : Type*} [CommRing R] [Algebra ℚ R] :
    H.map (Int.castRingHom R) * C.map (algebraMap ℚ R) = -(D.map (Int.castRingHom R)) := by
  have h := congrArg (fun A : Matrix (Fin 15) (Fin 20) ℚ => A.map (algebraMap ℚ R)) C_relation
  rw [Matrix.map_mul] at h
  have hr : (-D.map (Int.castRingHom ℚ)).map (algebraMap ℚ R) =
      -(D.map (Int.castRingHom R)) := by ext i j; simp
  rw [map_int_rat, hr] at h
  exact h

lemma high_relation_point {R : Type*} [Field R] [Algebra ℚ R] (t : Fin 3 → R)
    (hm : minor (Fin.cons 1 t) = 0) :
    ∀ i, high t i = ∑ m, (algebraMap ℚ R) (C i m) * low t m := by
  let : CharZero R := Algebra.charZero_of_charZero ℚ R
  have he : high t = C.map (algebraMap ℚ R) *ᵥ low t := by
    apply H_mulVec_injective
    change H.map (Int.castRingHom R) *ᵥ high t = H.map (Int.castRingHom R) *ᵥ (C.map (algebraMap ℚ R) *ᵥ low t)
    erw [Matrix.mulVec_mulVec, C_relation_map, Matrix.neg_mulVec]
    rw [minors_eq, homogeneousLow_chart] at hm
    change D.map (Int.castRingHom R) *ᵥ low t + H.map (Int.castRingHom R) *ᵥ high t = 0 at hm
    exact eq_neg_of_add_eq_zero_right hm
  intro i
  exact congrFun he i

def pointEval {R : Type*} [CommRing R] [Algebra ℚ R] (t : Fin 3 → R) : L →ₗ[ℚ] R where
  toFun a := ∑ m, (algebraMap ℚ R) (E a m) * low t m
  map_add' a b := by
    simp [map_add, Finset.sum_add_distrib, add_mul]
  map_smul' c a := by
    change (∑ m, (algebraMap ℚ R) (E (c • a) m) * low t m) = _
    erw [E.map_smul]
    simp [Pi.smul_apply, Algebra.smul_def, Finset.mul_sum, mul_assoc]

lemma pointEval_one {R : Type*} [CommRing R] [Algebra ℚ R] (t : Fin 3 → R) :
    pointEval t 1 = 1 := by
  change (∑ m, (algebraMap ℚ R) (E 1 m) * low t m) = 1
  rw [E_one, single_to_sum, low_zero]

lemma pointEval_alpha_mul {R : Type*} [CommRing R] [Algebra ℚ R]
    (t : Fin 3 → R) (h : ∀ i, high t i = ∑ m, (algebraMap ℚ R) (C i m) * low t m)
    (j : Fin 3) (a : L) : pointEval t (alpha j * a) = t j * pointEval t a := by
  change (∑ m, (algebraMap ℚ R) (E (alpha j * a) m) * low t m) =
    t j * ∑ m, (algebraMap ℚ R) (E a m) * low t m
  rw [E_mul, rho_alpha]
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  erw [mul_left_comm (t j), eigen_columns t h j k, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  ring

lemma pointEval_root_mul {R : Type*} [CommRing R] [Algebra ℚ R]
    (t : Fin 3 → R) (h : ∀ i, high t i = ∑ m, (algebraMap ℚ R) (C i m) * low t m)
    (a : L) : pointEval t (AdjoinRoot.root fQ * a) =
      ((algebraMap ℚ R) (d : ℚ) * t 0) * pointEval t a := by
  erw [root_eq_alpha, smul_mul_assoc, map_smul, pointEval_alpha_mul t h 0 a,
    Algebra.smul_def, mul_assoc]

lemma embedding_of_minor_zero {R : Type*} [Field R] [Algebra ℚ R]
    (t : Fin 3 → R) (hm : minor (Fin.cons 1 t) = 0) :
    ∃ σ : L →ₐ[ℚ] R, ∀ j, σ (alpha j) = t j := by
  have h := high_relation_point t hm
  let σ := Arithmetic.algHomOfEigen fQ (pointEval t)
    ((algebraMap ℚ R) (d : ℚ) * t 0) (pointEval_one t) (pointEval_root_mul t h)
  refine ⟨σ, fun j => ?_⟩
  change pointEval t (alpha j) = t j
  have hh := pointEval_alpha_mul t h j 1
  simpa only [mul_one, pointEval_one] using hh

end DimensionTen.Border

end
end

end OAI
