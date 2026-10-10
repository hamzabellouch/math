import OAI.Analysis.WeakInfiniteness.CPSchwarz

namespace OAI

/-! # Norm control for the unital return map in a nuclear approximation -/

noncomputable section
open scoped CStarAlgebra ComplexOrder

namespace WeakPureInfiniteness

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

lemma completelyPositive_schwarz_of_unital {φ : A →L[ℂ] B}
    (hφ : CompletelyPositive φ) (h1 : φ 1 = 1) (a : A) :
    star (φ a) * φ a ≤ φ (star a * a) := by
  let R : CStarMatrix (Fin 2) (Fin 2) A := CStarMatrix.ofMatrix !![a,1;0,0]
  let M := matrixLinearMap φ (star R * R)
  have hM : 0 ≤ M := matrixLinearMap_nonneg hφ (star_mul_self_nonneg R)
  let V : CStarMatrix (Fin 2) (Fin 2) B := CStarMatrix.ofMatrix !![1,0;-φ a,0]
  have hN := cstarMatrix_diagonal_nonneg (star V * M * V)
    (star_left_conjugate_nonneg hM V) 0
  have he : (star V * M * V) 0 0 = φ (star a * a) - star (φ a) * φ a := by
    simp [V, M, R, CStarMatrix.mul_apply, CStarMatrix.star_apply,
      Fin.sum_univ_two, completelyPositive_map_star hφ, h1, sub_eq_add_neg]
  exact sub_nonneg.mp (he ▸ hN)

lemma completelyPositive_norm_apply_le_of_unital {φ : A →L[ℂ] B}
    (hφ : CompletelyPositive φ) (h1 : φ 1 = 1) (a : A) : ‖φ a‖ ≤ ‖a‖ := by
  have hmono : φ (star a * a) ≤ algebraMap ℝ B (‖a‖ ^ 2) := by
    have h := map_nonneg hφ.toMap
      (sub_nonneg.mpr (CStarAlgebra.star_mul_le_algebraMap_norm_sq a))
    rw [map_sub, sub_nonneg] at h
    have he : φ (algebraMap ℝ A (‖a‖ ^ 2)) = algebraMap ℝ B (‖a‖ ^ 2) := by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        LinearMapClass.map_smul_of_tower, h1]
    exact he ▸ h
  have hn : ‖star (φ a) * φ a‖ ≤ ‖a‖ ^ 2 :=
    (CStarAlgebra.norm_le_iff_le_algebraMap _ (sq_nonneg ‖a‖)
      (star_mul_self_nonneg _)).mpr
      ((completelyPositive_schwarz_of_unital hφ h1 a).trans hmono)
  rw [CStarRing.norm_star_mul_self] at hn
  nlinarith [norm_nonneg a, norm_nonneg (φ a)]

lemma completelyPositive_norm_le_of_unital {φ : A →L[ℂ] B}
    (hφ : CompletelyPositive φ) (h1 : φ 1 = 1) : ‖φ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro a
  simpa only [one_mul] using completelyPositive_norm_apply_le_of_unital hφ h1 a

end WeakPureInfiniteness

end

end OAI
