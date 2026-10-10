import OAI.Analysis.BoundedHochschild.MatrixDilation

namespace OAI

/-! The elementary two-by-two positivity test for a contraction. -/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild.KadisonRingrose

open HochschildMatrixDilation

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def positiveUnitBlock (a : A) : Mat A := 1 + offdiag a (star a)

lemma positiveUnitBlock_nonneg (a : A) (ha : ‖a‖ ≤ 1) : 0 ≤ positiveUnitBlock a := by
  have hsq : star a * a ≤ 1 := by
    apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg a)).mp
    rw [CStarRing.norm_star_mul_self]
    nlinarith [norm_nonneg a]
  let d := CFC.sqrt (1 - star a * a)
  have hd : star d * d = 1 - star a * a := by
    rw [(CFC.sqrt_nonneg _).isSelfAdjoint.star_eq]
    exact CFC.sqrt_mul_sqrt_self _ (sub_nonneg.mpr hsq)
  let R : Mat A := CStarMatrix.ofMatrix !![1, a; 0, d]
  have hR : star R * R = positiveUnitBlock a := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp [R, positiveUnitBlock, offdiag, CStarMatrix.mul_apply, CStarMatrix.star_apply,
        Fin.sum_univ_two]
    · simp [R, positiveUnitBlock, offdiag, CStarMatrix.mul_apply, CStarMatrix.star_apply,
        Fin.sum_univ_two]
    · simp [R, positiveUnitBlock, offdiag, CStarMatrix.mul_apply, CStarMatrix.star_apply,
        Fin.sum_univ_two]
    · simp [R, positiveUnitBlock, offdiag, CStarMatrix.mul_apply, CStarMatrix.star_apply,
        Fin.sum_univ_two, hd]
  rw [← hR]
  exact star_mul_self_nonneg R

lemma norm_le_one_of_positiveUnitBlock (a : A) (ha : 0 ≤ positiveUnitBlock a) : ‖a‖ ≤ 1 := by
  let V : Mat A := CStarMatrix.ofMatrix !![-a, 0; 1, 0]
  have hp := diagEntry_nonneg (star V * positiveUnitBlock a * V)
    (star_left_conjugate_nonneg ha V) 0
  have he : (star V * positiveUnitBlock a * V) 0 0 = 1 - star a * a := by
    simp [V, positiveUnitBlock, offdiag, CStarMatrix.mul_apply, CStarMatrix.star_apply,
      Fin.sum_univ_two]
    noncomm_ring
  rw [he] at hp
  have hn := (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg a)).mpr
    (sub_nonneg.mp hp)
  rw [CStarRing.norm_star_mul_self] at hn
  exact (sq_le_one_iff₀ (norm_nonneg a)).mp (by simpa only [pow_two] using hn)

theorem positiveUnitBlock_nonneg_iff (a : A) : 0 ≤ positiveUnitBlock a ↔ ‖a‖ ≤ 1 :=
  ⟨norm_le_one_of_positiveUnitBlock a, positiveUnitBlock_nonneg a⟩

end BoundedHochschild.KadisonRingrose

end

end OAI
