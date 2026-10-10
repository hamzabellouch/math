import OAI.Analysis.Pureness.GroupAlgebra.FreeGroupPartialTranslations
import OAI.Analysis.Pureness.Tensor.SpatialCoordinateProjection
import OAI.Analysis.Pureness.Tensor.SpatialCommutingTensor
import OAI.Analysis.Pureness.Operators.ProjectionWeightedBounds

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzComparison
open scoped TensorProduct CStarAlgebra
lemma sum_mul_star_sum_of_orthogonal {B ι : Type*} [CStarAlgebra B] [Fintype ι]
    (x : ι → B) (hx : ∀ i j, i ≠ j → x i * star (x j) = 0) :
    (∑ i, x i) * star (∑ i, x i) = ∑ i, x i * star (x i) := by
  have h := star_sum_mul_sum_of_orthogonal (fun i => star (x i))
    (fun i j hij => by simpa only [star_star] using hx i j hij)
  simpa only [← star_sum, star_star] using h

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H))

abbrev spatialPartialOperatorOrder : PartialOrder
    (SpatialHilbert H (GroupL2 (FreeGroup ℕ)) →L[ℂ] SpatialHilbert H (GroupL2 (FreeGroup ℕ))) :=
  CStarAlgebra.spectralOrder _

attribute [local instance] spatialPartialOperatorOrder

abbrev spatialPartialOperatorStarOrdered : StarOrderedRing
    (SpatialHilbert H (GroupL2 (FreeGroup ℕ)) →L[ℂ] SpatialHilbert H (GroupL2 (FreeGroup ℕ))) :=
  CStarAlgebra.spectralOrderedRing
    (SpatialHilbert H (GroupL2 (FreeGroup ℕ)) →L[ℂ] SpatialHilbert H (GroupL2 (FreeGroup ℕ)))

attribute [local instance] spatialPartialOperatorStarOrdered

omit [CompleteSpace H] in
lemma spatialTensorOp_sub_right (S : H →L[ℂ] H) {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] (T U : K →L[ℂ] K) :
    spatialTensorOp S (T - U) = spatialTensorOp S T - spatialTensorOp S U := by
  have h := spatialTensorOp_add_right S (T - U) U
  rw [sub_add_cancel] at h
  exact eq_sub_iff_add_eq.mpr h.symm

def spatialLetterSum {n : ℕ} (b : Bool) (a : Fin n → A) :=
  ∑ i, spatialTensorOp (α (a i)) (freeLetterProjection (i : ℕ) b)

omit [PartialOrder A] [StarOrderedRing A] in
lemma spatialLetterSum_compressions {n : ℕ} (b : Bool) (a : Fin n → A) :
    spatialLetterSum α b a = ∑ i : Fin n,
      spatialRightOperator (H := H) (freeLetterProjection (i : ℕ) b) *
        spatialLeftHom (K := GroupL2 (FreeGroup ℕ)) α (a i) *
          spatialRightOperator (H := H) (freeLetterProjection (i : ℕ) b) := by
  apply Finset.sum_congr rfl
  intro i _
  change spatialTensorOp _ _ = spatialTensorOp 1 _ * spatialTensorOp _ 1 * spatialTensorOp 1 _
  rw [← spatialTensorOp_mul, ← spatialTensorOp_mul, one_mul, mul_one, mul_one,
    (freeLetterProjection_isProjection (i : ℕ) b).isIdempotentElem.eq]

lemma spatialLetterSum_nonneg {n : ℕ} (b : Bool) (a : Fin n → A) (ha : ∀ i, 0 ≤ a i) :
    0 ≤ spatialLetterSum α b a := by
  rw [spatialLetterSum_compressions]
  apply Finset.sum_nonneg
  intro i _
  have hp := (freeLetterProjection_isProjection (i : ℕ) b).map (spatialRightOperator (H := H))
  simpa only [hp.isSelfAdjoint.star_eq] using star_left_conjugate_nonneg
    (map_nonneg (spatialLeftHom (K := GroupL2 (FreeGroup ℕ)) α) (ha i))
      (spatialRightOperator (H := H) (freeLetterProjection (i : ℕ) b))

omit [PartialOrder A] [StarOrderedRing A] in
lemma spatialPartialLeft_norm_le (a : A) :
    ‖spatialLeftHom (K := GroupL2 (FreeGroup ℕ)) α a‖ ≤ ‖a‖ := by
  change ‖spatialTensorOp (α a) (1 : GroupOperator (FreeGroup ℕ))‖ ≤ _
  exact (spatialTensorOp_norm_le _ _).trans ((mul_le_mul
    (NonUnitalStarAlgHom.norm_apply_le α.toNonUnitalStarAlgHom a)
    (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := GroupL2 (FreeGroup ℕ))) (norm_nonneg _) (norm_nonneg _)).trans_eq
      (mul_one _))

lemma spatialLetterSum_norm_le {n : ℕ} (b : Bool) (a : Fin n → A) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ i, 0 ≤ a i) (hn : ∀ i, ‖a i‖ ≤ C) : ‖spatialLetterSum α b a‖ ≤ C := by
  rw [spatialLetterSum_compressions]
  apply norm_orthogonal_positive_compressions_le
    (B := SpatialHilbert H (GroupL2 (FreeGroup ℕ)) →L[ℂ] SpatialHilbert H (GroupL2 (FreeGroup ℕ)))
    _ _ C hC
  · intro i
    exact (freeLetterProjection_isProjection (i : ℕ) b).map (spatialRightOperator (H := H))
  · intro i j hij
    rw [← map_mul, freeLetterProjection_disjoint _ _ b b (Fin.val_injective.ne hij), map_zero]
  · intro i
    exact map_nonneg (spatialLeftHom (K := GroupL2 (FreeGroup ℕ)) α) (ha i)
  · intro i
    exact (spatialPartialLeft_norm_le α _).trans (hn i)

def spatialFreeCreationSum {n : ℕ} (a : Fin n → A) :=
  ∑ i, spatialTensorOp (α (a i)) (freeCreation (i : ℕ))

def spatialFreeCancellationSum {n : ℕ} (a : Fin n → A) :=
  ∑ i, spatialTensorOp (α (a i)) (freeCancellation (i : ℕ))

omit [PartialOrder A] [StarOrderedRing A] in
lemma spatialFreeTranslation_split {n : ℕ} (a : Fin n → A) :
    spatialFreeCreationSum α a + spatialFreeCancellationSum α a =
      ∑ i, spatialTensorOp (α (a i)) (groupLeft (FreeGroup.of (i : ℕ))) := by
  rw [spatialFreeCreationSum, spatialFreeCancellationSum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← spatialTensorOp_add_right, freeTranslation_split]

omit [PartialOrder A] [StarOrderedRing A] in
lemma spatialFreeCreationSum_square {n : ℕ} (a : Fin n → A) :
    star (spatialFreeCreationSum α a) * spatialFreeCreationSum α a =
      spatialLeftHom (K := GroupL2 (FreeGroup ℕ)) α (∑ i, star (a i) * a i) -
        spatialLetterSum α false (fun i => star (a i) * a i) := by
  have hh := CuntzPureness.star_sum_mul_sum_of_orthogonal
    (fun i : Fin n => spatialTensorOp (α (a i)) (freeCreation (i : ℕ))) (by
    intro i j hij
    rw [← spatialTensorOp_star, ← spatialTensorOp_mul,
      freeCreation_orthogonal _ _ (Fin.val_injective.ne hij), spatialTensorOp_zero_right])
  change star (∑ i, spatialTensorOp (α (a i)) (freeCreation (i : ℕ))) *
    (∑ i, spatialTensorOp (α (a i)) (freeCreation (i : ℕ))) = _
  rw [hh]
  simp only [← spatialTensorOp_star, ← spatialTensorOp_mul, ← map_star, ← map_mul,
    freeCreation_star_mul, spatialTensorOp_sub_right, Finset.sum_sub_distrib,
    spatialLetterSum, map_sum]
  rfl

omit [PartialOrder A] [StarOrderedRing A] in
lemma spatialFreeCancellationSum_square {n : ℕ} (a : Fin n → A) :
    spatialFreeCancellationSum α a * star (spatialFreeCancellationSum α a) =
      spatialLeftHom (K := GroupL2 (FreeGroup ℕ)) α (∑ i, a i * star (a i)) -
        spatialLetterSum α true (fun i => a i * star (a i)) := by
  have heq : spatialFreeCancellationSum α a * star (spatialFreeCancellationSum α a) =
      ∑ i, spatialTensorOp (α (a i)) (freeCancellation (i : ℕ)) *
        star (spatialTensorOp (α (a i)) (freeCancellation (i : ℕ))) := by
    have hh := sum_mul_star_sum_of_orthogonal
      (fun i : Fin n => spatialTensorOp (α (a i)) (freeCancellation (i : ℕ))) (by
        intro i j hij
        rw [← spatialTensorOp_star, ← spatialTensorOp_mul,
          freeCancellation_orthogonal _ _ (Fin.val_injective.ne hij), spatialTensorOp_zero_right])
    exact hh
  rw [heq]
  simp only [← spatialTensorOp_star, ← spatialTensorOp_mul, ← map_star, ← map_mul,
    freeCancellation_mul_star, spatialTensorOp_sub_right, Finset.sum_sub_distrib,
    spatialLetterSum, map_sum]
  rfl
end CuntzPureness

end

end OAI
