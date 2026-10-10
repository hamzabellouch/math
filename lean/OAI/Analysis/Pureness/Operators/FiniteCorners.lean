import OAI.Analysis.Pureness.Cuntz.MatrixTraces
import Mathlib.Analysis.CStarAlgebra.Hom

namespace OAI
namespace CuntzPureness
open scoped ComplexOrder
variable {A : Type*} [CStarAlgebra A]
variable {k l m : ℕ}

noncomputable def corner (_h : k ≤ l) (a : CStarMatrix (Fin k) (Fin k) A) :
    CStarMatrix (Fin l) (Fin l) A :=
  fun i j =>
    if hi : i.val < k then if hj : j.val < k then a ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0 else 0

@[simp] lemma corner_apply_cast (h : k ≤ l) (a : CStarMatrix (Fin k) (Fin k) A)
    (i j : Fin k) : corner h a (Fin.castLE h i) (Fin.castLE h j) = a i j := by
  simp [corner, i.isLt, j.isLt]

lemma corner_row_zero (h : k ≤ l) (a : CStarMatrix (Fin k) (Fin k) A)
    (i j : Fin l) (hi : ¬ i.val < k) : corner h a i j = 0 := by simp [corner, hi]
lemma corner_col_zero (h : k ≤ l) (a : CStarMatrix (Fin k) (Fin k) A)
    (i j : Fin l) (hj : ¬ j.val < k) : corner h a i j = 0 := by simp [corner, hj]

lemma sum_corner_support {G : Type*} [AddCommMonoid G] (h : k ≤ l) (f : Fin l → G)
    (hf : ∀ i, ¬ i.val < k → f i = 0) :
    ∑ i, f i = ∑ i : Fin k, f (Fin.castLE h i) := by
  symm
  apply Fintype.sum_of_injective (Fin.castLE h) (fun i j hij => Fin.ext (congrArg (fun t : Fin l => t.val) hij))
  · intro i hi
    apply hf i
    intro hik
    exact hi ⟨⟨i.val, hik⟩, Fin.ext rfl⟩
  · intro i; rfl

lemma corner_mul (h : k ≤ l) (a b : CStarMatrix (Fin k) (Fin k) A) :
    corner h (a * b) = corner h a * corner h b := by
  ext i j
  by_cases hi : i.val < k
  · by_cases hj : j.val < k
    · rw [CStarMatrix.mul_apply, sum_corner_support h _ (fun t ht => by
        rw [corner_col_zero h a i t ht, zero_mul])]
      simp [corner, hi, hj, CStarMatrix.mul_apply]
    · simp [corner_col_zero h _ _ _ hj, CStarMatrix.mul_apply]
  · simp [corner_row_zero h _ _ _ hi, CStarMatrix.mul_apply]

noncomputable def cornerHom (h : k ≤ l) :
    CStarMatrix (Fin k) (Fin k) A →⋆ₙₐ[ℂ] CStarMatrix (Fin l) (Fin l) A where
  toFun := corner h
  map_zero' := by ext i j; simp [corner]
  map_add' a b := by
    ext i j
    by_cases hi : i.val < k <;> by_cases hj : j.val < k <;> simp [corner, hi, hj]
  map_mul' := corner_mul h
  map_smul' z a := by
    ext i j
    by_cases hi : i.val < k <;> by_cases hj : j.val < k <;> simp [corner, hi, hj]
  map_star' a := by
    ext i j
    simp only [CStarMatrix.star_apply, corner]
    by_cases hi : i.val < k <;> by_cases hj : j.val < k <;> simp [hi, hj]

lemma corner_injective (h : k ≤ l) : Function.Injective (cornerHom (A := A) h) := by
  intro a b hab
  ext i j
  exact (corner_apply_cast h a i j).symm.trans
    ((congrArg (fun M : CStarMatrix (Fin l) (Fin l) A => M (Fin.castLE h i) (Fin.castLE h j)) hab).trans
      (corner_apply_cast h b i j))

variable [PartialOrder A] [StarOrderedRing A]

lemma corner_isometry (h : k ≤ l) : Isometry (cornerHom (A := A) h) :=
  NonUnitalStarAlgHom.isometry _ (corner_injective h)

@[simp] lemma corner_norm (h : k ≤ l) (a : CStarMatrix (Fin k) (Fin k) A) :
    ‖corner h a‖ = ‖a‖ := NonUnitalStarAlgHom.norm_map (cornerHom h) (corner_injective h) a

lemma corner_nonneg (h : k ≤ l) (a : CStarMatrix (Fin k) (Fin k) A) (ha : 0 ≤ a) :
    0 ≤ corner h a := by
  obtain ⟨x, rfl⟩ := positive_square_factor a ha
  change 0 ≤ cornerHom h (star x * x)
  rw [map_mul, map_star]
  exact star_mul_self_nonneg _

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma corner_refl (a : CStarMatrix (Fin k) (Fin k) A) : corner le_rfl a = a := by
  ext i j
  simp [corner, i.isLt, j.isLt]

omit [PartialOrder A] [StarOrderedRing A] in
lemma corner_comp (h : k ≤ l) (g : l ≤ m) (a : CStarMatrix (Fin k) (Fin k) A) :
    corner g (corner h a) = corner (h.trans g) a := by
  ext i j
  by_cases hi : i.val < k <;> by_cases hj : j.val < k
  · simp [corner, hi, hj, hi.trans_le h, hj.trans_le h]
  · simp [corner, hi, hj, hi.trans_le h]
  · simp [corner, hi]
  · simp [corner, hi]

lemma matrixTrace_corner (τ : TracialState A) (h : k ≤ l)
    (a : CStarMatrix (Fin k) (Fin k) A) : matrixTrace τ (corner h a) = matrixTrace τ a := by
  rw [matrixTrace_apply, sum_corner_support h _ (fun i hi => by
    rw [corner_row_zero h a i i hi, map_zero])]
  simp only [corner_apply_cast, matrixTrace_apply]
end CuntzPureness

end OAI
