import OAI.Analysis.Pureness.Completion.CompletedOrthogonalSeries

namespace OAI
noncomputable section
namespace CuntzPureness
open Filter Topology
open scoped ComplexOrder ENNReal NNReal CStarAlgebra
variable {A : Type*} [CStarAlgebra A]

def offsetMatrix (o : ℕ) {k l : ℕ} (_h : o + k ≤ l) (a : MatrixStage A k) : MatrixStage A l :=
  fun i j => if hi : o ≤ i.val ∧ i.val < o + k then
    if hj : o ≤ j.val ∧ j.val < o + k then a ⟨i.val - o, by omega⟩ ⟨j.val - o, by omega⟩ else 0 else 0

def offsetIndex (o : ℕ) {k l : ℕ} (h : o + k ≤ l) (i : Fin k) : Fin l :=
  ⟨o + i.val, by omega⟩

lemma offsetIndex_injective (o : ℕ) {k l : ℕ} (h : o + k ≤ l) : Function.Injective (offsetIndex o h) := by
  intro i j hij
  apply Fin.ext
  have he := congrArg Fin.val hij
  dsimp [offsetIndex] at he
  omega

@[simp] lemma offsetMatrix_apply_index (o : ℕ) {k l : ℕ} (h : o + k ≤ l) (a : MatrixStage A k) (i j : Fin k) :
    offsetMatrix o h a (offsetIndex o h i) (offsetIndex o h j) = a i j := by
  simp [offsetMatrix, offsetIndex, i.isLt, j.isLt]

lemma offsetMatrix_row_zero (o : ℕ) {k l : ℕ} (h : o + k ≤ l) (a : MatrixStage A k)
    (i j : Fin l) (hi : ¬ (o ≤ i.val ∧ i.val < o + k)) : offsetMatrix o h a i j = 0 := by
  simp [offsetMatrix, hi]

lemma offsetMatrix_col_zero (o : ℕ) {k l : ℕ} (h : o + k ≤ l) (a : MatrixStage A k)
    (i j : Fin l) (hj : ¬ (o ≤ j.val ∧ j.val < o + k)) : offsetMatrix o h a i j = 0 := by
  simp [offsetMatrix, hj]

lemma sum_offset_support {G : Type*} [AddCommMonoid G] (o : ℕ) {k l : ℕ}
    (h : o + k ≤ l) (f : Fin l → G) (hf : ∀ i, ¬ (o ≤ i.val ∧ i.val < o + k) → f i = 0) :
    ∑ i, f i = ∑ i : Fin k, f (offsetIndex o h i) := by
  symm
  apply Fintype.sum_of_injective (offsetIndex o h) (offsetIndex_injective o h)
  · intro i hi
    apply hf i
    intro hik
    apply hi
    refine ⟨⟨i.val - o, by omega⟩, ?_⟩
    apply Fin.ext
    dsimp [offsetIndex]
    omega
  · intro i; rfl

lemma offsetMatrix_mul (o : ℕ) {k l : ℕ} (h : o + k ≤ l) (a b : MatrixStage A k) :
    offsetMatrix o h (a * b) = offsetMatrix o h a * offsetMatrix o h b := by
  ext i j
  by_cases hi : o ≤ i.val ∧ i.val < o + k
  · by_cases hj : o ≤ j.val ∧ j.val < o + k
    · rw [CStarMatrix.mul_apply, sum_offset_support o h _ (fun t ht => by
        rw [offsetMatrix_col_zero o h a i t ht, zero_mul])]
      simp [offsetMatrix, offsetIndex, hi, hj, CStarMatrix.mul_apply]
    · simp [offsetMatrix_col_zero o h _ _ _ hj, CStarMatrix.mul_apply]
  · simp [offsetMatrix_row_zero o h _ _ _ hi, CStarMatrix.mul_apply]

def offsetMatrixHom (o : ℕ) {k l : ℕ} (h : o + k ≤ l) : MatrixStage A k →⋆ₙₐ[ℂ] MatrixStage A l where
  toFun := offsetMatrix o h
  map_zero' := by ext i j; simp [offsetMatrix]
  map_add' a b := by
    ext i j
    by_cases hi : o ≤ i.val ∧ i.val < o + k <;> by_cases hj : o ≤ j.val ∧ j.val < o + k <;>
      simp [offsetMatrix, hi, hj]
  map_mul' := offsetMatrix_mul o h
  map_smul' z a := by
    ext i j
    by_cases hi : o ≤ i.val ∧ i.val < o + k <;> by_cases hj : o ≤ j.val ∧ j.val < o + k <;>
      simp [offsetMatrix, hi, hj]
  map_star' a := by
    ext i j
    simp only [CStarMatrix.star_apply, offsetMatrix]
    by_cases hi : o ≤ i.val ∧ i.val < o + k <;> by_cases hj : o ≤ j.val ∧ j.val < o + k <;>
      simp [hi, hj]

lemma offsetMatrixHom_injective (o : ℕ) {k l : ℕ} (h : o + k ≤ l) :
    Function.Injective (offsetMatrixHom (A := A) o h) := by
  intro a b hab
  ext i j
  have he := congrArg (fun M : MatrixStage A l => M (offsetIndex o h i) (offsetIndex o h j)) hab
  simpa only [offsetMatrixHom, NonUnitalStarAlgHom.coe_mk, offsetMatrix_apply_index] using he

lemma offsetMatrix_norm [PartialOrder A] [StarOrderedRing A]
    (o : ℕ) {k l : ℕ} (h : o + k ≤ l) (a : MatrixStage A k) :
    ‖offsetMatrix o h a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map (offsetMatrixHom o h) (offsetMatrixHom_injective o h) a

lemma matrixTrace_offset [PartialOrder A] [StarOrderedRing A] (τ : TracialState A)
    (o : ℕ) {k l : ℕ} (h : o + k ≤ l) (a : MatrixStage A k) :
    matrixTrace τ (offsetMatrix o h a) = matrixTrace τ a := by
  rw [matrixTrace_apply, sum_offset_support o h _ (fun i hi => by
    rw [offsetMatrix_row_zero o h a i i hi, map_zero])]
  simp only [offsetMatrix_apply_index, matrixTrace_apply]

lemma corner_offsetMatrix (o : ℕ) {k l m : ℕ} (h : o + k ≤ l) (g : l ≤ m) (a : MatrixStage A k) :
    corner g (offsetMatrix o h a) = offsetMatrix o (h.trans g) a := by
  ext i j
  by_cases hi : i.val < l <;> by_cases hj : j.val < l
  · simp [corner, offsetMatrix, hi, hj]
  · have hx : ¬ (o ≤ j.val ∧ j.val < o + k) := by omega
    simp [corner, offsetMatrix, hj, hx]
  · have hx : ¬ (o ≤ i.val ∧ i.val < o + k) := by omega
    simp [corner, offsetMatrix, hi, hx]
  · have hx : ¬ (o ≤ i.val ∧ i.val < o + k) := by omega
    simp [corner, offsetMatrix, hi, hx]

lemma offsetMatrix_disjoint (o p : ℕ) {k m l : ℕ} (h : o + k ≤ l) (g : p + m ≤ l)
    (hg : o + k ≤ p) (a : MatrixStage A k) (b : MatrixStage A m) :
    offsetMatrix o h a * offsetMatrix p g b = 0 := by
  ext i j
  rw [CStarMatrix.mul_apply]
  apply Finset.sum_eq_zero
  intro t _
  by_cases ht : o ≤ t.val ∧ t.val < o + k
  · rw [offsetMatrix_row_zero p g b t j (by omega), mul_zero]
  · rw [offsetMatrix_col_zero o h a i t ht, zero_mul]
end CuntzPureness

end

end OAI
