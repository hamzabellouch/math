import Mathlib

namespace OAI

/-! # Finite Toeplitz rows compressed by an almost central projection

These are the quantitative estimates in the projection-splitting step for a
finite row of canonical O∞ isometries. In addition to almost centrality, a
coisometric compression needs small compression of the original vacuum
projection. No projection with these properties is assumed to exist here.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E I : Type*} [CStarAlgebra E] [Fintype I] [DecidableEq I]

/-- Compression in the ambient algebra, with relative unit `q`. -/
def toeplitzRowCompression (q : E) (s : I → E) (i : I) : E := q * s i * q

/-- The defect of the finite isometry row before compression. -/
def toeplitzRowVacuum (s : I → E) : E := 1 - ∑ i, s i * star (s i)

private lemma compression_projection_norm (q : E) (hq : q * q = q)
    (hqs : star q = q) : ‖q‖ ≤ 1 :=
  IsStarProjection.norm_le q (isStarProjection_iff'.mpr ⟨hq, hqs⟩)

private lemma compression_contract_mul_left (q x : E) (hq : ‖q‖ ≤ 1) :
    ‖q * x‖ ≤ ‖x‖ :=
  (norm_mul_le q x).trans (mul_le_of_le_one_left (norm_nonneg x) hq)

private lemma compression_contract_mul_right (q x : E) (hq : ‖q‖ ≤ 1) :
    ‖x * q‖ ≤ ‖x‖ :=
  (norm_mul_le x q).trans (mul_le_of_le_one_right (norm_nonneg x) hq)

/-- The adjoint has the same commutator error. -/
lemma toeplitz_star_commutator_norm (q x : E) (hqs : star q = q) :
    ‖q * star x - star x * q‖ = ‖q * x - x * q‖ := by
  have h : q * star x - star x * q = -star (q * x - x * q) := by
    rw [star_sub, star_mul, star_mul, hqs]
    abel
  rw [h, norm_neg, norm_star]

omit [Fintype I] in
/-- Exact defect formula for the compressed Gram matrix. -/
lemma toeplitzRowCompression_gram (q : E) (s : I → E)
    (hq : q * q = q) (hqs : star q = q)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (i j : I) :
    star (toeplitzRowCompression q s i) * toeplitzRowCompression q s j -
        (if i = j then q else 0) =
      q * star (s i) * (q * s j - s j * q) * q := by
  have hij : q * (star (s i) * s j) * q = if i = j then q else 0 := by
    rw [hs]
    split_ifs
    · simpa only [mul_one] using hq
    · simp only [mul_zero, zero_mul]
  rw [← hij]
  simp only [toeplitzRowCompression, star_mul, hqs]
  noncomm_ring
  simp only [← mul_assoc q q, hq]

omit [Fintype I] in
/-- Every Gram entry is controlled by one generator commutator. -/
lemma toeplitzRowCompression_gram_bound (q : E) (s : I → E)
    (hq : q * q = q) (hqs : star q = q)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (hns : ∀ i, ‖s i‖ ≤ 1) (δ : ℝ)
    (hcomm : ∀ i, ‖q * s i - s i * q‖ ≤ δ) (i j : I) :
    ‖star (toeplitzRowCompression q s i) * toeplitzRowCompression q s j -
        (if i = j then q else 0)‖ ≤ δ := by
  rw [toeplitzRowCompression_gram q s hq hqs hs]
  have hnq := compression_projection_norm q hq hqs
  calc
    _ ≤ ‖q * star (s i) * (q * s j - s j * q)‖ :=
      compression_contract_mul_right _ _ hnq
    _ ≤ ‖star (s i) * (q * s j - s j * q)‖ := by
      rw [mul_assoc]
      exact compression_contract_mul_left _ _ hnq
    _ ≤ ‖q * s j - s j * q‖ :=
      compression_contract_mul_left _ _ (by simpa only [norm_star] using hns i)
    _ ≤ δ := hcomm j

omit [DecidableEq I] in
/-- The coisometry defect contains the compressed original vacuum explicitly. -/
lemma toeplitzRowCompression_coisometry (q : E) (s : I → E)
    (hq : q * q = q) (hqs : star q = q) :
    (∑ i, toeplitzRowCompression q s i * star (toeplitzRowCompression q s i)) - q =
      (∑ i, q * s i * (q * star (s i) - star (s i) * q) * q) -
        q * toeplitzRowVacuum s * q := by
  have hterm (i : I) :
      toeplitzRowCompression q s i * star (toeplitzRowCompression q s i) =
        q * s i * (q * star (s i) - star (s i) * q) * q +
          q * (s i * star (s i)) * q := by
    simp only [toeplitzRowCompression, star_mul, hqs]
    noncomm_ring
    simp only [← mul_assoc q q, hq]
    abel
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  unfold toeplitzRowVacuum
  rw [mul_sub, sub_mul, mul_one, hq, Finset.mul_sum, Finset.sum_mul]
  abel

omit [DecidableEq I] in
/-- Approximate centrality and small vacuum compression give the finite
coisometry estimate used before perturbing a Toeplitz row to a Cuntz row. -/
lemma toeplitzRowCompression_coisometry_bound (q : E) (s : I → E)
    (hq : q * q = q) (hqs : star q = q) (hns : ∀ i, ‖s i‖ ≤ 1)
    (δ : ℝ) (hcomm : ∀ i, ‖q * s i - s i * q‖ ≤ δ) :
    ‖(∑ i, toeplitzRowCompression q s i * star (toeplitzRowCompression q s i)) - q‖ ≤
      (Fintype.card I : ℝ) * δ + ‖q * toeplitzRowVacuum s * q‖ := by
  rw [toeplitzRowCompression_coisometry q s hq hqs]
  apply (norm_sub_le _ _).trans
  apply add_le_add _ le_rfl
  calc
    _ ≤ ∑ i, ‖q * s i * (q * star (s i) - star (s i) * q) * q‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i : I, δ := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ ‖q * s i * (q * star (s i) - star (s i) * q)‖ :=
          compression_contract_mul_right _ _ (compression_projection_norm q hq hqs)
        _ ≤ ‖s i * (q * star (s i) - star (s i) * q)‖ := by
          rw [mul_assoc]
          exact compression_contract_mul_left _ _ (compression_projection_norm q hq hqs)
        _ ≤ ‖q * star (s i) - star (s i) * q‖ :=
          compression_contract_mul_left _ _ (hns i)
        _ = ‖q * s i - s i * q‖ := toeplitz_star_commutator_norm q (s i) hqs
        _ ≤ δ := hcomm i
    _ = (Fintype.card I : ℝ) * δ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The two relative compressions recover each generator up to twice its
commutator error. No smallness is asserted for either complementary projection. -/
lemma toeplitz_complementary_compression_bound (q x : E)
    (hq : q * q = q) (hqs : star q = q) :
    ‖q * x * q + (1 - q) * x * (1 - q) - x‖ ≤ 2 * ‖q * x - x * q‖ := by
  have hnq := compression_projection_norm q hq hqs
  have hnp : ‖1 - q‖ ≤ 1 := compression_projection_norm (1 - q)
    (by noncomm_ring [hq]) (by rw [star_sub, star_one, hqs])
  have he : q * x * q + (1 - q) * x * (1 - q) - x =
      (q * x - x * q) * q - (q * x - x * q) * (1 - q) := by
    noncomm_ring [hq]
  rw [he]
  calc
    _ ≤ ‖(q * x - x * q) * q‖ + ‖(q * x - x * q) * (1 - q)‖ := norm_sub_le _ _
    _ ≤ ‖q * x - x * q‖ + ‖q * x - x * q‖ :=
      add_le_add (compression_contract_mul_right _ _ hnq) (compression_contract_mul_right _ _ hnp)
    _ = 2 * ‖q * x - x * q‖ := by ring

end WeakPureInfiniteness

end

end OAI
