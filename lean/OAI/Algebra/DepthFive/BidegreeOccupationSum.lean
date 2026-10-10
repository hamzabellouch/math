import OAI.Algebra.DepthFive.ExponentCardinality

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem335

variable {σ : Type*} [Fintype σ] (isV : σ → Bool) (a b : ℕ)

@[simp] theorem bidegreeExponentsEquiv_fst_apply
    (d : {d : σ →₀ ℕ // Finsupp.weight (bidegreeWeight isV) d = (a, b)})
    (i : {i // isV i = true}) :
    (bidegreeExponentsEquiv isV a b d).1.1 i = d.1 i := rfl

@[simp] theorem bidegreeExponentsEquiv_snd_apply
    (d : {d : σ →₀ ℕ // Finsupp.weight (bidegreeWeight isV) d = (a, b)})
    (i : {i // ¬ isV i = true}) :
    (bidegreeExponentsEquiv isV a b d).2.1 i = d.1 i := rfl

@[simp] theorem bidegreeExponentsEquiv_symm_true
    (p : {d : {i // isV i = true} → ℕ // ∑ i, d i = a} ×
      {d : {i // ¬ isV i = true} → ℕ // ∑ i, d i = b})
    (i : {i // isV i = true}) :
    ((bidegreeExponentsEquiv isV a b).symm p).1 i = p.1.1 i := by
  simpa using (bidegreeExponentsEquiv_fst_apply isV a b
    ((bidegreeExponentsEquiv isV a b).symm p) i).symm

@[simp] theorem bidegreeExponentsEquiv_symm_false
    (p : {d : {i // isV i = true} → ℕ // ∑ i, d i = a} ×
      {d : {i // ¬ isV i = true} → ℕ // ∑ i, d i = b})
    (i : {i // ¬ isV i = true}) :
    ((bidegreeExponentsEquiv isV a b).symm p).1 i = p.2.1 i := by
  simpa using (bidegreeExponentsEquiv_snd_apply isV a b
    ((bidegreeExponentsEquiv isV a b).symm p) i).symm

variable
  [Fintype {d : σ →₀ ℕ // Finsupp.weight (bidegreeWeight isV) d = (a, b)}]
  [Fintype {d : {i // isV i = true} → ℕ // ∑ i, d i = a}]
  [Fintype {d : {i // ¬ isV i = true} → ℕ // ∑ i, d i = b}]

/-- Uniform bidegree exponents split into the independent uniform occupation
vectors of the differentiated and multiplied coordinate sets. -/
theorem sum_bidegree_occupation_products
    (s : Finset {i // isV i = true}) (t : Finset {i // ¬ isV i = true}) :
    (∑ d : {d : σ →₀ ℕ // Finsupp.weight (bidegreeWeight isV) d = (a, b)},
      (∏ i ∈ s, (d.1 i : ℝ)) * (∏ i ∈ t, ((d.1 i : ℝ) + 1))) =
    (∑ d : {d : {i // isV i = true} → ℕ // ∑ i, d i = a},
      ∏ i ∈ s, (d.1 i : ℝ)) *
    (∑ d : {d : {i // ¬ isV i = true} → ℕ // ∑ i, d i = b},
      ∏ i ∈ t, ((d.1 i : ℝ) + 1)) := by
  classical
  rw [← (bidegreeExponentsEquiv isV a b).symm.sum_comp
    (fun d => (∏ i ∈ s, (d.1 i : ℝ)) * (∏ i ∈ t, ((d.1 i : ℝ) + 1)))]
  simp only [bidegreeExponentsEquiv_symm_true, bidegreeExponentsEquiv_symm_false,
    Fintype.sum_prod_type]
  rw [Finset.sum_mul_sum]

/-- The corresponding normalized-average identity. It remains valid for empty
index sets because both sides use the field convention for division by zero. -/
theorem mean_bidegree_occupation_products
    (s : Finset {i // isV i = true}) (t : Finset {i // ¬ isV i = true}) :
    (∑ d : {d : σ →₀ ℕ // Finsupp.weight (bidegreeWeight isV) d = (a, b)},
      (∏ i ∈ s, (d.1 i : ℝ)) * (∏ i ∈ t, ((d.1 i : ℝ) + 1))) /
      Fintype.card {d : σ →₀ ℕ // Finsupp.weight (bidegreeWeight isV) d = (a, b)} =
    ((∑ d : {d : {i // isV i = true} → ℕ // ∑ i, d i = a},
      ∏ i ∈ s, (d.1 i : ℝ)) /
      Fintype.card {d : {i // isV i = true} → ℕ // ∑ i, d i = a}) *
    ((∑ d : {d : {i // ¬ isV i = true} → ℕ // ∑ i, d i = b},
      ∏ i ∈ t, ((d.1 i : ℝ) + 1)) /
      Fintype.card {d : {i // ¬ isV i = true} → ℕ // ∑ i, d i = b}) := by
  rw [sum_bidegree_occupation_products, Fintype.card_congr (bidegreeExponentsEquiv isV a b),
    Fintype.card_prod, Nat.cast_mul]
  exact (div_mul_div_comm _ _ _ _).symm

end Problem335

end

end OAI
