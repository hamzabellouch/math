import OAI.Probability.SpanningForest.PolynomialGramUpdate

namespace OAI

noncomputable section

open scoped BigOperators Matrix

namespace Problem336.Determinantal

variable {ν ι R : Type*} [finiteRows : Fintype ν] [decidableRows : DecidableEq ν]
variable [Fintype ι] [DecidableEq ι] [CommRing R]

omit [Fintype ι] in

theorem prod_marked_weights (c : ι → R) (T S : Finset ι) (z : R) :
    (∏ e ∈ T, c e * (if e ∈ S then 1 + z else 1)) =
      (∏ e ∈ T, c e) * (1 + z) ^ (T ∩ S).card := by
  rw [Finset.prod_mul_distrib]
  congr 1
  simp only [Finset.prod_ite, Finset.prod_const, Finset.filter_mem_eq_inter,
    one_pow, mul_one]

omit finiteRows decidableRows in
private theorem gram_entry [Fintype ν] [DecidableEq ν] {E : Type*}
    [Fintype E] [DecidableEq E]
    (A : Matrix ν E R) (c : E → R) (i j : ν) :
    (A * Matrix.diagonal c * A.transpose) i j = ∑ e, A i e * c e * A j e := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]

theorem gram_marked_diagonal (A : Matrix ν ι R) (c : ι → R)
    (S : Finset ι) (z : R) :
    A * Matrix.diagonal (fun e => c e * (if e ∈ S then 1 + z else 1)) * A.transpose =
      A * Matrix.diagonal c * A.transpose +
        z • (A.submatrix id (Subtype.val : S → ι) *
          Matrix.diagonal (fun e : S => c e) *
          (A.submatrix id (Subtype.val : S → ι)).transpose) := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, gram_entry,
    Matrix.submatrix_apply, id_eq]
  have hterm (e : ι) : A i e * (c e * (if e ∈ S then 1 + z else 1)) * A j e =
      A i e * c e * A j e + (if e ∈ S then z * (A i e * c e * A j e) else 0) := by
    split_ifs <;> ring
  have hsub : (∑ e : S, A i e * c e * A j e) =
      ∑ e ∈ S, A i e * c e * A j e :=
    Finset.sum_coe_sort S (fun e : ι => A i e * c e * A j e)
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, hsub]
  congr 1
  simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]

theorem det_marked_weighted_gram (A : Matrix ν ι ℝ) (c : ι → ℝ)
    (hA : IsUnit (A * Matrix.diagonal c * A.transpose).det) (S : Finset ι) :
    (A.map Polynomial.C * Matrix.diagonal (fun e =>
      Polynomial.C (c e) * (if e ∈ S then 1 + (Polynomial.X : Polynomial ℝ) else 1)) *
      (A.map Polynomial.C).transpose).det =
      Polynomial.C (A * Matrix.diagonal c * A.transpose).det *
        (1 + (Polynomial.X : Polynomial ℝ) •
          (Matrix.diagonal (fun e : S => c e) *
            ((A.submatrix id (Subtype.val : S → ι)).transpose *
              (A * Matrix.diagonal c * A.transpose)⁻¹ *
              A.submatrix id (Subtype.val : S → ι))).map Polynomial.C).det := by
  have hm := gram_marked_diagonal (A.map Polynomial.C)
    (fun e => Polynomial.C (c e)) S (Polynomial.X : Polynomial ℝ)
  have hm' : A.map Polynomial.C * Matrix.diagonal (fun e =>
      Polynomial.C (c e) * (if e ∈ S then 1 + (Polynomial.X : Polynomial ℝ) else 1)) *
      (A.map Polynomial.C).transpose =
      (A * Matrix.diagonal c * A.transpose).map Polynomial.C +
        (Polynomial.X : Polynomial ℝ) •
          (A.submatrix id (Subtype.val : S → ι) *
            Matrix.diagonal (fun e : S => c e) *
            (A.submatrix id (Subtype.val : S → ι)).transpose).map Polynomial.C := by
    simpa only [Matrix.map_mul, Matrix.diagonal_map (map_zero Polynomial.C),
      Matrix.transpose_map, Matrix.submatrix_map] using hm
  rw [hm']
  exact det_polynomial_weighted_columns _ hA _ _

end Problem336.Determinantal

end

end OAI
