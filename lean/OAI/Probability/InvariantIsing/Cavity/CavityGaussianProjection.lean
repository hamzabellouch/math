import OAI.Probability.InvariantIsing.Cavity.CavityGaussianImage

namespace OAI

/-! The exact Gaussian law before orthonormalization. Different fresh
axes are independent; replica covariance is the normalized Gram matrix
of the projected replica vectors. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

namespace InvariantIsing

def cavityProjectionMatrix {n r q : ℕ} (v : Fin r → Fin n → ℝ) :
    Matrix (Fin r × Fin q) (Fin n × Fin q) ℝ :=
  fun a b => if a.2 = b.2 then v a.1 b.1 / Real.sqrt n else 0

lemma cavityProjectionMatrix_covariance {n r q : ℕ}
    (v : Fin r → Fin n → ℝ) (a b : Fin r × Fin q) :
    (cavityProjectionMatrix (q := q) v * (cavityProjectionMatrix (q := q) v).transpose) a b =
      if a.2 = b.2 then (∑ k, v a.1 k * v b.1 k) / (n : ℝ) else 0 := by
  classical
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  have hs (k : Fin n) :
      (∑ j : Fin q, cavityProjectionMatrix (q := q) v a (k, j) *
        (cavityProjectionMatrix (q := q) v).transpose (k, j) b) =
      if a.2 = b.2 then v a.1 k * v b.1 k / (n : ℝ) else 0 := by
    by_cases hab : a.2 = b.2
    · simp only [cavityProjectionMatrix, Matrix.transpose_apply]
      rw [hab]
      simp only [ite_mul_ite, mul_zero, ite_true, div_mul_div_comm,
        Real.mul_self_sqrt (Nat.cast_nonneg n)]
      simp
    · have hz (j : Fin q) : cavityProjectionMatrix (q := q) v a (k, j) *
          (cavityProjectionMatrix (q := q) v).transpose (k, j) b = 0 := by
        by_cases haj : a.2 = j
        · have hbj : b.2 ≠ j := fun h => hab (haj.trans h.symm)
          simp [cavityProjectionMatrix, Matrix.transpose_apply, haj, hbj]
        · simp [cavityProjectionMatrix, Matrix.transpose_apply, haj]
      simp only [hz, Finset.sum_const_zero, ite_eq_right hab]
  simp_rw [hs]
  split_ifs <;> simp [Finset.sum_div]

def cavityRawProjection {n r q : ℕ} (v : Fin r → Fin n → ℝ)
    (x : ℕ → Fin q → ℝ) : EuclideanSpace ℝ (Fin r × Fin q) :=
  (cavityProjectionMatrix (q := q) v).toEuclideanLin
    (WithLp.toLp 2 (fun p : Fin n × Fin q => x p.1 p.2))

lemma cavityRawProjection_apply {n r q : ℕ} (v : Fin r → Fin n → ℝ)
    (x : ℕ → Fin q → ℝ) (a : Fin r × Fin q) :
    cavityRawProjection v x a =
      ∑ k : Fin n, v a.1 k * cavityGaussianMatrix x n k a.2 := by
  classical
  change (∑ b : Fin n × Fin q, cavityProjectionMatrix (q := q) v a b * x b.1 b.2) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _
  simp only [cavityProjectionMatrix, ite_mul, zero_mul]
  simp [cavityGaussianMatrix, div_mul_eq_mul_div, mul_div_assoc]

theorem cavityRawProjection_hasLaw {n r q : ℕ} (v : Fin r → Fin n → ℝ) :
    HasLaw (cavityRawProjection (q := q) v)
      (multivariateGaussian 0
        (cavityProjectionMatrix (q := q) v * (cavityProjectionMatrix (q := q) v).transpose))
      (cavityGaussianRows q) := by
  have hL : HasLaw (cavityProjectionMatrix (q := q) v).toEuclideanLin.toContinuousLinearMap
      (multivariateGaussian 0
        (cavityProjectionMatrix (q := q) v * (cavityProjectionMatrix (q := q) v).transpose))
      (stdGaussian (EuclideanSpace ℝ (Fin n × Fin q))) :=
    ⟨(by fun_prop), cavity_standardGaussian_image _⟩
  exact hL.fun_comp (cavityGaussianRows_finite_standard_law n q)

end InvariantIsing

end

end OAI
