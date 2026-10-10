import OAI.Analysis.IrrationalRotation.Model.FiniteConvolution
import OAI.Analysis.IrrationalRotation.Operators.FiniteConvolutionAlgebra

namespace OAI

namespace InvariantProjection.FiniteConvolution

@[simp] theorem polynomial_coeff {K : ℕ} (a : Coefficients K)
    (i : Fin (2 * K + 1)) : (polynomial a).coeff (i : ℕ) = a i := by
  classical
  simp [polynomial, Polynomial.coeff_monomial,
    Fin.val_inj]

theorem continuous_lowProduct (K : ℕ) :
    Continuous (fun p : Coefficients K × Coefficients K => lowProduct p.1 p.2) := by
  classical
  apply continuous_pi
  intro n
  simp only [lowProduct, polynomial, Finset.sum_mul, Finset.mul_sum,
    Polynomial.finsetSum_coeff, Polynomial.monomial_mul_monomial]
  apply continuous_finsetSum
  intro i hi
  apply continuous_finsetSum
  intro j hj
  simp only [Polynomial.coeff_monomial]
  split_ifs <;> fun_prop

theorem uniform_lower_bound (K : ℕ) (D δ : ℝ) (hδ : 0 < δ) :
    ∃ ε > 0, ∀ a b : Coefficients K,
      (∀ i, ‖a i‖ ≤ D) → (∀ i, ‖b i‖ ≤ D) →
      δ ≤ ‖a (center K)‖ → δ ≤ ‖b (center K)‖ →
      ∃ n : Fin (2 * K + 1), ε ≤ ‖lowProduct a b n‖ := by
  classical
  let S : Set (Coefficients K) :=
    Metric.closedBall 0 D ∩ {a | δ ≤ ‖a (center K)‖}
  have hS : IsCompact S :=
    (isCompact_closedBall (0 : Coefficients K) D).inter_right
      (isClosed_le continuous_const (continuous_apply (center K)).norm)
  have hpositive : ∀ p ∈ S ×ˢ S, 0 < ‖lowProduct p.1 p.2‖ := by
    intro p hp
    apply norm_pos_iff.mpr
    have ha : (polynomial p.1).coeff K ≠ 0 := by
      change (polynomial p.1).coeff ((center K) : ℕ) ≠ 0
      rw [polynomial_coeff]
      exact norm_pos_iff.mp (lt_of_lt_of_le hδ hp.1.2)
    have hb : (polynomial p.2).coeff K ≠ 0 := by
      change (polynomial p.2).coeff ((center K) : ℕ) ≠ 0
      rw [polynomial_coeff]
      exact norm_pos_iff.mp (lt_of_lt_of_le hδ hp.2.2)
    obtain ⟨n, hn, hne⟩ :=
      InvariantProjection.exists_nonzero_product_coeff_le_two_mul
        (polynomial p.1) (polynomial p.2) K ha hb
    intro hz
    apply hne
    have he := congrFun hz (⟨n, by omega⟩ : Fin (2 * K + 1))
    simpa only [lowProduct, Pi.zero_apply] using he
  obtain ⟨ε, hε, hbound⟩ := (hS.prod hS).exists_forall_le'
    (continuous_lowProduct K).norm.continuousOn hpositive
  refine ⟨ε, hε, ?_⟩
  intro a b ha hb hca hcb
  have haS : a ∈ S := by
    refine ⟨?_, hca⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      ((pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans (ha (center K)))).mpr ha)
  have hbS : b ∈ S := by
    refine ⟨?_, hcb⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      ((pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans (hb (center K)))).mpr hb)
  have hnorm := hbound (a, b) ⟨haS, hbS⟩
  by_contra h
  push Not at h
  exact (not_lt_of_ge hnorm) ((pi_norm_lt_iff hε).mpr h)

end InvariantProjection.FiniteConvolution

end OAI
