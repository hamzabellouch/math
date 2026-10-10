import OAI.Probability.InvariantIsing.Cavity.CavityMultivariateGaussian

namespace OAI

/-! The ordinary, exponent-zero Gaussian expectation at the common
root of the quadratic cavity recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_gaussian_eval_memLp {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) :
    MemLp (fun z : EuclideanSpace ℝ (Fin d) => z i) 2 (multivariateGaussian 0 S) := by
  simpa only [EuclideanSpace.coe_proj, id_eq] using (IsGaussian.memLp_two_id :
    MemLp id 2 (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S)).continuousLinearMap_comp
      (EuclideanSpace.proj (𝕜 := ℝ) i)

lemma cavity_gaussian_eval_integral {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) :
    (∫ z : EuclideanSpace ℝ (Fin d), z i ∂multivariateGaussian 0 S) = 0 := by
  have h := (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm
    (IsGaussian.integrable_id : Integrable id (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S))
  simpa only [id_eq, EuclideanSpace.coe_proj, integral_id_multivariateGaussian, map_zero] using h

lemma cavity_gaussian_eval_mul_integral {d : ℕ}
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef) (i j : Fin d) :
    (∫ z : EuclideanSpace ℝ (Fin d), z i * z j ∂multivariateGaussian 0 S) = S i j := by
  have h := covariance_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ (Fin d))) hS i j
  rw [covariance_eq_sub (cavity_gaussian_eval_memLp S i) (cavity_gaussian_eval_memLp S j),
    cavity_gaussian_eval_integral, cavity_gaussian_eval_integral, zero_mul, sub_zero] at h
  exact h

lemma cavity_quadratic_as_sum {d : ℕ} (K : Matrix (Fin d) (Fin d) ℝ)
    (z : EuclideanSpace ℝ (Fin d)) :
    ⟪z, Matrix.toEuclideanCLM (𝕜 := ℝ) K z⟫ =
      ∑ i, ∑ j, K i j * (z i * z j) := by
  rw [Matrix.inner_toEuclideanCLM]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem cavity_gaussian_root_integrable {d : ℕ} (K S : Matrix (Fin d) (Fin d) ℝ) :
    Integrable (fun z : EuclideanSpace ℝ (Fin d) =>
      ⟪z, Matrix.toEuclideanCLM (𝕜 := ℝ) K z⟫ / 2) (multivariateGaussian 0 S) := by
  simp_rw [cavity_quadratic_as_sum]
  apply Integrable.div_const
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  exact ((cavity_gaussian_eval_memLp S i).integrable_mul
    (cavity_gaussian_eval_memLp S j)).const_mul _

theorem cavity_gaussian_root_integral {d : ℕ}
    (K S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef) :
    (∫ z : EuclideanSpace ℝ (Fin d),
      ⟪z, Matrix.toEuclideanCLM (𝕜 := ℝ) K z⟫ / 2 ∂multivariateGaussian 0 S) =
      (S * K).trace / 2 := by
  have hij (i j : Fin d) : Integrable (fun z : EuclideanSpace ℝ (Fin d) =>
      K i j * (z i * z j)) (multivariateGaussian 0 S) :=
    ((cavity_gaussian_eval_memLp S i).integrable_mul
      (cavity_gaussian_eval_memLp S j)).const_mul _
  simp_rw [cavity_quadratic_as_sum]
  rw [integral_div]
  congr 1
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hij i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hij _ j), integral_const_mul,
    cavity_gaussian_eval_mul_integral S hS]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hs : S j i = S i j := congrFun (congrFun
    (Matrix.isHermitian_iff_isSymm.mp hS.isHermitian) i) j
  rw [hs]

end InvariantIsing

end

end OAI
