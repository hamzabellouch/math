import OAI.Probability.InvariantIsing.Cavity.CavityProjectionUniform

namespace OAI

/-! The uniform frame approximation may be averaged against any finite
Gibbs probability independent of the fresh frame. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix BoundedContinuousFunction

namespace InvariantIsing

theorem cavityGibbsProjection_error_tendsto {r q : ℕ}
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (μ : (k : ℕ) → Measure (Orthogonal (N k)))
    [∀ k, IsProbabilityMeasure (μ k)] [∀ k, (μ k).IsMulRightInvariant]
    (A₀ : (k : ℕ) → Matrix (Fin (N k)) (Fin q) ℝ)
    (hA₀ : ∀ k, (A₀ k).transpose * A₀ k = 1)
    (X : ℕ → Type*) [∀ k, Fintype (X k)]
    (w : (k : ℕ) → X k → ℝ) (hw : ∀ k x, 0 ≤ w k x)
    (hsum : ∀ k, ∑ x, w k x = 1)
    (v : (k : ℕ) → X k → Fin r → Fin (N k) → ℝ)
    (F : EuclideanSpace ℝ (Fin r × Fin q) →ᵇ ℝ) (L : ℝ)
    (hGram : ∀ k x i j, |cavityReplicaGram (v k x) i j| ≤ L) :
    Tendsto (fun k => ∑ x, w k x *
      ((∫ U, F (cavityMatrixProjection (v k x)
          ((U : Matrix (Fin (N k)) (Fin (N k)) ℝ) * A₀ k)) ∂μ k) -
        ∫ y, F y ∂multivariateGaussian 0 (cavityReplicaCovariance q (cavityReplicaGram (v k x)))))
      atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hh := cavityHaarFrame_uniform_gaussian N hN μ A₀ hA₀ F L (ε / 2) (half_pos hε)
  filter_upwards [hh] with k hk
  rw [Real.dist_eq, sub_zero]
  apply lt_of_le_of_lt _ (show ε / 2 < ε by linarith)
  calc
    _ ≤ ∑ x, |w k x *
        ((∫ U, F (cavityMatrixProjection (v k x)
            ((U : Matrix (Fin (N k)) (Fin (N k)) ℝ) * A₀ k)) ∂μ k) -
          ∫ y, F y ∂multivariateGaussian 0 (cavityReplicaCovariance q (cavityReplicaGram (v k x))))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, w k x * (ε / 2) := by
      apply Finset.sum_le_sum
      intro x _
      rw [abs_mul, abs_of_nonneg (hw k x)]
      exact mul_le_mul_of_nonneg_left (hk (v k x) (hGram k x)).le (hw k x)
    _ = ε / 2 := by rw [← Finset.sum_mul, hsum, one_mul]

end InvariantIsing

end

end OAI
