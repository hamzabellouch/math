import OAI.Probability.InvariantIsing.Cavity.CavityGroupProjectionUniform

namespace OAI

/-! The joint fresh-frame approximation is uniform under finite base
Gibbs averages, including averages of finitely many replicas. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix BoundedContinuousFunction

namespace InvariantIsing

theorem cavityGroupGibbsProjection_error_tendsto {m r q : ℕ}
    (N : ℕ → Fin m → ℕ) (hN : ∀ a, Tendsto (fun k => N k a) atTop atTop)
    (μ : (k : ℕ) → (a : Fin m) → Measure (Orthogonal (N k a)))
    [∀ k a, IsProbabilityMeasure (μ k a)] [∀ k a, (μ k a).IsMulRightInvariant]
    (A₀ : (k : ℕ) → (a : Fin m) → Matrix (Fin (N k a)) (Fin q) ℝ)
    (hA₀ : ∀ k a, (A₀ k a).transpose * A₀ k a = 1)
    (X : ℕ → Type*) [∀ k, Fintype (X k)]
    (w : (k : ℕ) → X k → ℝ) (hw : ∀ k x, 0 ≤ w k x)
    (hsum : ∀ k, ∑ x, w k x = 1)
    (v : (k : ℕ) → X k → (a : Fin m) → Fin r → Fin (N k a) → ℝ)
    (F : EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →ᵇ ℝ) (L : ℝ)
    (hGram : ∀ k x a i j, |cavityGroupReplicaGram (v k x) a i j| ≤ L) :
    Tendsto (fun k => ∑ x, w k x *
      ((∫ U, F (cavityGroupMatrixProjection (v k x)
          (cavityGroupHaarFrames (A₀ k) U)) ∂Measure.pi (μ k)) -
        ∫ y, F y ∂multivariateGaussian 0
          (cavityGroupReplicaCovariance q (cavityGroupReplicaGram (v k x)))))
      atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hh := cavityGroupHaarFrame_uniform_gaussian N hN μ A₀ hA₀ F L (ε / 2) (half_pos hε)
  filter_upwards [hh] with k hk
  rw [Real.dist_eq, sub_zero]
  apply lt_of_le_of_lt _ (show ε / 2 < ε by linarith)
  calc
    _ ≤ ∑ x, |w k x *
        ((∫ U, F (cavityGroupMatrixProjection (v k x)
            (cavityGroupHaarFrames (A₀ k) U)) ∂Measure.pi (μ k)) -
          ∫ y, F y ∂multivariateGaussian 0
            (cavityGroupReplicaCovariance q (cavityGroupReplicaGram (v k x))))| :=
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
