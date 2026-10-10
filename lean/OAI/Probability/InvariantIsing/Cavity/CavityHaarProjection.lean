import OAI.Probability.InvariantIsing.Cavity.CavityConditionedFrame
import OAI.Probability.InvariantIsing.Cavity.CavityFrameHaar
import OAI.Probability.InvariantIsing.Cavity.CavityConditionedProjection

namespace OAI

/-! Gaussian replica projections for genuine Haar-distributed orthonormal
frames, obtained from the conditioned Gaussian construction. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Topology BoundedContinuousFunction

namespace InvariantIsing

lemma cavityFrame_integral_eq_haar {n q : ℕ}
    (hp : 0 < (cavityGaussianRows q).real (cavityGoodGram q n))
    (μ : Measure (Orthogonal n)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (A₀ : Matrix (Fin n) (Fin q) ℝ) (hA₀ : A₀.transpose * A₀ = 1)
    (f : Matrix (Fin n) (Fin q) ℝ → ℝ) (hf : Continuous f) :
    (∫ x, f (cavityNormalizeFrame (cavityGaussianMatrix x n))
      ∂cond (cavityGaussianRows q) (cavityGoodGram q n)) =
      ∫ U, f ((U : Matrix (Fin n) (Fin n) ℝ) * A₀) ∂μ := by
  have hp' : stdGaussian (EuclideanSpace ℝ (Fin n × Fin q)) (cavityArrayGood n q) ≠ 0 := by
    rw [cavityArrayGood_probability]
    exact fun h => by simp [Measure.real, h] at hp
  let := cavityConditionedFrameLaw_probability hp'
  have hlaw := cavityFrame_eq_haar_orbit μ (cavityConditionedFrameLaw n q)
    cavityConditionedFrameLaw_rotation (cavityConditionedFrameLaw_orthonormal n q) A₀ hA₀
  have hnorm : Measurable (fun x : ℕ → Fin q → ℝ =>
      cavityNormalizeFrame (cavityGaussianMatrix x n)) := by
    apply (measurable_cavityNormalizeFrame n q).comp
    apply Measurable.of_eval_matrix
    intro i j
    exact ((measurable_pi_apply j).comp (measurable_pi_apply (i : ℕ))).div_const _
  rw [← integral_map hnorm.aemeasurable hf.aestronglyMeasurable,
    cavityConditionedFrameLaw_of_rows, hlaw]
  exact integral_map
    ((continuous_cavityFrameAction n q).comp (continuous_id.prodMk continuous_const)).aemeasurable
    hf.aestronglyMeasurable

def cavityMatrixProjection {n r q : ℕ} (v : Fin r → Fin n → ℝ)
    (A : Matrix (Fin n) (Fin q) ℝ) : EuclideanSpace ℝ (Fin r × Fin q) :=
  WithLp.toLp 2 (fun a => ∑ i, v a.1 i * A i a.2)

lemma continuous_cavityMatrixProjection {n r q : ℕ} (v : Fin r → Fin n → ℝ) :
    Continuous (cavityMatrixProjection (q := q) v) := by
  unfold cavityMatrixProjection
  fun_prop

theorem cavityHaarFrameProjection_integral_tendsto {r q : ℕ}
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (v : (k : ℕ) → Fin r → Fin (N k) → ℝ)
    (Q : Matrix (Fin r) (Fin r) ℝ)
    (hQ : Tendsto (fun k i j => (∑ l, v k i l * v k j l) / (N k : ℝ))
      atTop (𝓝 Q))
    (μ : (k : ℕ) → Measure (Orthogonal (N k)))
    [∀ k, IsProbabilityMeasure (μ k)] [∀ k, (μ k).IsMulRightInvariant]
    (A₀ : (k : ℕ) → Matrix (Fin (N k)) (Fin q) ℝ)
    (hA₀ : ∀ k, (A₀ k).transpose * A₀ k = 1)
    (F : EuclideanSpace ℝ (Fin r × Fin q) →ᵇ ℝ) :
    Tendsto (fun k => ∫ U, F (cavityMatrixProjection (v k)
      ((U : Matrix (Fin (N k)) (Fin (N k)) ℝ) * A₀ k)) ∂μ k) atTop
      (𝓝 (∫ y, F y ∂multivariateGaussian 0 (cavityReplicaCovariance q Q))) := by
  apply (cavityConditionedFrameProjection_integral_tendsto N hN v Q hQ F).congr'
  filter_upwards [hN.eventually (cavityGoodGram_eventually_positive q)] with k hk
  exact cavityFrame_integral_eq_haar hk (μ k) (A₀ k) (hA₀ k)
    (fun A => F (cavityMatrixProjection (v k) A))
    (F.continuous.comp (continuous_cavityMatrixProjection (v k)))

end InvariantIsing

end

end OAI
