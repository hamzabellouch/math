import OAI.Probability.InvariantIsing.Cavity.CavityGroupHaarProjection
import OAI.Probability.InvariantIsing.Cavity.CavityGaussianJointTest

namespace OAI

/-! The joint fresh-frame Gaussian limit with converging finite overlap
labels. The same Gaussian marks are retained across all replicas. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavityGroupHaarFrame_labeled_integral_tendsto {m r q : ℕ}
    {L : Type*} [NormedAddCommGroup L] [MeasurableSpace L]
    [BorelSpace L] [SecondCountableTopology L]
    (l : ℕ → L) (l₀ : L) (hl : Tendsto l atTop (𝓝 l₀))
    (N : ℕ → Fin m → ℕ) (hN : ∀ a, Tendsto (fun k => N k a) atTop atTop)
    (v : (k : ℕ) → (a : Fin m) → Fin r → Fin (N k a) → ℝ)
    (Q : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hQ : Tendsto (fun k a i j => (∑ t, v k a i t * v k a j t) / (N k a : ℝ))
      atTop (𝓝 Q))
    (μ : (k : ℕ) → (a : Fin m) → Measure (Orthogonal (N k a)))
    [∀ k a, IsProbabilityMeasure (μ k a)] [∀ k a, (μ k a).IsMulRightInvariant]
    (A₀ : (k : ℕ) → (a : Fin m) → Matrix (Fin (N k a)) (Fin q) ℝ)
    (hA₀ : ∀ k a, (A₀ k a).transpose * A₀ k a = 1)
    (F : L × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →ᵇ ℝ) :
    Tendsto (fun k => ∫ U, F (l k, cavityGroupMatrixProjection (v k)
      (cavityGroupHaarFrames (A₀ k) U)) ∂Measure.pi (μ k)) atTop
      (𝓝 (∫ y, F (l₀, y) ∂multivariateGaussian 0 (cavityGroupReplicaCovariance q Q))) := by
  have hd := cavityGroupFrameProjection_tendsto_of_replicaGram (q := q) N hN v Q hQ
  have ht : TendstoInMeasure (cavityGroupGaussianRows m q) (fun k _ => l k) atTop (fun _ => l₀) :=
    tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const) (ae_of_all _ fun _ => hl)
  have hp := hd.prodMk_of_tendstoInMeasure_const _ _ _ ht (fun _ => aemeasurable_const)
  let G : (EuclideanSpace ℝ (Fin m × (Fin r × Fin q))) × L →ᵇ ℝ :=
    F.compContinuous ⟨Prod.swap, continuous_swap⟩
  have hu := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
    hp.forall_aemeasurable hp.aemeasurable_limit).mp hp G
  apply (show Tendsto (fun k => ∫ x, F (l k, cavityGroupFrameProjection (v k) x)
    ∂cavityGroupGaussianRows m q) atTop _ from hu).congr'
  have hn : ∀ᶠ k in atTop, ∀ a, q ≤ N k a := by
    apply eventually_all.mpr
    intro a
    exact (hN a).eventually (eventually_ge_atTop q)
  filter_upwards [hn] with k hk
  exact cavityGroupFrame_integral_eq_haar (N k) hk (μ k) (A₀ k) (hA₀ k) (v k)
    (F.compContinuous ⟨fun z => (l k, z), continuous_const.prodMk continuous_id⟩)

end InvariantIsing

end

end OAI
