import OAI.Probability.InvariantIsing.Cavity.CavityGroupCovariance
import OAI.Probability.InvariantIsing.Cavity.CavityHaarRank

namespace OAI

/-! The joint Gaussian projection limit for independent Haar frames in
all spectral groups. The exact finite-dimensional law is obtained before
taking limits; no conditional independence is assumed as an extra input. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Topology BoundedContinuousFunction

namespace InvariantIsing

lemma cavityGoodGram_cond_eq (n q : ℕ) (hqn : q ≤ n) :
    cond (cavityGaussianRows q) (cavityGoodGram q n) = cavityGaussianRows q := by
  have hae : ∀ᵐ x ∂cavityGaussianRows q, x ∈ cavityGoodGram q n :=
    (cavityGaussianRows_gram_posDef n q hqn).mono (fun _ hx => hx.det_pos)
  rw [ProbabilityTheory.cond, cavityGoodGram_probability_one n q hqn,
    inv_one, one_smul, Measure.restrict_eq_self_of_ae_mem hae]

lemma cavityGaussianNormalizedFrame_eq_haar {n q : ℕ} (hqn : q ≤ n)
    (μ : Measure (Orthogonal n)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (A₀ : Matrix (Fin n) (Fin q) ℝ) (hA₀ : A₀.transpose * A₀ = 1) :
    (cavityGaussianRows q).map (fun x => cavityNormalizeFrame (cavityGaussianMatrix x n)) =
      μ.map (fun U : Orthogonal n => (U : Matrix (Fin n) (Fin n) ℝ) * A₀) := by
  have hp : stdGaussian (EuclideanSpace ℝ (Fin n × Fin q)) (cavityArrayGood n q) ≠ 0 := by
    rw [cavityArrayGood_probability, cavityGoodGram_probability_one n q hqn]
    exact one_ne_zero
  let := cavityConditionedFrameLaw_probability hp
  rw [← cavityGoodGram_cond_eq n q hqn, cavityConditionedFrameLaw_of_rows]
  exact cavityFrame_eq_haar_orbit μ (cavityConditionedFrameLaw n q)
    cavityConditionedFrameLaw_rotation (cavityConditionedFrameLaw_orthonormal n q) A₀ hA₀

def cavityGroupNormalizedFrames {m q : ℕ} (N : Fin m → ℕ)
    (x : Fin m → ℕ → Fin q → ℝ) : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ :=
  fun a => cavityNormalizeFrame (cavityGaussianMatrix (x a) (N a))

def cavityGroupHaarFrames {m q : ℕ} {N : Fin m → ℕ}
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (U : (a : Fin m) → Orthogonal (N a)) : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ :=
  fun a => (U a : Matrix (Fin (N a)) (Fin (N a)) ℝ) * A₀ a

lemma measurable_cavityGroupNormalizedFrames {m q : ℕ} (N : Fin m → ℕ) :
    Measurable (cavityGroupNormalizedFrames (q := q) N) := by
  exact Measurable.of_eval (fun a => (measurable_cavityGaussianNormalizedFrame q (N a)).comp
    (measurable_pi_apply a))

lemma continuous_cavityGroupHaarFrames {m q : ℕ} {N : Fin m → ℕ}
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ) :
    Continuous (cavityGroupHaarFrames A₀) := by
  apply continuous_pi
  intro a
  change Continuous (fun U : (a : Fin m) → Orthogonal (N a) =>
    (U a : Matrix (Fin (N a)) (Fin (N a)) ℝ) * A₀ a)
  have he : Continuous (fun U : (b : Fin m) → Orthogonal (N b) => U a) := continuous_apply a
  exact (continuous_subtype_val.comp he).matrix_mul continuous_const

lemma measurable_cavityGroupHaarFrames {m q : ℕ} {N : Fin m → ℕ}
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ) :
    Measurable (cavityGroupHaarFrames A₀) := by
  apply Measurable.of_eval
  intro a
  exact (((continuous_cavityFrameAction (N a) q).comp
    (continuous_id.prodMk continuous_const)).measurable).comp (measurable_pi_apply a)

theorem cavityGroupNormalizedFrames_eq_haar {m q : ℕ} (N : Fin m → ℕ)
    (hN : ∀ a, q ≤ N a) (μ : (a : Fin m) → Measure (Orthogonal (N a)))
    [∀ a, IsProbabilityMeasure (μ a)] [∀ a, (μ a).IsMulRightInvariant]
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (hA₀ : ∀ a, (A₀ a).transpose * A₀ a = 1) :
    (cavityGroupGaussianRows m q).map (cavityGroupNormalizedFrames N) =
      (Measure.pi μ).map (cavityGroupHaarFrames A₀) := by
  unfold cavityGroupGaussianRows cavityGroupNormalizedFrames cavityGroupHaarFrames
  rw [Measure.pi_map_pi (fun a => (measurable_cavityGaussianNormalizedFrame q (N a)).aemeasurable),
    Measure.pi_map_pi (μ := μ)
      (f := fun a (U : Orthogonal (N a)) => (U : Matrix (Fin (N a)) (Fin (N a)) ℝ) * A₀ a)
      (fun a => ((continuous_cavityFrameAction (N a) q).comp
        (continuous_id.prodMk continuous_const)).measurable.aemeasurable)]
  congr 1
  funext a
  exact cavityGaussianNormalizedFrame_eq_haar (hN a) (μ a) (A₀ a) (hA₀ a)

def cavityGroupMatrixProjection {m r q : ℕ} {N : Fin m → ℕ}
    (v : (a : Fin m) → Fin r → Fin (N a) → ℝ)
    (A : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ) :
    EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) :=
  WithLp.toLp 2 (fun i => ∑ k, v i.1 i.2.1 k * A i.1 k i.2.2)

lemma continuous_cavityGroupMatrixProjection {m r q : ℕ} {N : Fin m → ℕ}
    (v : (a : Fin m) → Fin r → Fin (N a) → ℝ) :
    Continuous (cavityGroupMatrixProjection (q := q) v) := by
  unfold cavityGroupMatrixProjection
  fun_prop

lemma cavityGroupFrame_integral_eq_haar {m r q : ℕ} (N : Fin m → ℕ)
    (hN : ∀ a, q ≤ N a) (μ : (a : Fin m) → Measure (Orthogonal (N a)))
    [∀ a, IsProbabilityMeasure (μ a)] [∀ a, (μ a).IsMulRightInvariant]
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (hA₀ : ∀ a, (A₀ a).transpose * A₀ a = 1)
    (v : (a : Fin m) → Fin r → Fin (N a) → ℝ)
    (F : EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →ᵇ ℝ) :
    (∫ x, F (cavityGroupFrameProjection v x) ∂cavityGroupGaussianRows m q) =
      ∫ U, F (cavityGroupMatrixProjection v (cavityGroupHaarFrames A₀ U)) ∂Measure.pi μ := by
  let : OpensMeasurableSpace ((a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ) :=
    inferInstanceAs (OpensMeasurableSpace ((a : Fin m) → Fin (N a) → Fin q → ℝ))
  let f := fun A : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ =>
    F (cavityGroupMatrixProjection v A)
  have hf : Continuous f := F.continuous.comp (continuous_cavityGroupMatrixProjection v)
  have he := congrArg (fun ν => ∫ A, f A ∂ν)
    (cavityGroupNormalizedFrames_eq_haar N hN μ A₀ hA₀)
  rw [integral_map (measurable_cavityGroupNormalizedFrames N).aemeasurable hf.aestronglyMeasurable,
    integral_map (measurable_cavityGroupHaarFrames A₀).aemeasurable
      hf.aestronglyMeasurable] at he
  exact he

theorem cavityGroupHaarFrameProjection_integral_tendsto {m r q : ℕ}
    (N : ℕ → Fin m → ℕ) (hN : ∀ a, Tendsto (fun k => N k a) atTop atTop)
    (v : (k : ℕ) → (a : Fin m) → Fin r → Fin (N k a) → ℝ)
    (Q : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hQ : Tendsto (fun k a i j => (∑ l, v k a i l * v k a j l) / (N k a : ℝ))
      atTop (𝓝 Q))
    (μ : (k : ℕ) → (a : Fin m) → Measure (Orthogonal (N k a)))
    [∀ k a, IsProbabilityMeasure (μ k a)] [∀ k a, (μ k a).IsMulRightInvariant]
    (A₀ : (k : ℕ) → (a : Fin m) → Matrix (Fin (N k a)) (Fin q) ℝ)
    (hA₀ : ∀ k a, (A₀ k a).transpose * A₀ k a = 1)
    (F : EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →ᵇ ℝ) :
    Tendsto (fun k => ∫ U, F (cavityGroupMatrixProjection (v k)
      (cavityGroupHaarFrames (A₀ k) U)) ∂Measure.pi (μ k)) atTop
      (𝓝 (∫ y, F y ∂multivariateGaussian 0 (cavityGroupReplicaCovariance q Q))) := by
  have hd := cavityGroupFrameProjection_tendsto_of_replicaGram (q := q) N hN v Q hQ
  have hu := ((tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
    hd.forall_aemeasurable hd.aemeasurable_limit).mp hd) F
  apply (show Tendsto (fun k => ∫ x, F (cavityGroupFrameProjection (v k) x)
    ∂cavityGroupGaussianRows m q) atTop _ from hu).congr'
  have hn : ∀ᶠ k in atTop, ∀ a, q ≤ N k a := by
    apply eventually_all.mpr
    intro a
    exact (hN a).eventually (eventually_ge_atTop q)
  filter_upwards [hn] with k hk
  exact cavityGroupFrame_integral_eq_haar (N k) hk (μ k) (A₀ k) (hA₀ k) (v k) F

end InvariantIsing

end

end OAI
