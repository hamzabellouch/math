import OAI.Probability.InvariantIsing.Cavity.CavityHaarJointTest
import OAI.Probability.InvariantIsing.Cavity.CavityGroupProjectionUniform

namespace OAI

/-! Fresh-frame Gaussian approximation uniformly over compact finite
labels and bounded replica Gram matrices. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology Matrix BoundedContinuousFunction

namespace InvariantIsing

theorem cavityGroupHaarFrame_labeled_uniform {m r q : ℕ}
    {L : Type*} [NormedAddCommGroup L] [MeasurableSpace L]
    [BorelSpace L] [SecondCountableTopology L]
    (K : Set L) (hK : IsCompact K)
    (N : ℕ → Fin m → ℕ) (hN : ∀ a, Tendsto (fun k => N k a) atTop atTop)
    (μ : (k : ℕ) → (a : Fin m) → Measure (Orthogonal (N k a)))
    [∀ k a, IsProbabilityMeasure (μ k a)] [∀ k a, (μ k a).IsMulRightInvariant]
    (A₀ : (k : ℕ) → (a : Fin m) → Matrix (Fin (N k a)) (Fin q) ℝ)
    (hA₀ : ∀ k a, (A₀ k a).transpose * A₀ k a = 1)
    (F : L × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →ᵇ ℝ) (C : ℝ) :
    ∀ ε > 0, ∀ᶠ k in atTop,
      ∀ (v : (a : Fin m) → Fin r → Fin (N k a) → ℝ) (l : L), l ∈ K →
      (∀ a i j, |cavityGroupReplicaGram v a i j| ≤ C) →
      |(∫ U, F (l, cavityGroupMatrixProjection v (cavityGroupHaarFrames (A₀ k) U))
          ∂Measure.pi (μ k)) -
        ∫ y, F (l, y) ∂multivariateGaussian 0
          (cavityGroupReplicaCovariance q (cavityGroupReplicaGram v))| < ε := by
  classical
  let : FirstCountableTopology (Fin m → Matrix (Fin r) (Fin r) ℝ) :=
    inferInstanceAs (FirstCountableTopology (Fin m → Fin r → Fin r → ℝ))
  intro ε hε
  by_contra hbad
  have hf : ∃ᶠ k in atTop, ∃ (v : (a : Fin m) → Fin r → Fin (N k a) → ℝ) (l : L),
      l ∈ K ∧ (∀ a i j, |cavityGroupReplicaGram v a i j| ≤ C) ∧
      ε ≤ |(∫ U, F (l, cavityGroupMatrixProjection v (cavityGroupHaarFrames (A₀ k) U))
          ∂Measure.pi (μ k)) -
        ∫ y, F (l, y) ∂multivariateGaussian 0
          (cavityGroupReplicaCovariance q (cavityGroupReplicaGram v))| := by
    simpa only [Filter.not_eventually, not_forall, not_imp, not_lt, exists_prop] using hbad
  obtain ⟨φ, hφ, hφbad⟩ := extraction_of_frequently_atTop hf
  choose v l hl hv he using hφbad
  let Qs : ℕ → Fin m → Matrix (Fin r) (Fin r) ℝ := fun k => cavityGroupReplicaGram (v k)
  have hmem k : (l k, Qs k) ∈ K ×ˢ Set.pi Set.univ
      (fun _ : Fin m => (Icc (-C) C).matrix) := by
    refine ⟨hl k, fun a _ i j => ?_⟩
    exact abs_le.mp (hv k a i j)
  obtain ⟨p, _, ψ, hψ, hlim⟩ :=
    (hK.prod (isCompact_univ_pi (fun _ : Fin m => isCompact_Icc.matrix))).tendsto_subseq hmem
  let τ := φ ∘ ψ
  have hτ : StrictMono τ := hφ.comp hψ
  have hsubN : ∀ a, Tendsto (fun k => N (τ k) a) atTop atTop :=
    fun a => (hN a).comp hτ.tendsto_atTop
  have hlabel : Tendsto (fun k => l (ψ k)) atTop (𝓝 p.1) :=
    (continuous_fst.tendsto p).comp hlim
  have hgram : Tendsto (fun k => Qs (ψ k)) atTop (𝓝 p.2) :=
    (continuous_snd.tendsto p).comp hlim
  have hHaar := cavityGroupHaarFrame_labeled_integral_tendsto (fun k => l (ψ k)) p.1 hlabel
    (fun k => N (τ k)) hsubN (fun k => v (ψ k)) p.2 hgram
    (fun k => μ (τ k)) (fun k => A₀ (τ k)) (fun k => hA₀ (τ k)) F
  have hcov := cavityGroupProjection_covariance_tendsto (q := q)
    (fun k => N (τ k)) (fun k => v (ψ k)) p.2 hgram
  have hp (k : ℕ) : (cavityGroupProjectionMatrix (q := q) (v (ψ k)) *
      (cavityGroupProjectionMatrix (q := q) (v (ψ k))).transpose).PosSemidef := by
    simpa using Matrix.posSemidef_self_mul_conjTranspose (cavityGroupProjectionMatrix (q := q) (v (ψ k)))
  have hQ : (cavityGroupReplicaCovariance q p.2).PosSemidef :=
    Matrix.posSemidef_is_closed.mem_of_tendsto hcov (Eventually.of_forall hp)
  have hGaussian := cavity_gaussian_joint_test_tendsto (fun k => l (ψ k)) p.1 hlabel
    (fun k => cavityGroupProjectionMatrix (q := q) (v (ψ k)) *
      (cavityGroupProjectionMatrix (q := q) (v (ψ k))).transpose)
    (cavityGroupReplicaCovariance q p.2) hp hQ hcov F
  simp_rw [← cavityGroupReplicaGram_covariance] at hGaussian
  have hz := (hHaar.sub hGaussian).abs
  simp only [sub_self, abs_zero] at hz
  have hsmall := hz.eventually (Iio_mem_nhds hε)
  obtain ⟨k, hk⟩ := hsmall.exists
  exact (not_le_of_gt hk) (he (ψ k))

theorem cavityGroupHaarFrame_labeled_average_error_tendsto {m r q : ℕ}
    {L : Type*} [NormedAddCommGroup L] [MeasurableSpace L]
    [BorelSpace L] [SecondCountableTopology L]
    (K : Set L) (hK : IsCompact K)
    (N : ℕ → Fin m → ℕ) (hN : ∀ a, Tendsto (fun k => N k a) atTop atTop)
    (μ : (k : ℕ) → (a : Fin m) → Measure (Orthogonal (N k a)))
    [∀ k a, IsProbabilityMeasure (μ k a)] [∀ k a, (μ k a).IsMulRightInvariant]
    (A₀ : (k : ℕ) → (a : Fin m) → Matrix (Fin (N k a)) (Fin q) ℝ)
    (hA₀ : ∀ k a, (A₀ k a).transpose * A₀ k a = 1)
    (F : L × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →ᵇ ℝ) (C : ℝ)
    (X : ℕ → Type*) [∀ k, MeasurableSpace (X k)]
    (P : (k : ℕ) → Measure (X k)) [∀ k, IsProbabilityMeasure (P k)]
    (l : (k : ℕ) → X k → L) (hl : ∀ k x, l k x ∈ K)
    (v : (k : ℕ) → X k → (a : Fin m) → Fin r → Fin (N k a) → ℝ)
    (hv : ∀ k x a i j, |cavityGroupReplicaGram (v k x) a i j| ≤ C) :
    Tendsto (fun k => ∫ x, ((∫ U, F (l k x, cavityGroupMatrixProjection (v k x)
        (cavityGroupHaarFrames (A₀ k) U)) ∂Measure.pi (μ k)) -
      ∫ y, F (l k x, y) ∂multivariateGaussian 0
        (cavityGroupReplicaCovariance q (cavityGroupReplicaGram (v k x)))) ∂P k)
      atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hu := cavityGroupHaarFrame_labeled_uniform K hK N hN μ A₀ hA₀ F C (ε / 2) (half_pos hε)
  filter_upwards [hu] with k hk
  rw [Real.dist_eq, sub_zero, ← Real.norm_eq_abs]
  have hb := norm_integral_le_of_norm_le_const (μ := P k) (C := ε / 2)
    (f := fun x => ((∫ U, F (l k x, cavityGroupMatrixProjection (v k x)
        (cavityGroupHaarFrames (A₀ k) U)) ∂Measure.pi (μ k)) -
      ∫ y, F (l k x, y) ∂multivariateGaussian 0
        (cavityGroupReplicaCovariance q (cavityGroupReplicaGram (v k x)))))
    (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]
      exact (hk (v k x) (l k x) (hl k x) (hv k x)).le)
  exact lt_of_le_of_lt (by simpa only [probReal_univ, mul_one] using hb) (half_lt_self hε)

end InvariantIsing

end

end OAI
