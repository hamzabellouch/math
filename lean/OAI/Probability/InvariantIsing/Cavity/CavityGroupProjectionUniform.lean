import OAI.Probability.InvariantIsing.Cavity.CavityGroupHaarProjection

namespace OAI

/-! Uniformity over all bounded spectral-group replica Gram arrays. This
allows the fresh frames to be averaged against the base Gibbs measure. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology Matrix BoundedContinuousFunction

namespace InvariantIsing

def cavityGroupReplicaGram {m r : ℕ} {N : Fin m → ℕ}
    (v : (a : Fin m) → Fin r → Fin (N a) → ℝ) :
    Fin m → Matrix (Fin r) (Fin r) ℝ :=
  fun a i j => (∑ k, v a i k * v a j k) / N a

lemma cavityGroupReplicaGram_covariance {m r q : ℕ} {N : Fin m → ℕ}
    (v : (a : Fin m) → Fin r → Fin (N a) → ℝ) :
    cavityGroupReplicaCovariance q (cavityGroupReplicaGram v) =
      cavityGroupProjectionMatrix (q := q) v * (cavityGroupProjectionMatrix (q := q) v).transpose := by
  ext i j
  exact (cavityGroupProjectionMatrix_covariance v i j).symm

theorem cavityGroupHaarFrame_uniform_gaussian {m r q : ℕ}
    (N : ℕ → Fin m → ℕ) (hN : ∀ a, Tendsto (fun k => N k a) atTop atTop)
    (μ : (k : ℕ) → (a : Fin m) → Measure (Orthogonal (N k a)))
    [∀ k a, IsProbabilityMeasure (μ k a)] [∀ k a, (μ k a).IsMulRightInvariant]
    (A₀ : (k : ℕ) → (a : Fin m) → Matrix (Fin (N k a)) (Fin q) ℝ)
    (hA₀ : ∀ k a, (A₀ k a).transpose * A₀ k a = 1)
    (F : EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →ᵇ ℝ) (L : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      ∀ v : (a : Fin m) → Fin r → Fin (N k a) → ℝ,
      (∀ a i j, |cavityGroupReplicaGram v a i j| ≤ L) →
      |(∫ U, F (cavityGroupMatrixProjection v (cavityGroupHaarFrames (A₀ k) U)) ∂Measure.pi (μ k)) -
        ∫ y, F y ∂multivariateGaussian 0 (cavityGroupReplicaCovariance q (cavityGroupReplicaGram v))| < ε := by
  classical
  let : FirstCountableTopology (Fin m → Matrix (Fin r) (Fin r) ℝ) :=
    inferInstanceAs (FirstCountableTopology (Fin m → Fin r → Fin r → ℝ))
  intro ε hε
  by_contra hbad
  have hbad' : ∃ᶠ k in atTop, ∃ v : (a : Fin m) → Fin r → Fin (N k a) → ℝ,
      (∀ a i j, |cavityGroupReplicaGram v a i j| ≤ L) ∧
      ε ≤ |(∫ U, F (cavityGroupMatrixProjection v (cavityGroupHaarFrames (A₀ k) U))
          ∂Measure.pi (μ k)) -
        ∫ y, F y ∂multivariateGaussian 0 (cavityGroupReplicaCovariance q (cavityGroupReplicaGram v))| := by
    simpa only [Filter.not_eventually, not_forall, not_imp, not_lt, exists_prop] using hbad
  obtain ⟨φ, hφ, hφbad⟩ := extraction_of_frequently_atTop hbad'
  choose v hv he using hφbad
  let Qs : ℕ → Fin m → Matrix (Fin r) (Fin r) ℝ := fun k => cavityGroupReplicaGram (v k)
  have hmem (k : ℕ) : Qs k ∈ Set.pi Set.univ (fun _ : Fin m => (Icc (-L) L).matrix) := by
    intro a _ i j
    exact abs_le.mp (hv k a i j)
  obtain ⟨Q, _, ψ, hψ, hlim⟩ :=
    (isCompact_univ_pi (fun _ : Fin m => isCompact_Icc.matrix)).tendsto_subseq hmem
  let τ := φ ∘ ψ
  have hτ : StrictMono τ := hφ.comp hψ
  have hsubN : ∀ a, Tendsto (fun k => N (τ k) a) atTop atTop :=
    fun a => (hN a).comp hτ.tendsto_atTop
  have hHaar := cavityGroupHaarFrameProjection_integral_tendsto
    (fun k => N (τ k)) hsubN (fun k => v (ψ k)) Q hlim
    (fun k => μ (τ k)) (fun k => A₀ (τ k)) (fun k => hA₀ (τ k)) F
  have hcov := cavityGroupProjection_covariance_tendsto (q := q)
    (fun k => N (τ k)) (fun k => v (ψ k)) Q hlim
  have hp (k : ℕ) : (cavityGroupProjectionMatrix (q := q) (v (ψ k)) *
      (cavityGroupProjectionMatrix (q := q) (v (ψ k))).transpose).PosSemidef := by
    simpa using Matrix.posSemidef_self_mul_conjTranspose (cavityGroupProjectionMatrix (q := q) (v (ψ k)))
  have hQ : (cavityGroupReplicaCovariance q Q).PosSemidef :=
    Matrix.posSemidef_is_closed.mem_of_tendsto hcov (Eventually.of_forall hp)
  have hGaussian := cavity_multivariateGaussian_integral_tendsto
    (fun k => cavityGroupProjectionMatrix (q := q) (v (ψ k)) *
      (cavityGroupProjectionMatrix (q := q) (v (ψ k))).transpose)
    (cavityGroupReplicaCovariance q Q) hp hQ hcov F
  simp_rw [← cavityGroupReplicaGram_covariance] at hGaussian
  have hz := (hHaar.sub hGaussian).abs
  simp only [sub_self, abs_zero] at hz
  have hsmall : ∀ᶠ k in atTop,
      |(∫ U, F (cavityGroupMatrixProjection (v (ψ k))
          (cavityGroupHaarFrames (A₀ (τ k)) U)) ∂Measure.pi (μ (τ k))) -
        ∫ y, F y ∂multivariateGaussian 0
          (cavityGroupReplicaCovariance q (cavityGroupReplicaGram (v (ψ k))))| < ε :=
    hz.eventually (Iio_mem_nhds hε)
  obtain ⟨k, hk⟩ := hsmall.exists
  exact (not_le_of_gt hk) (he (ψ k))

end InvariantIsing

end

end OAI
