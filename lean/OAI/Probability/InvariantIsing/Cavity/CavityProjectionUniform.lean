import OAI.Probability.InvariantIsing.Cavity.CavityHaarProjection

namespace OAI

/-! The Haar-to-Gaussian replica comparison is uniform over bounded
replica Gram matrices. This is needed when the replicas are sampled
from a disorder-dependent Gibbs probability. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology Matrix BoundedContinuousFunction

namespace InvariantIsing

def cavityReplicaGram {N r : ℕ} (v : Fin r → Fin N → ℝ) :
    Matrix (Fin r) (Fin r) ℝ := fun i j => (∑ k, v i k * v j k) / N

lemma cavityReplicaGram_covariance {N r q : ℕ} (v : Fin r → Fin N → ℝ) :
    cavityReplicaCovariance q (cavityReplicaGram v) =
      cavityProjectionMatrix (q := q) v * (cavityProjectionMatrix (q := q) v).transpose := by
  ext i j
  exact (cavityProjectionMatrix_covariance v i j).symm

theorem cavityHaarFrame_uniform_gaussian {r q : ℕ}
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (μ : (k : ℕ) → Measure (Orthogonal (N k)))
    [∀ k, IsProbabilityMeasure (μ k)] [∀ k, (μ k).IsMulRightInvariant]
    (A₀ : (k : ℕ) → Matrix (Fin (N k)) (Fin q) ℝ)
    (hA₀ : ∀ k, (A₀ k).transpose * A₀ k = 1)
    (F : EuclideanSpace ℝ (Fin r × Fin q) →ᵇ ℝ) (L : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ v : Fin r → Fin (N k) → ℝ,
      (∀ i j, |cavityReplicaGram v i j| ≤ L) →
      |(∫ U, F (cavityMatrixProjection v
          ((U : Matrix (Fin (N k)) (Fin (N k)) ℝ) * A₀ k)) ∂μ k) -
        ∫ y, F y ∂multivariateGaussian 0 (cavityReplicaCovariance q (cavityReplicaGram v))| < ε := by
  classical
  let : FirstCountableTopology (Matrix (Fin r) (Fin r) ℝ) :=
    inferInstanceAs (FirstCountableTopology (Fin r → Fin r → ℝ))
  intro ε hε
  by_contra hbad
  have hbad' : ∃ᶠ k in atTop, ∃ v : Fin r → Fin (N k) → ℝ,
      (∀ i j, |cavityReplicaGram v i j| ≤ L) ∧
      ε ≤ |(∫ U, F (cavityMatrixProjection v
          ((U : Matrix (Fin (N k)) (Fin (N k)) ℝ) * A₀ k)) ∂μ k) -
        ∫ y, F y ∂multivariateGaussian 0 (cavityReplicaCovariance q (cavityReplicaGram v))| := by
    simpa only [Filter.not_eventually, not_forall, not_imp, not_lt, exists_prop] using hbad
  obtain ⟨φ, hφ, hφbad⟩ := extraction_of_frequently_atTop hbad'
  choose v hv he using hφbad
  let Qs : ℕ → Matrix (Fin r) (Fin r) ℝ := fun k => cavityReplicaGram (v k)
  have hmem (k : ℕ) : Qs k ∈ (Icc (-L) L).matrix := by
    intro i j
    exact abs_le.mp (hv k i j)
  obtain ⟨Q, _, ψ, hψ, hlim⟩ := (isCompact_Icc.matrix).tendsto_subseq hmem
  let τ := φ ∘ ψ
  have hτ : StrictMono τ := hφ.comp hψ
  have hsubN : Tendsto (fun k => N (τ k)) atTop atTop := hN.comp hτ.tendsto_atTop
  have hHaar := cavityHaarFrameProjection_integral_tendsto
    (fun k => N (τ k)) hsubN (fun k => v (ψ k)) Q hlim
    (fun k => μ (τ k)) (fun k => A₀ (τ k)) (fun k => hA₀ (τ k)) F
  have hcov := cavityProjection_covariance_tendsto (q := q)
    (fun k => N (τ k)) (fun k => v (ψ k)) Q hlim
  have hp (k : ℕ) : (cavityProjectionMatrix (q := q) (v (ψ k)) *
      (cavityProjectionMatrix (q := q) (v (ψ k))).transpose).PosSemidef := by
    simpa using Matrix.posSemidef_self_mul_conjTranspose (cavityProjectionMatrix (q := q) (v (ψ k)))
  have hQ : (cavityReplicaCovariance q Q).PosSemidef :=
    Matrix.posSemidef_is_closed.mem_of_tendsto hcov (Eventually.of_forall hp)
  have hGaussian := cavity_multivariateGaussian_integral_tendsto
    (fun k => cavityProjectionMatrix (q := q) (v (ψ k)) *
      (cavityProjectionMatrix (q := q) (v (ψ k))).transpose)
    (cavityReplicaCovariance q Q) hp hQ hcov F
  simp_rw [← cavityReplicaGram_covariance] at hGaussian
  have hz := (hHaar.sub hGaussian).abs
  simp only [sub_self, abs_zero] at hz
  have hsmall : ∀ᶠ k in atTop,
      |(∫ U, F (cavityMatrixProjection (v (ψ k))
          ((U : Matrix (Fin (N (τ k))) (Fin (N (τ k))) ℝ) * A₀ (τ k))) ∂μ (τ k)) -
        ∫ y, F y ∂multivariateGaussian 0 (cavityReplicaCovariance q (cavityReplicaGram (v (ψ k))))| < ε := by
    exact hz.eventually (Iio_mem_nhds hε)
  obtain ⟨k, hk⟩ := hsmall.exists
  exact (not_le_of_gt hk) (he (ψ k))

end InvariantIsing

end

end OAI
