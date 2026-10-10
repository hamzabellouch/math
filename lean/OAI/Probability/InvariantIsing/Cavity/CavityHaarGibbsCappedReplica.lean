import OAI.Probability.InvariantIsing.Cavity.CavityHaarGibbsNumerator
import OAI.Probability.InvariantIsing.Cavity.CavityFiniteCappedComparison
import OAI.Probability.InvariantIsing.Cavity.CavityHaarSpinNumerator

namespace OAI

/-! The normalized fresh-Haar Gibbs comparison, with all ordinary-moment
and strict finite-approximation assumptions proved for the actual models. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_haar_gibbs_capped_replica_match {m r q dim kspin : ℕ}
    (N : ℕ → Fin m → ℕ) (hN : ∀ a, Tendsto (fun k => N k a) atTop atTop)
    (hNpos : ∀ k a, 0 < N k a)
    (μ : (k : ℕ) → (a : Fin m) → Measure (Orthogonal (N k a)))
    [∀ k a, IsProbabilityMeasure (μ k a)] [∀ k a, (μ k a).IsMulRightInvariant]
    (A₀ : (k : ℕ) → (a : Fin m) → Matrix (Fin (N k a)) (Fin q) ℝ)
    (hA₀ : ∀ k a, (A₀ k a).transpose * A₀ k a = 1)
    (Ω X : ℕ → Type*) [∀ k, MeasurableSpace (Ω k)] [∀ k, MeasurableSpace (X k)]
    [∀ k, Countable (X k)] [∀ k, MeasurableSingletonClass (X k)]
    (P : (k : ℕ) → Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (ν : (k : ℕ) → Ω k → Measure (X k)) (hν : ∀ k, Measurable (ν k))
    [∀ k ω, IsProbabilityMeasure (ν k ω)]
    (B : (k : ℕ) → Ω k → X k → X k → SpectralEntry (m + 1))
    (hB : ∀ k x y, Measurable (fun ω => B k ω x y))
    (hGram : ∀ k x, SpectralGram (cavitySampledEntryArray (B k) x))
    (v₀ : (k : ℕ) → Ω k → (j : Fin m) → X k → Fin (N k j) → ℝ)
    (hvM : ∀ k x, Measurable (fun ω j => v₀ k ω j x))
    (C : ℝ) (hC : 0 ≤ C)
    (hv : ∀ r k (x : Ω k × (ℕ → X k)) j i l, |cavityGroupReplicaGram (fun j (i : Fin r) => v₀ k x.1 j (x.2 i)) j i l| ≤ C)
    (ρs : ℕ → Fin m → ℝ) (ρ eig : Fin m → ℝ)
    (hρs : ∀ k j, 0 < ρs k j) (hρ : ∀ j, 0 < ρ j)
    (hρlim : Tendsto ρs atTop (𝓝 ρ)) (hρsum : ∑ j, ρ j = 1)
    (hcov : ∀ r k (x : Ω k × (ℕ → X k)), cavityGroupReplicaCovariance q (cavityGroupReplicaGram (fun j (i : Fin r) => v₀ k x.1 j (x.2 i))) =
      cavitySpectralBlockCovariance q (ρs k) (spectralBlockView (m + 1) r (cavitySampledEntryArray (B k) x)))
    (Q : ℕ → ProbabilityMeasure (SpectralArray (m + 1)))
    (Q₀ : ProbabilityMeasure (SpectralArray (m + 1)))
    (hQ : ∀ k, (Q k : Measure (SpectralArray (m + 1))) = (disorderReplicaLaw (P k) (ν k) (hν k)).map (cavitySampledEntryArray (B k)))
    (hlim : Tendsto Q atTop (𝓝 Q₀))
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q₀ : Measure (SpectralArray (m + 1))))
    (hG : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), SpectralGram x)
    (d : Fin (m + 1) → ℝ) (hd0 : ∀ j, 0 ≤ d j)
    (hd : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), ∀ i j, (x (i,i) j : ℝ) = d j)
    (hE : ∀ e : ℕ → ℕ, Function.Injective e →
      (Q₀ : Measure (SpectralArray (m + 1))).map (permuteSpectralArray e) = Q₀)
    (hP : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), ∀ j, 0 ≤ (x (0,1) j : ℝ))
    (hoff : ∀ j l, ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ B : ℝ, 0 ≤ B → (∀ t, |Φ t| ≤ B) →
      spectralOffWardResidual Q₀ ρ eig j l Φ = 0)
    (hdiag : ∀ j l, spectralDiagonalWardResidual Q₀ ρ eig j l = 0)
    (g : Fin dim → Fin m) (e : Fin dim → Fin m × Fin q)
    (he : Function.Injective e) (heg : ∀ j, (e j).1 = g j)
    (K : Matrix (Fin dim) (Fin dim) ℝ) (L : Matrix (Fin dim) (Fin kspin) ℝ)
    (Cspin : Matrix (Fin kspin) (Fin kspin) ℝ) (T : ℝ) (hT : 0 ≤ T)
    (π : Measure (Spin kspin)) [IsProbabilityMeasure π]
    (Fspin : SpectralBlock m r × (Fin r → Spin kspin) →ᵇ ℝ) :
    let p := spectralSpinQuantilePath Q₀ hP hn
    Tendsto (fun k =>
      (∫ ω, ∫ U, cavityWeightedReplicaMean ((ν k ω).prod π)
        (fun x => Real.exp (min (cavityLogFactor K L Cspin
          (cavitySelectedSiteProjection e (v₀ k ω) (cavityGroupHaarFrames (A₀ k) U) x.1) x.2) T))
        (cavityProjectedSpinTest (cavitySampledGroupBlock (B k) ω) Fspin)
        ∂Measure.pi (μ k) ∂P k) -
      ∫ ω, cavityWeightedReplicaMean
        (cavityLabeledPriorKernel k
          (cavityFiniteCovariancePath ρ eig hρ hρsum g (cavityStrictUniformPath p k)
            (cavityStrictUniformLevels p k) k) π ω)
        (fun x => Real.exp (min (cavityLabeledPotential k K L Cspin (ω,x)) T))
        (fun σ => cavityLabeledReplicaTest
          (cavityFiniteReplicaSpectralBlock ρ eig hρ hρsum (cavityStrictUniformPath p k)
            (cavityStrictUniformLevels p k)) Fspin (ω,σ))
        ∂cavityLabeledDisorderLaw k (chainExponent (uniformCut k))
          (cavityFiniteRootCovariance ρ eig hρ hρsum g (cavityStrictUniformPath p k)
            (cavityStrictUniformLevels p k))
          (cavityFiniteNoiseCovariance ρ eig hρ hρsum g (cavityStrictUniformPath p k)
            (uniformCut k) (cavityStrictUniformLevels p k)))
      atTop (𝓝 0) := by
  intro p
  let B' := fun k ω x y (a : Fin m) => B k ω x y a.castSucc
  have hB' k x y : Measurable (fun ω => B' k ω x y) :=
    Measurable.of_eval fun a => (measurable_pi_apply a.castSucc).comp (hB k x y)
  have hnorm k ω x : ∀ a, ‖(WithLp.toLp 2 (v₀ k ω a x) :
      EuclideanSpace ℝ (Fin (N k a)))‖^2 ≤ C * N k a :=
    cavity_group_gram_diagonal_norm (hNpos k) (fun a => v₀ k ω a x)
      (fun a => hv 1 k (ω,fun _ => x) a 0 0)
  have hcomp := cavity_finite_capped_spin_comparison N hNpos μ Ω X P ν hν e v₀ hvM
    A₀ hA₀ hC hnorm B' hB' ρ eig hρ hρsum g p K L Cspin π T hT Fspin
  have hraw (j : ℕ) := cavity_haar_gibbs_numerator_match (r := r+j)
    N hN μ A₀ hA₀ Ω X P ν hν B hB hGram v₀ hvM C (hv (r+j))
    ρs ρ eig hρs hρ hρlim hρsum (hcov (r+j)) Q Q₀ hQ hlim hgg hG d hd0 hd hE hP hn
    hoff hdiag g e he heg K L Cspin T π (cavityReplicaPrefixTest j Fspin)
  have hnum (j k : ℕ) := cavity_haar_spin_numerator_integral (P k) (ν k) (hν k)
    (μ k) e (v₀ k) (hvM k) (A₀ k) (fun ω σ i l => B' k ω (σ i) (σ l))
    (fun σ => Measurable.of_eval fun i => Measurable.of_eval fun l => hB' k (σ i) (σ l))
    K L Cspin π T (cavityReplicaPrefixTest j Fspin)
  have hcap := hcomp (fun j => by
    apply (hraw j).congr'
    filter_upwards [] with k
    rw [← hnum j k]
    rfl)
  have hint k := cavity_haar_spin_replica_integral (P k) (ν k) (hν k) (μ k) e
    (v₀ k) (hvM k) (A₀ k) (fun ω σ i l => B' k ω (σ i) (σ l))
    (fun σ => Measurable.of_eval fun i => Measurable.of_eval fun l => hB' k (σ i) (σ l))
    K L Cspin π T Fspin
  apply hcap.congr'
  filter_upwards [] with k
  rw [← hint k]
  rfl

end InvariantIsing

end

end OAI
