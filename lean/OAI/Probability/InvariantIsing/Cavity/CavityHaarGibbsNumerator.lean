import OAI.Probability.InvariantIsing.Cavity.CavitySampledBlocks

namespace OAI

/-! The physical fresh-Haar limit for actual Gibbs-kernel numerators.
The original disorder is retained in every sampled spectral array. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_haar_gibbs_numerator_match {m r q dim kspin : ℕ}
    (N : ℕ → Fin m → ℕ) (hN : ∀ a, Tendsto (fun k => N k a) atTop atTop)
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
    (C : ℝ)
    (hv : ∀ k (x : Ω k × (ℕ → X k)) j i l, |cavityGroupReplicaGram (fun j (i : Fin r) => v₀ k x.1 j (x.2 i)) j i l| ≤ C)
    (ρs : ℕ → Fin m → ℝ) (ρ eig : Fin m → ℝ)
    (hρs : ∀ k j, 0 < ρs k j) (hρ : ∀ j, 0 < ρ j)
    (hρlim : Tendsto ρs atTop (𝓝 ρ)) (hρsum : ∑ j, ρ j = 1)
    (hcov : ∀ k (x : Ω k × (ℕ → X k)), cavityGroupReplicaCovariance q (cavityGroupReplicaGram (fun j (i : Fin r) => v₀ k x.1 j (x.2 i))) =
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
    (Cspin : Matrix (Fin kspin) (Fin kspin) ℝ) (T : ℝ)
    (π : Measure (Spin kspin)) [IsProbabilityMeasure π]
    (Fspin : SpectralBlock m r × (Fin r → Spin kspin) →ᵇ ℝ) :
    let p := spectralSpinQuantilePath Q₀ hP hn
    Tendsto (fun k =>
      (∫ ω, ∫ U, cavityWeightNumerator ((ν k ω).prod π)
        (fun x => Real.exp (min (cavityLogFactor K L Cspin
          (cavitySelectedSiteProjection e (v₀ k ω) (cavityGroupHaarFrames (A₀ k) U) x.1) x.2) T))
        (cavityProjectedSpinTest (cavitySampledGroupBlock (B k) ω) Fspin)
        ∂Measure.pi (μ k) ∂P k) -
      ∫ ω, cavityLabeledCappedNumerator k K
        (cavityFiniteCovariancePath ρ eig hρ hρsum g (cavityStrictUniformPath p k)
          (cavityStrictUniformLevels p k) k) L Cspin π T
        (cavityFiniteReplicaSpectralBlock ρ eig hρ hρsum (cavityStrictUniformPath p k)
          (cavityStrictUniformLevels p k)) Fspin ω
        ∂cavityLabeledDisorderLaw k (chainExponent (uniformCut k))
          (cavityFiniteRootCovariance ρ eig hρ hρsum g (cavityStrictUniformPath p k)
            (cavityStrictUniformLevels p k))
          (cavityFiniteNoiseCovariance ρ eig hρ hρsum g (cavityStrictUniformPath p k)
            (uniformCut k) (cavityStrictUniformLevels p k)))
      atTop (𝓝 0) := by
  intro p
  let v := fun k (x : Ω k × (ℕ → X k)) j (i : Fin r) => v₀ k x.1 j (x.2 i)
  have hh := cavity_haar_model_numerator_match N hN μ A₀ hA₀
    (fun k => Ω k × (ℕ → X k)) (fun k => disorderReplicaLaw (P k) (ν k) (hν k))
    (fun k => cavitySampledEntryArray (B k)) (fun k => measurable_cavitySampledEntryArray (B k) (hB k))
    hGram v (fun k => measurable_cavitySampledGroupVectors (v₀ k) (hvM k)) C hv
    ρs ρ eig hρs hρ hρlim hρsum hcov Q Q₀ hQ hlim hgg hG d hd0 hd hE hP hn hoff hdiag
    g e he heg K L Cspin T π Fspin
  have heval k := cavity_haar_spin_numerator_average (P k) (ν k) (hν k) (μ k) (A₀ k)
    (cavitySampledGroupBlock (B k))
    (fun σ => measurable_cavitySampledGroupBlock (B k) (hB k) σ)
    e (v₀ k) (hvM k) K L Cspin T π Fspin
  apply hh.congr'
  filter_upwards [] with k
  congr 1
  exact (heval k).symm

end InvariantIsing

end

end OAI
