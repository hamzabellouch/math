import OAI.Probability.InvariantIsing.Cavity.CavityHaarRestrictedSpinMatch
import OAI.Probability.InvariantIsing.Cavity.CavityFiniteRestrictedModel

namespace OAI

/-! The restricted physical Haar moments converge to the actual
finite labeled Gibbs numerators, including all Gaussian residuals. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_haar_restricted_model_numerator_match {m r q dim kspin : ℕ}
    (N : ℕ → Fin m → ℕ) (hN : ∀ a, Tendsto (fun k => N k a) atTop atTop)
    (μ : (k : ℕ) → (a : Fin m) → Measure (Orthogonal (N k a)))
    [∀ k a, IsProbabilityMeasure (μ k a)] [∀ k a, (μ k a).IsMulRightInvariant]
    (A₀ : (k : ℕ) → (a : Fin m) → Matrix (Fin (N k a)) (Fin q) ℝ)
    (hA₀ : ∀ k a, (A₀ k a).transpose * A₀ k a = 1)
    (X : ℕ → Type*) [∀ k, MeasurableSpace (X k)]
    (P : (k : ℕ) → Measure (X k)) [∀ k, IsProbabilityMeasure (P k)]
    (a : (k : ℕ) → X k → SpectralArray (m + 1)) (ha : ∀ k, Measurable (a k))
    (hGram : ∀ k x, SpectralGram (a k x))
    (v : (k : ℕ) → X k → (j : Fin m) → Fin r → Fin (N k j) → ℝ)
    (hvM : ∀ k, Measurable (v k)) (C : ℝ)
    (hv : ∀ k x j i l, |cavityGroupReplicaGram (v k x) j i l| ≤ C)
    (ρs : ℕ → Fin m → ℝ) (ρ eig : Fin m → ℝ)
    (hρs : ∀ k j, 0 < ρs k j) (hρ : ∀ j, 0 < ρ j)
    (hρlim : Tendsto ρs atTop (𝓝 ρ)) (hρsum : ∑ j, ρ j = 1)
    (hcov : ∀ k x, cavityGroupReplicaCovariance q (cavityGroupReplicaGram (v k x)) =
      cavitySpectralBlockCovariance q (ρs k) (spectralBlockView (m + 1) r (a k x)))
    (Q : ℕ → ProbabilityMeasure (SpectralArray (m + 1)))
    (Q₀ : ProbabilityMeasure (SpectralArray (m + 1)))
    (hQ : ∀ k, (Q k : Measure (SpectralArray (m + 1))) = (P k).map (a k))
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
    (Fspin : SpectralBlock m r × (Fin r → Spin kspin) →ᵇ ℝ)
    {Bcut : ℝ} (hBcut : 0 ≤ Bcut)
    (hnull : (cavityBlockMarkedLaw (q := q) Q₀ ρ (cavitySpectralGroupBlock m r) : Measure
      (SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q))))
      {z | cavityReplicaRadius (cavitySelectedGroupProjection e) z = Bcut} = 0) :
    let F := cavityRestrictedSpinReplicaValue K L Cspin T Bcut (cavitySelectedGroupProjection e) π Fspin
    let p := spectralSpinQuantilePath Q₀ hP hn
    Tendsto (fun k =>
      (∫ x, ∫ U, F (cavitySpectralGroupBlock m r (a k x),
        cavityGroupMatrixProjection (v k x) (cavityGroupHaarFrames (A₀ k) U))
        ∂Measure.pi (μ k) ∂P k) -
      ∫ ω, cavityLabeledRestrictedNumerator k K
        (cavityFiniteCovariancePath ρ eig hρ hρsum g (cavityStrictUniformPath p k)
          (cavityStrictUniformLevels p k) k) L Cspin π T Bcut
        (cavityFiniteReplicaSpectralBlock ρ eig hρ hρsum (cavityStrictUniformPath p k)
          (cavityStrictUniformLevels p k)) Fspin ω
        ∂cavityLabeledDisorderLaw k (chainExponent (uniformCut k))
          (cavityFiniteRootCovariance ρ eig hρ hρsum g (cavityStrictUniformPath p k)
            (cavityStrictUniformLevels p k))
          (cavityFiniteNoiseCovariance ρ eig hρ hρsum g (cavityStrictUniformPath p k)
            (uniformCut k) (cavityStrictUniformLevels p k)))
      atTop (𝓝 0) := by
  intro F p
  have hh := cavity_haar_strict_restricted_spin_match N hN μ A₀ hA₀ X P a ha hGram v hvM C hv
    ρs ρ eig hρs hρ hρlim hρsum hcov Q Q₀ hQ hlim hgg hG d hd0 hd hE hP hn hoff hdiag
    K L Cspin T hBcut (cavitySelectedGroupProjection e) π Fspin hnull
  dsimp only at hh
  have heval (k : ℕ) := cavity_finite_restricted_model_numerator ρ eig hρ hρsum g e he heg
    (cavityStrictUniformPath p k) (uniformCut k) (uniformCut_strict k)
    (uniformCut_zero k) (uniformCut_last k) (cavityStrictUniformLevels p k)
    (cavityStrictUniformLevels_strict p k)
    (fun i s hs => cavityStrictUniformPath_on_cell p k i hs)
    (cavityStrictUniformLevels_mem p k (Fin.last k)).2
    (chainExponent (uniformCut k)) K L Cspin T hBcut π Fspin
  apply hh.congr'
  filter_upwards [] with k
  congr 1
  exact (cavityStrictMarkedLaw_integral ρ eig hρ hρsum p k _
    (measurable_cavityRestrictedSpinReplicaValue K L Cspin T hBcut
      (cavitySelectedGroupProjection e) π Fspin)
    (cavityRestrictedSpinReplicaValue_bound K L Cspin T hBcut
      (cavitySelectedGroupProjection e) π Fspin)).trans (heval k)

end InvariantIsing

end

end OAI
