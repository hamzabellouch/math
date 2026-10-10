import OAI.Probability.InvariantIsing.Cavity.CavityStrictMarkedLimit
import OAI.Probability.InvariantIsing.Cavity.CavityRestrictedSpinLimit

namespace OAI

/-! The hard-restricted physical Haar spin moments match the strict
finite Gaussian cavity moments. The cutoff is taken at a common
continuity radius of the limiting marked law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_haar_strict_restricted_spin_match {m r q : ℕ}
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

    {dim kspin : ℕ}
    (K : Matrix (Fin dim) (Fin dim) ℝ) (L : Matrix (Fin dim) (Fin kspin) ℝ)
    (Cspin : Matrix (Fin kspin) (Fin kspin) ℝ) (T : ℝ) {B : ℝ} (hB : 0 ≤ B)
    (J : EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →L[ℝ]
      (Fin r → EuclideanSpace ℝ (Fin dim)))
    (π : Measure (Spin kspin)) [IsProbabilityMeasure π]
    (F : SpectralBlock m r × (Fin r → Spin kspin) →ᵇ ℝ)
    (hnull : (cavityBlockMarkedLaw (q := q) Q₀ ρ (cavitySpectralGroupBlock m r) : Measure
      (SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q))))
      {z | cavityReplicaRadius J z = B} = 0) :
    let p := spectralSpinQuantilePath Q₀ hP hn
    Tendsto (fun k =>
      (∫ x, ∫ U, cavityRestrictedSpinReplicaValue K L Cspin T B J π F
        (cavitySpectralGroupBlock m r (a k x),
          cavityGroupMatrixProjection (v k x) (cavityGroupHaarFrames (A₀ k) U))
          ∂Measure.pi (μ k) ∂P k) -
      ∫ z, cavityRestrictedSpinReplicaValue K L Cspin T B J π F z
        ∂(cavityStrictMarkedLaw (r := r) (q := q) ρ eig hρ hρsum p k : Measure
          (SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)))))
      atTop (𝓝 0) := by
  intro p
  have hH := cavity_spectral_haar_marked_law_tendsto N hN μ A₀ hA₀ X P a ha hGram
    v hvM C hv ρs ρ hρlim hρs hρ hcov Q Q₀ hQ hlim
  have hS := cavity_strict_marked_law_tendsto N hN μ A₀ hA₀ X P a ha hGram v hvM C hv
    ρs ρ eig hρs hρ hρlim hρsum hcov Q Q₀ hQ hlim hgg hG d hd0 hd hE hP hn hoff hdiag
  have hHR := cavity_restricted_spin_replica_tendsto _ _ hH K L Cspin T hB J π F hnull
  have hSR := cavity_restricted_spin_replica_tendsto _ _ hS K L Cspin T hB J π F hnull
  have hout := hHR.sub hSR
  simp only [sub_self] at hout
  simp_rw [cavityHaarMarkedLaw_integral _ _ _ _ _ _ _ _
    (measurable_cavityRestrictedSpinReplicaValue K L Cspin T hB J π F)
    (cavityRestrictedSpinReplicaValue_bound K L Cspin T hB J π F)] at hout
  exact hout

end InvariantIsing

end

end OAI
