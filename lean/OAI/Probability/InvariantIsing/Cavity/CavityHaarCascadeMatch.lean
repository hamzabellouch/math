import OAI.Probability.InvariantIsing.Cavity.CavitySpectralHaarLimit
import OAI.Probability.InvariantIsing.Cavity.CavityRecalculatedGaussian

namespace OAI

/-! The fresh Haar field and the recalculated finite cascade have matching
bounded spectral-group replica tests. The common limit is identified by GG
and the Ward equations, rather than assumed as an auxiliary cascade law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

def cavityGroupBlockOfBlock {m r : ℕ} (x : SpectralBlock (m + 1) r) : SpectralBlock m r :=
  fun i j a => x i j a.castSucc

lemma continuous_cavityGroupBlockOfBlock {m r : ℕ} :
    Continuous (cavityGroupBlockOfBlock (m := m) (r := r)) := by
  unfold cavityGroupBlockOfBlock
  fun_prop

@[simp] lemma cavityGroupBlockOfBlock_view {m r : ℕ} (x : SpectralArray (m + 1)) :
    cavityGroupBlockOfBlock (spectralBlockView (m + 1) r x) = cavitySpectralGroupBlock m r x := rfl

theorem cavity_haar_recalculated_cascade_match {m r q : ℕ}
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
    (pseq : ℕ → OverlapPath)
    (hLp : Tendsto (fun k => ∫ s, |pseq k s - spectralSpinQuantilePath Q₀ hP hn s| ∂pathMeasure)
      atTop (𝓝 0))
    (F : SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →ᵇ ℝ) :
    let p := spectralSpinQuantilePath Q₀ hP hn
    let B := fun p' : OverlapPath => fun x : JointArray =>
      cavitySynchronizedBlock (cavityCanonicalDiagonal ρ eig hρ hρsum p')
        (cavityCanonicalLabel ρ eig hρ hρsum p') (arrayBlock spinArray r x)
    Tendsto (fun k =>
      (∫ x, ∫ U, F (cavitySpectralGroupBlock m r (a k x),
        cavityGroupMatrixProjection (v k x) (cavityGroupHaarFrames (A₀ k) U))
        ∂Measure.pi (μ k) ∂P k) -
      ∫ x, ∫ z, F (B (pseq k) x, z)
        ∂multivariateGaussian 0 (cavityGroupBlockCovariance q ρ (B (pseq k) x))
        ∂(cascadeCompactLaw k (uniformExponent k) (uniformCellAverage p k) : Measure JointArray))
      atTop (𝓝 0) := by
  intro p B
  let F' : SpectralBlock (m + 1) r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →ᵇ ℝ :=
    F.compContinuous ⟨fun z => (cavityGroupBlockOfBlock z.1, z.2),
      (continuous_cavityGroupBlockOfBlock.comp continuous_fst).prodMk continuous_snd⟩
  have hh := cavity_spectral_haar_test_tendsto N hN μ A₀ hA₀ X P a ha hGram v hvM C hv
    ρs ρ hρlim hρs hρ hcov Q Q₀ hQ hlim F'
  have hc := cavity_canonical_marked_group_block_tendsto Q₀ hgg hG d hd0 hd hE hP hn
    ρ eig hρ hρsum hoff hdiag r q F
  have he := cavity_recalculated_gaussian_cascade_error ρ eig hρ hρsum p pseq hLp F
  have hdiff := hh.sub hc
  have hout := hdiff.sub he
  simpa only [F', BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk,
    cavityGroupBlockOfBlock_view, cavityGroupBlockCovariance, cavitySpectralBlockCovariance,
    cavitySpectralGroupBlock, spectralBlockView,
    sub_self, sub_sub_sub_cancel_right, p, B] using hout

end InvariantIsing

end

end OAI
