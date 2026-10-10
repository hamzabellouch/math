import OAI.Probability.InvariantIsing.Cavity.CavitySpectralHaarLimit
import OAI.Probability.InvariantIsing.Cavity.CavityHaarMarkedLaw
import OAI.Probability.InvariantIsing.Cavity.CavityBlockMarkedLaw
import OAI.Probability.InvariantIsing.Cavity.CavityHaarCascadeMatch

namespace OAI

/-! The physical spectral replica law with its fresh Haar coordinates
converges as a probability law, before any radius restriction. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_spectral_haar_marked_law_tendsto {m r q : ℕ}
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
    (ρs : ℕ → Fin m → ℝ) (ρ : Fin m → ℝ)
    (hρ : Tendsto ρs atTop (𝓝 ρ)) (hρs : ∀ k j, 0 < ρs k j) (hρ0 : ∀ j, 0 < ρ j)
    (hcov : ∀ k x, cavityGroupReplicaCovariance q (cavityGroupReplicaGram (v k x)) =
      cavitySpectralBlockCovariance q (ρs k) (spectralBlockView (m + 1) r (a k x)))
    (Q : ℕ → ProbabilityMeasure (SpectralArray (m + 1)))
    (Q₀ : ProbabilityMeasure (SpectralArray (m + 1)))
    (hQ : ∀ k, (Q k : Measure (SpectralArray (m + 1))) = (P k).map (a k))
    (hlim : Tendsto Q atTop (𝓝 Q₀))
 :
    Tendsto (fun k => cavityHaarMarkedLaw (P k) (μ k)
      (fun x => cavitySpectralGroupBlock m r (a k x))
      ((continuous_cavitySpectralGroupBlock m r).measurable.comp (ha k))
      (v k) (hvM k) (A₀ k)) atTop
      (𝓝 (cavityBlockMarkedLaw (q := q) Q₀ ρ (cavitySpectralGroupBlock m r))) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro F
  simp_rw [cavityHaarMarkedLaw_integral _ _ _ _ _ _ _ _ F.continuous.measurable
    (fun x => F.norm_coe_le_norm x),
    cavityBlockMarkedLaw_integral _ _ _ (continuous_cavitySpectralGroupBlock m r).measurable
      _ F.continuous.measurable (fun x => F.norm_coe_le_norm x)]
  let F' : SpectralBlock (m+1) r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →ᵇ ℝ :=
    F.compContinuous ⟨fun z => (cavityGroupBlockOfBlock z.1,z.2),
      (continuous_cavityGroupBlockOfBlock.comp continuous_fst).prodMk continuous_snd⟩
  have ht := cavity_spectral_haar_test_tendsto N hN μ A₀ hA₀ X P a ha hGram v hvM C hv
    ρs ρ hρ hρs hρ0 hcov Q Q₀ hQ hlim F'
  simpa only [F',BoundedContinuousFunction.compContinuous_apply,ContinuousMap.coe_mk,
    cavityGroupBlockOfBlock_view,cavityGroupBlockCovariance,cavitySpectralBlockCovariance,
    cavitySpectralGroupBlock,spectralBlockView] using ht

end InvariantIsing

end

end OAI
