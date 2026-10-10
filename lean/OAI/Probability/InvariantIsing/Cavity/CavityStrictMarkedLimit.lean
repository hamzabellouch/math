import OAI.Probability.InvariantIsing.Cavity.CavityStrictMarkedLaw
import OAI.Probability.InvariantIsing.Cavity.CavitySpectralMarkedLimit

namespace OAI

/-! The strict finite Gaussian cavity laws and the physical Haar marks
have the same weak limit. The identification uses the proved spectral
GG and Ward consequences through the finite cascade comparison. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_strict_marked_law_tendsto {m r q : ℕ}
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
 :
    let p := spectralSpinQuantilePath Q₀ hP hn
    Tendsto (fun k => cavityStrictMarkedLaw (r := r) (q := q) ρ eig hρ hρsum p k)
      atTop (𝓝 (cavityBlockMarkedLaw (q := q) Q₀ ρ (cavitySpectralGroupBlock m r))) := by
  intro p
  have hH := cavity_spectral_haar_marked_law_tendsto N hN μ A₀ hA₀ X P a ha hGram
    v hvM C hv ρs ρ hρlim hρs hρ hcov Q Q₀ hQ hlim
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro F
  have ht := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hH F
  simp_rw [cavityHaarMarkedLaw_integral _ _ _ _ _ _ _ _ F.continuous.measurable
    (fun x => F.norm_coe_le_norm x)] at ht
  have hdifference := cavity_haar_strict_cascade_match N hN μ A₀ hA₀ X P a ha hGram v hvM C hv
    ρs ρ eig hρs hρ hρlim hρsum hcov Q Q₀ hQ hlim hgg hG d hd0 hd hE hP hn hoff hdiag F
  have hout := ht.sub hdifference
  simp_rw [cavityStrictMarkedLaw_integral ρ eig hρ hρsum p _ _ F.continuous.measurable
    (fun x => F.norm_coe_le_norm x)]
  simpa only [sub_sub_cancel,sub_zero,p,cavityPathReplicaBlock] using hout

end InvariantIsing

end

end OAI
