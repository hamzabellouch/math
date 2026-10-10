import OAI.Probability.InvariantIsing.Cavity.CavityHaarRestrictedGibbs
import OAI.Probability.InvariantIsing.Cavity.CavityFiniteRestrictedComparison
import OAI.Probability.InvariantIsing.Cavity.CavityProductDisorder

namespace OAI

/-! Actual physical Haar Gibbs means and the finite cascade agree after
spatial restriction and fixed positive denominator regularization. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_haar_restricted_gibbs_regularized_match {m r q dim kspin : ℕ}
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
    (hv : ∀ s k (x : Ω k × (ℕ → X k)) j (i l : Fin s), |cavityGroupReplicaGram (fun j (i : Fin s) => v₀ k x.1 j (x.2 i)) j i l| ≤ C)
    (ρs : ℕ → Fin m → ℝ) (ρ eig : Fin m → ℝ)
    (hρs : ∀ k j, 0 < ρs k j) (hρ : ∀ j, 0 < ρ j)
    (hρlim : Tendsto ρs atTop (𝓝 ρ)) (hρsum : ∑ j, ρ j = 1)
    (hcov : ∀ s k (x : Ω k × (ℕ → X k)), cavityGroupReplicaCovariance q (cavityGroupReplicaGram (fun j (i : Fin s) => v₀ k x.1 j (x.2 i))) =
      cavitySpectralBlockCovariance q (ρs k) (spectralBlockView (m + 1) s (cavitySampledEntryArray (B k) x)))
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
    (Cspin : Matrix (Fin kspin) (Fin kspin) ℝ) (T δ : ℝ) (hδ : 0 < δ)
    (π : Measure (Spin kspin)) [IsProbabilityMeasure π]
    (Fspin : SpectralBlock m r × (Fin r → Spin kspin) →ᵇ ℝ)
    {Bcut : ℝ} (hBcut : 0 ≤ Bcut)
    (hnull : ∀ s, (cavityBlockMarkedLaw (q := q) Q₀ ρ (cavitySpectralGroupBlock m s) : Measure
      (SpectralBlock m s × EuclideanSpace ℝ (Fin m × (Fin s × Fin q))))
      {z | cavityReplicaRadius (cavitySelectedGroupProjection e) z = Bcut} = 0) :
    let p := spectralSpinQuantilePath Q₀ hP hn
    Tendsto (fun n =>
      (∫ ω, cavityRegularizedReplicaMean ((ν n ω.1).prod π)
        (fun x => cavityHaarRestrictedWeight e (v₀ n) (A₀ n) K L Cspin T Bcut (ω,x))
        (cavityProjectedSpinTest (cavitySampledGroupBlock (B n) ω.1) Fspin) δ
        ∂(P n).prod (Measure.pi (μ n))) -
      ∫ ω, cavityRegularizedReplicaMean
        (cavityLabeledPriorKernel n
          (cavityFiniteCovariancePath ρ eig hρ hρsum g (cavityStrictUniformPath p n)
            (cavityStrictUniformLevels p n) n) π ω)
        (fun x => cavityLabeledRestrictedWeight n K L Cspin T Bcut (ω,x))
        (fun σ => cavityLabeledReplicaTest
          (cavityFiniteReplicaSpectralBlock ρ eig hρ hρsum (cavityStrictUniformPath p n)
            (cavityStrictUniformLevels p n)) Fspin (ω,σ)) δ
        ∂cavityLabeledDisorderLaw n (chainExponent (uniformCut n))
          (cavityFiniteRootCovariance ρ eig hρ hρsum g (cavityStrictUniformPath p n)
            (cavityStrictUniformLevels p n))
          (cavityFiniteNoiseCovariance ρ eig hρ hρsum g (cavityStrictUniformPath p n)
            (uniformCut n) (cavityStrictUniformLevels p n))) atTop (𝓝 0) := by
  intro p
  have hBg n x y : Measurable (fun (ω : Ω n) (a : Fin m) => B n ω x y a.castSucc) :=
    Measurable.of_eval fun a => (measurable_pi_apply a.castSucc).comp (hB n x y)
  apply cavity_finite_restricted_spin_comparison N μ Ω X P ν hν e v₀ hvM A₀
    (fun n ω x y a => B n ω x y a.castSucc) hBg ρ eig hρ hρsum g p
    K L Cspin π T Bcut δ hδ Fspin
  intro j
  have h := cavity_haar_restricted_gibbs_numerator_match N hN μ A₀ hA₀ Ω X P ν hν B hB
    hGram v₀ hvM C (hv (r+j)) ρs ρ eig hρs hρ hρlim hρsum (hcov (r+j))
    Q Q₀ hQ hlim hgg hG d hd0 hd hE hP hn hoff hdiag g e he heg
    K L Cspin T π (cavityReplicaPrefixTest j Fspin) hBcut (hnull (r+j))
  apply h.congr'
  filter_upwards [] with n
  congr 1
  let w := cavityHaarRestrictedWeight e (v₀ n) (A₀ n) K L Cspin T Bcut
  let f := cavityHaarSpinReplicaTest (U := (a : Fin m) → Orthogonal (N n a))
    (cavitySampledGroupBlock (B n)) (cavityReplicaPrefixTest j Fspin)
  have hf := measurable_cavityHaarSpinReplicaTest (U := (a : Fin m) → Orthogonal (N n a)) (cavitySampledGroupBlock (B n))
    (measurable_cavitySampledGroupBlock (B n) (hB n)) (cavityReplicaPrefixTest j Fspin)
  have hi := cavity_product_disorder_numerator (P n) (Measure.pi (μ n)) (ν n) (hν n) π
    w (measurable_cavityHaarRestrictedWeight e (v₀ n) (hvM n) (A₀ n) K L Cspin T Bcut)
    f hf (Real.exp_pos T).le (norm_nonneg (cavityReplicaPrefixTest j Fspin))
    (fun ω x => cavityHaarRestrictedWeight_mem e (v₀ n) (A₀ n) K L Cspin T Bcut (ω,x))
    (fun ω σ => cavityHaarSpinReplicaTest_bound _ (cavityReplicaPrefixTest j Fspin) (ω,σ))
  exact hi

end InvariantIsing

end

end OAI
