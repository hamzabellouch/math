import OAI.Probability.InvariantIsing.Cavity.CavityHaarRestrictedWeight
import OAI.Probability.InvariantIsing.Cavity.CavityLabeledRestrictedModel
import OAI.Probability.InvariantIsing.Cavity.CavityMovingRestrictedMoments
import OAI.Probability.InvariantIsing.Cavity.CavityStrictUniformPath

namespace OAI

/-! Fixed-floor normalization of the actual physical and finite-cascade
restricted spin numerators. All weight bounds are proved pointwise. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_finite_restricted_spin_comparison {m q d k r : ℕ}
    (N : ℕ → Fin m → ℕ)
    (μ : (n : ℕ) → (a : Fin m) → Measure (Orthogonal (N n a)))
    [∀ n a, IsProbabilityMeasure (μ n a)]
    (Ω X : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (X n)]
    [∀ n, Countable (X n)] [∀ n, MeasurableSingletonClass (X n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (ν : (n : ℕ) → Ω n → Measure (X n)) (hν : ∀ n, Measurable (ν n))
    [∀ n ω, IsProbabilityMeasure (ν n ω)]
    (e : Fin d → Fin m × Fin q)
    (v : (n : ℕ) → Ω n → (a : Fin m) → X n → Fin (N n a) → ℝ)
    (hvM : ∀ n x, Measurable (fun ω a => v n ω a x))
    (A₀ : (n : ℕ) → (a : Fin m) → Matrix (Fin (N n a)) (Fin q) ℝ)
    (B : (n : ℕ) → Ω n → X n → X n → SpectralEntry m)
    (hB : ∀ n x y, Measurable (fun ω => B n ω x y))
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (g : Fin d → Fin m) (p : OverlapPath)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (T Bcut δ : ℝ) (hδ : 0 < δ) (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ)
    (hraw : ∀ j : ℕ, Tendsto (fun n =>
      (∫ ω, cavityWeightNumerator ((ν n ω.1).prod π)
        (fun x => cavityHaarRestrictedWeight e (v n) (A₀ n) K L C T Bcut (ω,x))
        (cavityProjectedSpinTest (fun σ i l => B n ω.1 (σ i) (σ l))
          (cavityReplicaPrefixTest j F)) ∂(P n).prod (Measure.pi (μ n))) -
      ∫ ω, cavityLabeledRestrictedNumerator n K
        (cavityFiniteCovariancePath ρ eig hρ hsum g (cavityStrictUniformPath p n)
          (cavityStrictUniformLevels p n) n) L C π T Bcut
        (cavityFiniteReplicaSpectralBlock ρ eig hρ hsum (cavityStrictUniformPath p n)
          (cavityStrictUniformLevels p n)) (cavityReplicaPrefixTest j F) ω
        ∂cavityLabeledDisorderLaw n (chainExponent (uniformCut n))
          (cavityFiniteRootCovariance ρ eig hρ hsum g (cavityStrictUniformPath p n)
            (cavityStrictUniformLevels p n))
          (cavityFiniteNoiseCovariance ρ eig hρ hsum g (cavityStrictUniformPath p n)
            (uniformCut n) (cavityStrictUniformLevels p n))) atTop (𝓝 0)) :
    Tendsto (fun n =>
      (∫ ω, cavityRegularizedReplicaMean ((ν n ω.1).prod π)
        (fun x => cavityHaarRestrictedWeight e (v n) (A₀ n) K L C T Bcut (ω,x))
        (cavityProjectedSpinTest (fun σ i l => B n ω.1 (σ i) (σ l)) F) δ
        ∂(P n).prod (Measure.pi (μ n))) -
      ∫ ω, cavityRegularizedReplicaMean
        (cavityLabeledPriorKernel n
          (cavityFiniteCovariancePath ρ eig hρ hsum g (cavityStrictUniformPath p n)
            (cavityStrictUniformLevels p n) n) π ω)
        (fun x => cavityLabeledRestrictedWeight n K L C T Bcut (ω,x))
        (fun σ => cavityLabeledReplicaTest
          (cavityFiniteReplicaSpectralBlock ρ eig hρ hsum (cavityStrictUniformPath p n)
            (cavityStrictUniformLevels p n)) F (ω,σ)) δ
        ∂cavityLabeledDisorderLaw n (chainExponent (uniformCut n))
          (cavityFiniteRootCovariance ρ eig hρ hsum g (cavityStrictUniformPath p n)
            (cavityStrictUniformLevels p n))
          (cavityFiniteNoiseCovariance ρ eig hρ hsum g (cavityStrictUniformPath p n)
            (uniformCut n) (cavityStrictUniformLevels p n))) atTop (𝓝 0) := by
  let Q n := cavityLabeledDisorderLaw n (chainExponent (uniformCut n))
    (cavityFiniteRootCovariance ρ eig hρ hsum g (cavityStrictUniformPath p n) (cavityStrictUniformLevels p n))
    (cavityFiniteNoiseCovariance ρ eig hρ hsum g (cavityStrictUniformPath p n) (uniformCut n)
      (cavityStrictUniformLevels p n))
  let ν₁ n := cavityHaarSpinPriorKernel (U := (a : Fin m) → Orthogonal (N n a)) (ν n) (hν n) π
  let ν₂ n := cavityLabeledPriorKernel n
    (cavityFiniteCovariancePath ρ eig hρ hsum g (cavityStrictUniformPath p n)
      (cavityStrictUniformLevels p n) n) π
  let w n := cavityHaarRestrictedWeight e (v n) (A₀ n) K L C T Bcut
  let w₂ n := cavityLabeledRestrictedWeight n K L C T Bcut
  let F₁ n := cavityHaarSpinReplicaTest (U := (a : Fin m) → Orthogonal (N n a))
    (fun ω σ i l => B n ω (σ i) (σ l)) F
  let F₂ n := cavityLabeledReplicaTest (d := d)
    (cavityFiniteReplicaSpectralBlock ρ eig hρ hsum (cavityStrictUniformPath p n)
      (cavityStrictUniformLevels p n)) F
  have hfB n (σ : Fin r → X n) : Measurable (fun ω => fun (i l : Fin r) => B n ω (σ i) (σ l)) :=
    Measurable.of_eval fun i => Measurable.of_eval fun l => hB n (σ i) (σ l)
  have hout := cavity_moving_regularized_test_fin
    (fun n => (P n).prod (Measure.pi (μ n))) Q (fun n ω => ν₁ n ω)
    (fun n => (ν₁ n).measurable)
    (fun n ω => ν₂ n ω) (fun n => (ν₂ n).measurable) w
    (fun n => measurable_cavityHaarRestrictedWeight e (v n) (hvM n) (A₀ n) K L C T Bcut)
    w₂ (fun n => measurable_cavityLabeledRestrictedWeight n K L C T Bcut)
    F₁ (fun n => measurable_cavityHaarSpinReplicaTest _ (hfB n) F)
    F₂ (fun n => measurable_cavityLabeledReplicaTest _ F)
    hδ (Real.exp_pos T).le (norm_nonneg F)
    (fun n ω x => cavityHaarRestrictedWeight_mem e (v n) (A₀ n) K L C T Bcut (ω,x))
    (fun n ω x => cavityLabeledRestrictedWeight_mem n K L C T Bcut (ω,x))
    (fun n ω σ => cavityHaarSpinReplicaTest_bound _ F (ω,σ))
    (fun n ω σ => (Real.norm_eq_abs _).symm.trans_le (F.norm_coe_le_norm _)) ?_
  · simpa only [ν₁,ν₂,cavityHaarSpinPriorKernel_apply,w,w₂,F₁,F₂,cavityHaarSpinReplicaTest,Q] using hout
  · intro j
    convert hraw j using 1
    funext n
    congr 1
    · apply integral_congr_ae
      filter_upwards [] with ω
      unfold cavityWeightNumerator
      simp only [ν₁,cavityHaarSpinPriorKernel_apply]
      apply integral_congr_ae
      filter_upwards [] with ξ
      simp only [w,F₁,cavityHaarSpinReplicaTest,cavityProjectedSpinTest,cavityReplicaPrefixTest]
      rfl
    · apply integral_congr_ae
      filter_upwards [] with ω
      unfold cavityLabeledRestrictedNumerator cavityWeightNumerator
      apply integral_congr_ae
      filter_upwards [] with ξ
      simp only [w₂,F₂,cavityLabeledReplicaTest_prefix]

end InvariantIsing

end

end OAI
