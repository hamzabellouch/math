import OAI.Probability.InvariantIsing.Cavity.CavityFiniteTiltedTail
import OAI.Probability.InvariantIsing.Cavity.CavityTailIntegral
import OAI.Probability.InvariantIsing.Cavity.CavityMovingFullReplicaTight
import OAI.Probability.InvariantIsing.Cavity.CavityLabeledModelNumerator

namespace OAI

/-! Removing the cap in a comparison with the finite spectral cavity
model using uniform moments and tightness. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology BigOperators BoundedContinuousFunction Matrix Matrix.Norms.L2Operator

namespace InvariantIsing

theorem cavity_finite_full_replica_comparison {m d N k r : ℕ}
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (B : Matrix (Fin (m * N)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (g : Fin d → Fin m) (a : Fin m) (ha : ∀ b, eig b ≤ eig a)
    (p : OverlapPath) (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (π : Measure (Spin k)) [IsProbabilityMeasure π]
    {Ω X : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (X n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (ν : (n : ℕ) → Ω n → Measure (X n)) (hν : ∀ n, Measurable (ν n))
    [∀ n ω, IsProbabilityMeasure (ν n ω)]
    (H R : (n : ℕ) → Ω n × X n → ℝ) (hH : ∀ n, Measurable (H n))
    (hR : ∀ n, Measurable (R n))
    (f : (n : ℕ) → Ω n × (Fin r → X n) → ℝ) (hf : ∀ n, Measurable (f n))
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ)
    (hfb : ∀ n ω σ, |f n (ω,σ)| ≤ ‖F‖)
    {D : ℝ} (hD : 0 ≤ D) (hg : ∀ n ω x, |H n (ω,x)| ≤ D * (1 + (R n (ω,x))^2))
    (he : ∀ n, ∀ᵐ ω ∂P n, Integrable (fun x => Real.exp (H n (ω,x))) (ν n ω))
    (ht : ∀ ε > 0, ∃ A > 0, ∀ᶠ n in atTop,
      (∫ ω, ((ν n ω).tilted (fun x => H n (ω,x))).real {x | A < |R n (ω,x)|} ∂P n) < ε) :
    let K := B.transpose * cavityRepeatedSpectrum (n := N) eig * B -
      Matrix.diagonal (fun i => eig (g i))
    let Q := fun n => cavityLabeledDisorderLaw n (chainExponent (uniformCut n))
      (cavityFiniteRootCovariance ρ eig hρ hsum g (cavityStrictUniformPath p n)
        (cavityStrictUniformLevels p n))
      (cavityFiniteNoiseCovariance ρ eig hρ hsum g (cavityStrictUniformPath p n)
        (uniformCut n) (cavityStrictUniformLevels p n))
    let η := fun n => cavityLabeledPriorKernel n
      (cavityFiniteCovariancePath ρ eig hρ hsum g (cavityStrictUniformPath p n)
        (cavityStrictUniformLevels p n) n) π
    let G := fun n => cavityLabeledPotential n K L C
    let V := fun n => cavityLabeledReplicaTest
      (cavityFiniteReplicaSpectralBlock ρ eig hρ hsum (cavityStrictUniformPath p n)
        (cavityStrictUniformLevels p n)) F
    (∀ T > 0, Tendsto (fun n =>
      (∫ ω, cavityWeightedReplicaMean (ν n ω) (fun x => Real.exp (min (H n (ω,x)) T))
        (fun σ => f n (ω,σ)) ∂P n) -
      ∫ ω, cavityWeightedReplicaMean (η n ω) (fun x => Real.exp (min (G n (ω,x)) T))
        (fun σ => V n (ω,σ)) ∂Q n) atTop (𝓝 0)) →
    Tendsto (fun n =>
      (∫ ω, cavityWeightedReplicaMean (ν n ω) (fun x => Real.exp (H n (ω,x)))
        (fun σ => f n (ω,σ)) ∂P n) -
      ∫ ω, cavityWeightedReplicaMean (η n ω) (fun x => Real.exp (G n (ω,x)))
        (fun σ => V n (ω,σ)) ∂Q n) atTop (𝓝 0) := by
  intro K Q η G V hcap
  let S n (z : CavityLabeledDisorder d n × CavityLabeledState d k n) :=
    ‖(cavityLabeledEndpoint n z).1‖
  have hG n : Measurable (G n) := measurable_cavityLabeledPotential n K L C
  have hS n : Measurable (S n) := (measurable_cavityLabeledEndpoint n).fst.norm
  have hmodel n := cavity_finite_labeled_moment ρ eig hρ hsum B hB g a ha
    (cavityStrictUniformPath p n) (uniformCut n) (uniformCut_strict n)
    (uniformCut_zero n) (uniformCut_last n) (cavityStrictUniformLevels p n)
    (cavityStrictUniformLevels_strict p n) (cavityStrictUniformPath_on_cell p n)
    (cavityStrictUniformLevels_mem p n (Fin.last n)).2 L C π 2
  have htmodel : ∀ ε > 0, ∃ A > 0, ∀ᶠ n in atTop,
      (∫ ω, ((η n ω).tilted (fun x => G n (ω,x))).real
        {x | A < |S n (ω,x)|} ∂Q n) < ε := by
    simpa only [S, abs_norm, η, Q, G, K] using
      cavity_strict_finite_labeled_tight ρ eig hρ hsum B hB g a ha p L C π
  have hsumtail := cavity_tightness_add
    (fun n A => ∫ ω, ((ν n ω).tilted (fun x => H n (ω,x))).real
      {x | A < |R n (ω,x)|} ∂P n)
    (fun n A => ∫ ω, ((η n ω).tilted (fun x => G n (ω,x))).real
      {x | A < |S n (ω,x)|} ∂Q n)
    (fun n => cavity_random_tilted_tail_antitone (P n) (ν n) (hν n) (H n) (R n) (hH n) (hR n))
    (fun n => cavity_random_tilted_tail_antitone (Q n) (η n) (η n).measurable (G n) (S n) (hG n) (hS n))
    ht htmodel
  apply cavity_moving_full_replica_tight P Q ν hν (fun n => η n) (fun n => (η n).measurable)
    H R G S hH hR hG hS f hf V (fun n => measurable_cavityLabeledReplicaTest _ F)
    (D := max D (cavityFactorSize K L C)) (norm_nonneg F)
    (hD.trans (le_max_left _ _)) hfb
    (fun n ω σ => (Real.norm_eq_abs _).symm.trans_le (F.norm_coe_le_norm _))
    ?_ ?_ he (fun n => (hmodel n).1.mono (fun _ h => h.1)) hsumtail hcap
  · intro n ω x
    exact (hg n ω x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · intro n ω x
    exact (cavity_logFactor_growth K L C _ _).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

end InvariantIsing

end

end OAI
