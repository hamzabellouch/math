import OAI.Probability.InvariantIsing.Cavity.CavityHaarSpinModel
import OAI.Probability.InvariantIsing.Cavity.CavityFinitePriorMoment
import OAI.Probability.InvariantIsing.Cavity.CavityMovingCappedLogAE
import OAI.Probability.InvariantIsing.Cavity.CavityStrictUniformPath

namespace OAI

/-! The logarithmic capped comparison for the actual Haar and finite
cavity models, with both ordinary fourth moments discharged. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology

namespace InvariantIsing

theorem cavity_finite_capped_log_comparison {m q d k : ℕ}
    (N : ℕ → Fin m → ℕ) (hN : ∀ n a, 0 < N n a)
    (μ : (n : ℕ) → (a : Fin m) → Measure (Orthogonal (N n a)))
    [∀ n a, IsProbabilityMeasure (μ n a)] [∀ n a, (μ n a).IsMulRightInvariant]
    (Ω X : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (X n)]
    [∀ n, Countable (X n)] [∀ n, MeasurableSingletonClass (X n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (ν : (n : ℕ) → Ω n → Measure (X n)) (hν : ∀ n, Measurable (ν n))
    [∀ n ω, IsProbabilityMeasure (ν n ω)]
    (e : Fin d → Fin m × Fin q)
    (v : (n : ℕ) → Ω n → (a : Fin m) → X n → Fin (N n a) → ℝ)
    (hvM : ∀ n x, Measurable (fun ω a => v n ω a x))
    (A₀ : (n : ℕ) → (a : Fin m) → Matrix (Fin (N n a)) (Fin q) ℝ)
    (hA₀ : ∀ n a, (A₀ n a).transpose * A₀ n a = 1)
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hv : ∀ n ω x a, ‖(WithLp.toLp 2 (v n ω a x) : EuclideanSpace ℝ (Fin (N n a)))‖^2 ≤ C₀ * N n a)
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (g : Fin d → Fin m) (p : OverlapPath)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (T : ℝ) (hT : 0 ≤ T) :
    let Q := fun n => cavityLabeledDisorderLaw n (chainExponent (uniformCut n))
      (cavityFiniteRootCovariance ρ eig hρ hsum g (cavityStrictUniformPath p n)
        (cavityStrictUniformLevels p n))
      (cavityFiniteNoiseCovariance ρ eig hρ hsum g (cavityStrictUniformPath p n)
        (uniformCut n) (cavityStrictUniformLevels p n))
    let η := fun n => cavityLabeledPriorKernel n
      (cavityFiniteCovariancePath ρ eig hρ hsum g (cavityStrictUniformPath p n)
        (cavityStrictUniformLevels p n) n) π
    let H := fun n => cavityHaarSpinPotential e (v n) (A₀ n) K L C
    let G := fun n => cavityLabeledPotential n K L C
    (∀ j : ℕ, Tendsto (fun n =>
      (∫ ω, ∫ ξ : Fin j → X n × Spin k,
        (∏ i, Real.exp (min (H n (ω,ξ i)) T))
          ∂Measure.pi (fun _ => (ν n ω.1).prod π) ∂(P n).prod (Measure.pi (μ n))) -
      ∫ ω, ∫ ξ : Fin j → CavityLabeledState d k n,
        (∏ i, Real.exp (min (G n (ω,ξ i)) T))
          ∂Measure.pi (fun _ => η n ω) ∂Q n) atTop (𝓝 0)) →
    Tendsto (fun n =>
      (∫ ω, Real.log (∫ x, Real.exp (min (H n (ω,x)) T) ∂(ν n ω.1).prod π)
        ∂(P n).prod (Measure.pi (μ n))) -
      ∫ ω, Real.log (∫ x, Real.exp (min (G n (ω,x)) T) ∂η n ω) ∂Q n)
      atTop (𝓝 0) := by
  intro Q η H G hraw
  let ν₁ n := cavityHaarSpinPriorKernel (U := (a : Fin m) → Orthogonal (N n a)) (ν n) (hν n) π
  let R n (s : (Ω n × ((a : Fin m) → Orthogonal (N n a))) × (X n × Spin k)) :=
    ‖cavitySelectedSiteProjection e (v n s.1.1) (cavityGroupHaarFrames (A₀ n) s.1.2) s.2.1‖
  let S n (s : CavityLabeledDisorder d n × CavityLabeledState d k n) :=
    ‖(cavityLabeledEndpoint n s).1‖
  let M₁ := (d : ℝ)^2 * cavityGaussianAbsMoment 4 * C₀^2
  let M₂ := cavityGaussianLinearMomentBound d 4 0 (∑ a, (ρ a)⁻¹)
  have hR₀ n := cavity_haar_prior_fourth_moment (P n) (ν n) (hν n) (hN n) (μ n) e (v n)
    (hvM n) (A₀ n) (hA₀ n) hC₀ (hv n) π
  have hR n : (∀ ω, Integrable (fun x => R n (ω,x)^4) (ν₁ n ω)) ∧
      Integrable (fun ω => ∫ x, R n (ω,x)^4 ∂ν₁ n ω) ((P n).prod (Measure.pi (μ n))) ∧
      (∫ ω, ∫ x, R n (ω,x)^4 ∂ν₁ n ω ∂(P n).prod (Measure.pi (μ n))) ≤ M₁ := by
    simpa only [R, ν₁, cavityHaarSpinPriorKernel_apply, M₁] using hR₀ n
  have hM₁ : 0 ≤ M₁ := mul_nonneg
    (mul_nonneg (sq_nonneg _) (cavityGaussianAbsMoment_nonneg 4)) (sq_nonneg C₀)
  have hS n := cavity_finite_prior_fourth_moment ρ eig hρ hsum g (cavityStrictUniformPath p n)
    (uniformCut n) (uniformCut_strict n) (uniformCut_zero n) (uniformCut_last n)
    (cavityStrictUniformLevels p n) (cavityStrictUniformLevels_strict p n)
    (cavityStrictUniformPath_on_cell p n) (cavityStrictUniformLevels_mem p n (Fin.last n)).2 π
  have out := cavity_moving_capped_log_ae (fun n => (P n).prod (Measure.pi (μ n))) Q
    (fun n => ν₁ n) (fun n => (ν₁ n).measurable) (fun n => η n) (fun n => (η n).measurable)
    H R G S (fun n => measurable_cavityHaarSpinPotential e (v n) (hvM n) (A₀ n) K L C)
    (fun n => measurable_cavityLabeledPotential n K L C)
    (fun n => ae_of_all _ (hR n).1) (fun n => (hS n).1)
    (fun n => (hR n).2.1) (fun n => (hS n).2.1)
    (D := cavityFactorSize K L C) (M := max M₁ M₂) (cavityFactorSize_nonneg K L C)
    (hM₁.trans (le_max_left _ _)) hT
    (fun n ω x => cavity_logFactor_growth K L C _ _)
    (fun n ω x => cavity_logFactor_growth K L C _ _)
    (fun n => (hR n).2.2.trans (le_max_left _ _))
    (fun n => (hS n).2.2.trans (le_max_right _ _))
    (by simpa only [ν₁, cavityHaarSpinPriorKernel_apply] using hraw)
  simpa only [ν₁, cavityHaarSpinPriorKernel_apply] using out

end InvariantIsing

end

end OAI
