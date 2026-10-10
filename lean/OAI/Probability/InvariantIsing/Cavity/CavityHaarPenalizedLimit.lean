import OAI.Probability.InvariantIsing.Cavity.CavityHaarVariablePenalty

namespace OAI

/-! The actual capped cavity logarithm with its geometric penalty has
its deterministic-block limit after fresh-Haar averaging. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

theorem cavity_haar_penalized_coefficient_limit {m q d k : ℕ}
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
    (hv : ∀ n ω x a, ‖(WithLp.toLp 2 (v n ω a x) :
      EuclideanSpace ℝ (Fin (N n a)))‖^2 ≤ C₀ * N n a)
    (A : (n : ℕ) → Ω n → CavityFactorBlocks d k) (hA : ∀ n, Measurable (A n))
    (A₁ : CavityFactorBlocks d k) {D : ℝ} (hD : 0 ≤ D)
    (hAb : ∀ n ω, cavityFactorSize (A n ω).1 (A n ω).2.1 (A n ω).2.2 ≤ D)
    (hA₁ : cavityFactorSize A₁.1 A₁.2.1 A₁.2.2 ≤ D)
    (hprob : ∀ δ > 0, Tendsto (fun n => (P n).real
      {ω | δ < cavityFactorDeviation (A n ω) A₁}) atTop (𝓝 0))
    (π : Measure (Spin k)) [IsProbabilityMeasure π] (T : ℝ) (hT : 0 ≤ T)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n) (hδlim : Tendsto δ atTop (𝓝 0)) :
    let Y := fun n (p : (Ω n × ((a : Fin m) → Orthogonal (N n a))) × (X n × Spin k)) =>
      cavitySelectedSiteProjection e (v n p.1.1) (cavityGroupHaarFrames (A₀ n) p.1.2) p.2.1
    Tendsto (fun n =>
      (∫ ω, Real.log (∫ x, Real.exp (min
        (cavityLogFactor (A n ω.1).1 (A n ω.1).2.1 (A n ω.1).2.2 (Y n (ω,x)) x.2) T -
          δ n*(1+‖Y n (ω,x)‖^2))
        ∂(ν n ω.1).prod π) ∂(P n).prod (Measure.pi (μ n))) -
      ∫ ω, Real.log (∫ x, Real.exp (min
        (cavityLogFactor A₁.1 A₁.2.1 A₁.2.2 (Y n (ω,x)) x.2) T)
        ∂(ν n ω.1).prod π) ∂(P n).prod (Measure.pi (μ n))) atTop (𝓝 0) := by
  intro Y
  have hc := cavity_haar_capped_coefficient_limit N hN μ Ω X P ν hν e v hvM A₀ hA₀ hC₀ hv
    A hA A₁ hD hAb hA₁ hprob π T hT
  have hp := cavity_haar_variable_quadratic_penalty N hN μ Ω X P ν hν e v hvM A₀ hA₀ hC₀ hv
    A hA hD hAb π T hT δ hδ hδlim
  have ht := hc.sub hp
  convert ht using 1
  · funext n
    dsimp only [Y]
    ring
  · simp

end InvariantIsing

end

end OAI
