import OAI.Probability.InvariantIsing.Cavity.CavityLogProbability
import OAI.Probability.InvariantIsing.Cavity.CavityCoefficientProbability

namespace OAI

/-! Replacement of random cavity blocks inside the capped expected
logarithm.  The hypotheses are the proved coefficient and prior bounds. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

theorem cavity_capped_block_log_limit {d k : ℕ}
    {Ω X : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (X n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (ν : (n : ℕ) → Ω n → Measure (X n)) (hν : ∀ n, Measurable (ν n))
    [∀ n ω, IsProbabilityMeasure (ν n ω)]
    (A : (n : ℕ) → Ω n → CavityFactorBlocks d k) (hA : ∀ n, Measurable (A n))
    (A₀ : CavityFactorBlocks d k)
    (Y : (n : ℕ) → Ω n × X n → EuclideanSpace ℝ (Fin d))
    (hY : ∀ n, Measurable (Y n))
    (ε : (n : ℕ) → Ω n × X n → Spin k) (hε : ∀ n, Measurable (ε n))
    (hi : ∀ n ω, Integrable (fun x => ‖Y n (ω,x)‖^4) (ν n ω))
    (hmi : ∀ n, Integrable (fun ω => ∫ x, ‖Y n (ω,x)‖^4 ∂ν n ω) (P n))
    {D M T : ℝ} (hD : 0 ≤ D) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hAb : ∀ n ω, cavityFactorSize (A n ω).1 (A n ω).2.1 (A n ω).2.2 ≤ D)
    (hA₀b : cavityFactorSize A₀.1 A₀.2.1 A₀.2.2 ≤ D)
    (hMR : ∀ n, (∫ ω, ∫ x, ‖Y n (ω,x)‖^4 ∂ν n ω ∂P n) ≤ M)
    (hprob : ∀ δ > 0, Tendsto (fun n => (P n).real
      {ω | δ < cavityFactorDeviation (A n ω) A₀}) atTop (𝓝 0)) :
    Tendsto (fun n =>
      (∫ ω, Real.log (∫ x, Real.exp (min
        (cavityLogFactor (A n ω).1 (A n ω).2.1 (A n ω).2.2 (Y n (ω,x)) (ε n (ω,x))) T)
        ∂ν n ω) ∂P n) -
      ∫ ω, Real.log (∫ x, Real.exp (min
        (cavityLogFactor A₀.1 A₀.2.1 A₀.2.2 (Y n (ω,x)) (ε n (ω,x))) T)
        ∂ν n ω) ∂P n) atTop (𝓝 0) := by
  let : OpensMeasurableSpace (CavityFactorBlocks d k) := inferInstanceAs
    (OpensMeasurableSpace ((Fin d → Fin d → ℝ) ×
      ((Fin d → Fin k → ℝ) × (Fin k → Fin k → ℝ))))
  let H n p := cavityLogFactor (A n p.1).1 (A n p.1).2.1 (A n p.1).2.2 (Y n p) (ε n p)
  let G n p := cavityLogFactor A₀.1 A₀.2.1 A₀.2.2 (Y n p) (ε n p)
  have hm n (B : Ω n → CavityFactorBlocks d k) (hB : Measurable B) :
      Measurable (fun p : Ω n × X n =>
        cavityLogFactor (B p.1).1 (B p.1).2.1 (B p.1).2.2 (Y n p) (ε n p)) := by
    unfold cavityLogFactor cavityQuadratic
    fun_prop
  refine cavity_capped_log_probability_limit P ν hν H G (fun n p => ‖Y n p‖)
    (fun n => hm n (A n) (hA n)) (fun n => hm n (fun _ => A₀) measurable_const)
    hi hmi hD hM hT ?_ ?_ hMR (fun n ω => cavityFactorDeviation (A n ω) A₀)
    (fun n => (continuous_cavityFactorDeviation A₀).measurable.comp (hA n)) ?_ hprob
  · intro n ω x
    exact (cavity_logFactor_growth _ _ _ _ _).trans
      (mul_le_mul_of_nonneg_right (hAb n ω) (by positivity))
  · intro n ω x
    exact (cavity_logFactor_growth _ _ _ _ _).trans
      (mul_le_mul_of_nonneg_right hA₀b (by positivity))
  · intro n ω x
    change |cavityLogFactor _ _ _ _ _-cavityLogFactor _ _ _ _ _| ≤ _
    rw [cavityLogFactor_sub]
    exact cavity_logFactor_growth _ _ _ _ _

end InvariantIsing

end

end OAI
