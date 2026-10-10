import OAI.Probability.InvariantIsing.Cavity.CavityCoefficientMean

namespace OAI

/-! Concentrating random cavity blocks may be replaced in every capped
replica moment, uniformly over the growing physical state spaces. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem cavity_capped_coefficient_tendsto
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)] {d k r : ℕ}
    (A A' : (n : ℕ) → Ω n → CavityFactorBlocks d k)
    (hA : ∀ n, Measurable (A n)) (hA' : ∀ n, Measurable (A' n))
    (y : (n : ℕ) → Ω n → Fin r → EuclideanSpace ℝ (Fin d)) (hy : ∀ n, Measurable (y n))
    (ε : (n : ℕ) → Ω n → Fin r → Spin k) (hε : ∀ n, Measurable (ε n))
    (F : (n : ℕ) → Ω n → ℝ) (hF : ∀ n, Measurable (F n))
    {B : ℝ} (hB : 0 ≤ B) (hFb : ∀ n ω, |F n ω| ≤ B)
    (T : ℝ) (s : (n : ℕ) → Set (Ω n)) (hs : ∀ n, MeasurableSet (s n))
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n) (hδlim : Tendsto δ atTop (𝓝 0))
    (hclose : ∀ n ω, ω ∈ s n → cavityFactorSize ((A n ω).1 - (A' n ω).1)
      ((A n ω).2.1 - (A' n ω).2.1) ((A n ω).2.2 - (A' n ω).2.2) ≤ δ n)
    (hbad : Tendsto (fun n => (P n).real (s n)ᶜ) atTop (𝓝 0))
    (hi : ∀ n, Integrable (fun ω => ∑ i, (1 + ‖y n ω i‖^2)) (P n))
    {M : ℝ} (hM : ∀ n, (∫ ω, ∑ i, (1 + ‖y n ω i‖^2) ∂P n) ≤ M) :
    Tendsto (fun n =>
      (∫ ω, cavityCappedReplicaProduct (A n ω) T (y n ω) (ε n ω) * F n ω ∂P n) -
      ∫ ω, cavityCappedReplicaProduct (A' n ω) T (y n ω) (ε n ω) * F n ω ∂P n)
      atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun n => ?_)
    (show Tendsto (fun n => Real.exp ((r : ℝ) * T) * B *
      (δ n * M + 2 * (P n).real (s n)ᶜ)) atTop (𝓝 0) by
      simpa only [zero_mul, mul_zero, add_zero] using
        ((hδlim.mul_const M).add (hbad.const_mul 2)).const_mul (Real.exp ((r : ℝ) * T) * B))
  rw [Real.norm_eq_abs]
  exact cavity_capped_coefficient_mean_error (P n) (A n) (A' n) (hA n) (hA' n)
    (y n) (hy n) (ε n) (hε n) (F n) (hF n) hB (hFb n) T (s n) (hs n)
    (hδ n) (hclose n) (hi n) (hM n)

end InvariantIsing

end

end OAI
