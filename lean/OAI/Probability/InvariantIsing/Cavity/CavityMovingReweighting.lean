import OAI.Probability.InvariantIsing.Cavity.CavityRegularizedReweighting
import OAI.Probability.InvariantIsing.Cavity.CavityMovingMoments

namespace OAI

/-! Extra-replica comparison for a finite system and a refining cascade.
A positive denominator regularizer makes the matching-moment passage continuous. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology

namespace InvariantIsing

theorem cavity_moving_regularized_reweighted_test
    {Ω X Ξ Y : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (X n)]
    [∀ n, MeasurableSpace (Ξ n)] [∀ n, MeasurableSpace (Y n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Q : (n : ℕ) → Measure (Ξ n)) [∀ n, IsProbabilityMeasure (Q n)]
    (ν : (n : ℕ) → Ω n → Measure (X n)) (hν : ∀ n, Measurable (ν n))
    [∀ n ω, IsProbabilityMeasure (ν n ω)]
    (ρ : (n : ℕ) → Ξ n → Measure (Y n)) (hρ : ∀ n, Measurable (ρ n))
    [∀ n ω, IsProbabilityMeasure (ρ n ω)]
    (w : (n : ℕ) → Ω n × X n → ℝ) (hw : ∀ n, Measurable (w n))
    (v : (n : ℕ) → Ξ n × Y n → ℝ) (hv : ∀ n, Measurable (v n)) {r : ℕ}
    (F : (n : ℕ) → Ω n × (Fin r → X n) → ℝ) (hF : ∀ n, Measurable (F n))
    (G : (n : ℕ) → Ξ n × (Fin r → Y n) → ℝ) (hG : ∀ n, Measurable (G n))
    {δ M B : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hwb : ∀ n ω x, w n (ω, x) ∈ Icc 0 M) (hvb : ∀ n ω x, v n (ω, x) ∈ Icc 0 M)
    (hFb : ∀ n ω σ, |F n (ω, σ)| ≤ B) (hGb : ∀ n ω σ, |G n (ω, σ)| ≤ B)
    (hmom : ∀ k : ℕ, Tendsto (fun n =>
      (∫ ω, ∫ ξ : (Fin r ⊕ Fin k) → X n,
        (∏ i, w n (ω, ξ i)) * F n (ω, fun i => ξ (.inl i))
          ∂Measure.pi (fun _ => ν n ω) ∂P n) -
      ∫ ω, ∫ ξ : (Fin r ⊕ Fin k) → Y n,
        (∏ i, v n (ω, ξ i)) * G n (ω, fun i => ξ (.inl i))
          ∂Measure.pi (fun _ => ρ n ω) ∂Q n) atTop (𝓝 0)) :
    Tendsto (fun n =>
      (∫ ω, cavityRegularizedReplicaMean (ν n ω)
        (fun x => w n (ω, x)) (fun σ => F n (ω, σ)) δ ∂P n) -
      ∫ ω, cavityRegularizedReplicaMean (ρ n ω)
        (fun x => v n (ω, x)) (fun σ => G n (ω, σ)) δ ∂Q n) atTop (𝓝 0) := by
  have hwabs n ω x : |w n (ω, x)| ≤ M := by
    rw [abs_of_nonneg (hwb n ω x).1]
    exact (hwb n ω x).2
  have hvabs n ω x : |v n (ω, x)| ≤ M := by
    rw [abs_of_nonneg (hvb n ω x).1]
    exact (hvb n ω x).2
  have hmixed k : Tendsto (fun n =>
      (∫ ω, cavityWeightNumerator (ν n ω) (fun x => w n (ω, x)) (fun σ => F n (ω, σ)) *
        cavityWeightNormalizer (ν n ω) (fun x => w n (ω, x)) ^ k ∂P n) -
      ∫ ω, cavityWeightNumerator (ρ n ω) (fun x => v n (ω, x)) (fun σ => G n (ω, σ)) *
        cavityWeightNormalizer (ρ n ω) (fun x => v n (ω, x)) ^ k ∂Q n) atTop (𝓝 0) := by
    have hp n ω := cavityWeightNumerator_mul_normalizer (ν n ω) (fun x => w n (ω, x))
      (fun σ => F n (ω, σ)) ((hw n).comp measurable_prodMk_left)
      ((hF n).comp measurable_prodMk_left) k
    have hq n ω := cavityWeightNumerator_mul_normalizer (ρ n ω) (fun x => v n (ω, x))
      (fun σ => G n (ω, σ)) ((hv n).comp measurable_prodMk_left)
      ((hG n).comp measurable_prodMk_left) k
    simpa only [hp, hq] using hmom k
  have hc : ContinuousOn (fun z : ℝ => 1 / (z + δ) ^ r) (Icc 0 M) :=
    continuousOn_const.div ((continuousOn_id.add continuousOn_const).pow r)
      (fun z hz => pow_ne_zero _ (by linarith [hz.1]))
  have ht := cavity_moving_weighted_moments P Q
    (fun n ω => cavityWeightNormalizer (ν n ω) (fun x => w n (ω, x)))
    (fun n ω => cavityWeightNumerator (ν n ω) (fun x => w n (ω, x)) (fun σ => F n (ω, σ)))
    (fun n ω => cavityWeightNormalizer (ρ n ω) (fun x => v n (ω, x)))
    (fun n ω => cavityWeightNumerator (ρ n ω) (fun x => v n (ω, x)) (fun σ => G n (ω, σ)))
    (fun n => measurable_cavityWeightNormalizer (ν n) (hν n) (w n) (hw n))
    (fun n => measurable_cavityWeightNumerator (ν n) (hν n) (w n) (hw n) (F n) (hF n))
    (fun n => measurable_cavityWeightNormalizer (ρ n) (hρ n) (v n) (hv n))
    (fun n => measurable_cavityWeightNumerator (ρ n) (hρ n) (v n) (hv n) (G n) (hG n))
    (mul_nonneg hB (pow_nonneg hM r))
    (fun n ω => cavityWeightNormalizer_mem (ν n ω) _ ((hw n).comp measurable_prodMk_left)
      le_rfl (hwb n ω))
    (fun n ω => cavityWeightNormalizer_mem (ρ n ω) _ ((hv n).comp measurable_prodMk_left)
      le_rfl (hvb n ω))
    (fun n ω => cavityWeightNumerator_abs_le (ν n ω) _ _ hM hB (hwabs n ω) (hFb n ω))
    (fun n ω => cavityWeightNumerator_abs_le (ρ n ω) _ _ hM hB (hvabs n ω) (hGb n ω))
    hmixed _ hc
  simpa only [cavityRegularizedReplicaMean, one_div, ← div_eq_mul_inv] using ht

end InvariantIsing

end

end OAI
