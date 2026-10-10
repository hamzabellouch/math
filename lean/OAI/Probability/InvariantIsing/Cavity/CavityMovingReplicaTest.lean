import OAI.Probability.InvariantIsing.Cavity.CavityMovingReweighting
import OAI.Probability.InvariantIsing.Cavity.CavityMovingRatio

namespace OAI

/-! Unregularized bounded replica comparison between the physical system
and its refining cascade, using uniform negative-log moments. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology

namespace InvariantIsing

theorem cavity_moving_reweighted_test
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
    {M B K : ℝ} (hM : 1 ≤ M) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hwb : ∀ n ω x, w n (ω, x) ∈ Icc 0 M) (hvb : ∀ n ω x, v n (ω, x) ∈ Icc 0 M)
    (hFb : ∀ n ω σ, |F n (ω, σ)| ≤ B) (hGb : ∀ n ω σ, |G n (ω, σ)| ≤ B)
    (hZ0 : ∀ n ω, 0 < cavityWeightNormalizer (ν n ω) (fun x => w n (ω, x)))
    (hW0 : ∀ n ω, 0 < cavityWeightNormalizer (ρ n ω) (fun x => v n (ω, x)))
    (hiZ : ∀ n, Integrable (fun ω => (max (-Real.log
      (cavityWeightNormalizer (ν n ω) (fun x => w n (ω, x)))) 0)^2) (P n))
    (hiW : ∀ n, Integrable (fun ω => (max (-Real.log
      (cavityWeightNormalizer (ρ n ω) (fun x => v n (ω, x)))) 0)^2) (Q n))
    (hKZ : ∀ n, (∫ ω, (max (-Real.log
      (cavityWeightNormalizer (ν n ω) (fun x => w n (ω, x)))) 0)^2 ∂P n) ≤ K)
    (hKW : ∀ n, (∫ ω, (max (-Real.log
      (cavityWeightNormalizer (ρ n ω) (fun x => v n (ω, x)))) 0)^2 ∂Q n) ≤ K)
    (hmom : ∀ k : ℕ, Tendsto (fun n =>
      (∫ ω, ∫ ξ : (Fin r ⊕ Fin k) → X n,
        (∏ i, w n (ω, ξ i)) * F n (ω, fun i => ξ (.inl i))
          ∂Measure.pi (fun _ => ν n ω) ∂P n) -
      ∫ ω, ∫ ξ : (Fin r ⊕ Fin k) → Y n,
        (∏ i, v n (ω, ξ i)) * G n (ω, fun i => ξ (.inl i))
          ∂Measure.pi (fun _ => ρ n ω) ∂Q n) atTop (𝓝 0)) :
    Tendsto (fun n =>
      (∫ ω, cavityWeightedReplicaMean (ν n ω)
        (fun x => w n (ω, x)) (fun σ => F n (ω, σ)) ∂P n) -
      ∫ ω, cavityWeightedReplicaMean (ρ n ω)
        (fun x => v n (ω, x)) (fun σ => G n (ω, σ)) ∂Q n) atTop (𝓝 0) := by
  apply cavity_moving_unregularized_ratio P Q
    (fun n ω => cavityWeightNormalizer (ν n ω) (fun x => w n (ω, x)))
    (fun n ω => cavityWeightNumerator (ν n ω) (fun x => w n (ω, x)) (fun σ => F n (ω, σ)))
    (fun n ω => cavityWeightNormalizer (ρ n ω) (fun x => v n (ω, x)))
    (fun n ω => cavityWeightNumerator (ρ n ω) (fun x => v n (ω, x)) (fun σ => G n (ω, σ)))
    (fun n => measurable_cavityWeightNormalizer (ν n) (hν n) (w n) (hw n))
    (fun n => measurable_cavityWeightNumerator (ν n) (hν n) (w n) (hw n) (F n) (hF n))
    (fun n => measurable_cavityWeightNormalizer (ρ n) (hρ n) (v n) (hv n))
    (fun n => measurable_cavityWeightNumerator (ρ n) (hρ n) (v n) (hv n) (G n) (hG n))
    hM hK hB r hZ0 hW0
    (fun n ω => (cavityWeightNormalizer_mem (ν n ω) _ ((hw n).comp measurable_prodMk_left)
      le_rfl (hwb n ω)).2)
    (fun n ω => (cavityWeightNormalizer_mem (ρ n ω) _ ((hv n).comp measurable_prodMk_left)
      le_rfl (hvb n ω)).2)
    (fun n ω => cavityWeightNumerator_abs_le_normalizer (ν n ω) _
      ((hw n).comp measurable_prodMk_left) _ ((hF n).comp measurable_prodMk_left)
      (zero_le_one.trans hM) hB (hwb n ω) (hFb n ω))
    (fun n ω => cavityWeightNumerator_abs_le_normalizer (ρ n ω) _
      ((hv n).comp measurable_prodMk_left) _ ((hG n).comp measurable_prodMk_left)
      (zero_le_one.trans hM) hB (hvb n ω) (hGb n ω))
    hiZ hiW hKZ hKW
  intro δ hδ
  exact cavity_moving_regularized_reweighted_test P Q ν hν ρ hρ w hw v hv F hF G hG
    hδ (zero_le_one.trans hM) hB hwb hvb hFb hGb hmom

end InvariantIsing

end

end OAI
