import OAI.Probability.InvariantIsing.Cavity.CavityRegularizedMoments
import OAI.Probability.InvariantIsing.Cavity.CavityBoundedReweighting

namespace OAI

/-! Extra-replica limits for bounded nonnegative factors, with the
normalizer regularized before any cutoff is removed. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology

namespace InvariantIsing

def cavityRegularizedReplicaMean {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (w : X → ℝ) {r : ℕ} (F : (Fin r → X) → ℝ) (δ : ℝ) : ℝ :=
  cavityWeightNumerator ν w F / (cavityWeightNormalizer ν w + δ) ^ r

theorem cavity_regularized_reweighted_test_tendsto
    {Ω X : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (X n)]
    {Ω₀ X₀ : Type*} [MeasurableSpace Ω₀] [MeasurableSpace X₀]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Q : Measure Ω₀) [IsProbabilityMeasure Q]
    (ν : (n : ℕ) → Ω n → Measure (X n)) (hν : ∀ n, Measurable (ν n))
    [∀ n ω, IsProbabilityMeasure (ν n ω)]
    (ρ : Ω₀ → Measure X₀) (hρ : Measurable ρ) [∀ ω, IsProbabilityMeasure (ρ ω)]
    (w : (n : ℕ) → Ω n × X n → ℝ) (hw : ∀ n, Measurable (w n))
    (v : Ω₀ × X₀ → ℝ) (hv : Measurable v) {r : ℕ}
    (F : (n : ℕ) → Ω n × (Fin r → X n) → ℝ) (hF : ∀ n, Measurable (F n))
    (G : Ω₀ × (Fin r → X₀) → ℝ) (hG : Measurable G)
    {δ M B : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hwb : ∀ n ω x, w n (ω, x) ∈ Icc 0 M) (hvb : ∀ ω x, v (ω, x) ∈ Icc 0 M)
    (hFb : ∀ n ω σ, |F n (ω, σ)| ≤ B) (hGb : ∀ ω σ, |G (ω, σ)| ≤ B)
    (hmom : ∀ k : ℕ, Tendsto
      (fun n => ∫ ω, ∫ ξ : (Fin r ⊕ Fin k) → X n,
        (∏ i, w n (ω, ξ i)) * F n (ω, fun i => ξ (.inl i))
          ∂Measure.pi (fun _ => ν n ω) ∂P n) atTop
      (𝓝 (∫ ω, ∫ ξ : (Fin r ⊕ Fin k) → X₀,
        (∏ i, v (ω, ξ i)) * G (ω, fun i => ξ (.inl i))
          ∂Measure.pi (fun _ => ρ ω) ∂Q))) :
    Tendsto (fun n => ∫ ω, cavityRegularizedReplicaMean (ν n ω)
        (fun x => w n (ω, x)) (fun σ => F n (ω, σ)) δ ∂P n) atTop
      (𝓝 (∫ ω, cavityRegularizedReplicaMean (ρ ω)
        (fun x => v (ω, x)) (fun σ => G (ω, σ)) δ ∂Q)) := by
  have hwabs n ω x : |w n (ω, x)| ≤ M := by
    rw [abs_of_nonneg (hwb n ω x).1]
    exact (hwb n ω x).2
  have hvabs ω x : |v (ω, x)| ≤ M := by
    rw [abs_of_nonneg (hvb ω x).1]
    exact (hvb ω x).2
  have hmixed k : Tendsto (fun n => ∫ ω,
      cavityWeightNumerator (ν n ω) (fun x => w n (ω, x)) (fun σ => F n (ω, σ)) *
        cavityWeightNormalizer (ν n ω) (fun x => w n (ω, x)) ^ k ∂P n) atTop
      (𝓝 (∫ ω, cavityWeightNumerator (ρ ω) (fun x => v (ω, x)) (fun σ => G (ω, σ)) *
        cavityWeightNormalizer (ρ ω) (fun x => v (ω, x)) ^ k ∂Q)) := by
    have hp n ω := cavityWeightNumerator_mul_normalizer (ν n ω) (fun x => w n (ω, x))
      (fun σ => F n (ω, σ)) ((hw n).comp measurable_prodMk_left)
      ((hF n).comp measurable_prodMk_left) k
    have hq ω := cavityWeightNumerator_mul_normalizer (ρ ω) (fun x => v (ω, x))
      (fun σ => G (ω, σ)) (hv.comp measurable_prodMk_left) (hG.comp measurable_prodMk_left) k
    simpa only [hp, hq] using hmom k
  exact cavity_regularized_reciprocal_tendsto P Q _ _ _ _
    (fun n => measurable_cavityWeightNormalizer (ν n) (hν n) (w n) (hw n))
    (fun n => measurable_cavityWeightNumerator (ν n) (hν n) (w n) (hw n) (F n) (hF n))
    (measurable_cavityWeightNormalizer ρ hρ v hv)
    (measurable_cavityWeightNumerator ρ hρ v hv G hG) hδ (mul_nonneg hB (pow_nonneg hM r))
    (fun n ω => cavityWeightNormalizer_mem (ν n ω) _ ((hw n).comp measurable_prodMk_left)
      le_rfl (hwb n ω))
    (fun ω => cavityWeightNormalizer_mem (ρ ω) _ (hv.comp measurable_prodMk_left) le_rfl (hvb ω))
    (fun n ω => cavityWeightNumerator_abs_le (ν n ω) _ _ hM hB (hwabs n ω) (hFb n ω))
    (fun ω => cavityWeightNumerator_abs_le (ρ ω) _ _ hM hB (hvabs ω) (hGb ω)) hmixed r

theorem cavity_floored_log_normalizer_tendsto
    {Ω X : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (X n)]
    {Ω₀ X₀ : Type*} [MeasurableSpace Ω₀] [MeasurableSpace X₀]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Q : Measure Ω₀) [IsProbabilityMeasure Q]
    (ν : (n : ℕ) → Ω n → Measure (X n)) (hν : ∀ n, Measurable (ν n))
    [∀ n ω, IsProbabilityMeasure (ν n ω)]
    (ρ : Ω₀ → Measure X₀) (hρ : Measurable ρ) [∀ ω, IsProbabilityMeasure (ρ ω)]
    (w : (n : ℕ) → Ω n × X n → ℝ) (hw : ∀ n, Measurable (w n))
    (v : Ω₀ × X₀ → ℝ) (hv : Measurable v) {δ M : ℝ} (hδ : 0 < δ)
    (hwb : ∀ n ω x, w n (ω, x) ∈ Icc 0 M) (hvb : ∀ ω x, v (ω, x) ∈ Icc 0 M)
    (hmom : ∀ k : ℕ, Tendsto
      (fun n => ∫ ω, ∫ ξ : Fin k → X n, (∏ i, w n (ω, ξ i))
        ∂Measure.pi (fun _ => ν n ω) ∂P n) atTop
      (𝓝 (∫ ω, ∫ ξ : Fin k → X₀, (∏ i, v (ω, ξ i))
        ∂Measure.pi (fun _ => ρ ω) ∂Q))) :
    Tendsto (fun n => ∫ ω, Real.log (cavityWeightNormalizer (ν n ω) (fun x => w n (ω, x)) + δ)
      ∂P n) atTop
      (𝓝 (∫ ω, Real.log (cavityWeightNormalizer (ρ ω) (fun x => v (ω, x)) + δ) ∂Q)) := by
  have hp k n ω : (cavityWeightNormalizer (ν n ω) (fun x => w n (ω, x))) ^ k =
      ∫ ξ : Fin k → X n, (∏ i, w n (ω, ξ i)) ∂Measure.pi (fun _ => ν n ω) := by
    simpa only [cavityWeightNormalizer, Fintype.card_fin] using
      (integral_fintype_prod_eq_pow (ι := Fin k) (μ := ν n ω) (fun x => w n (ω, x))).symm
  have hq k ω : (cavityWeightNormalizer (ρ ω) (fun x => v (ω, x))) ^ k =
      ∫ ξ : Fin k → X₀, (∏ i, v (ω, ξ i)) ∂Measure.pi (fun _ => ρ ω) := by
    simpa only [cavityWeightNormalizer, Fintype.card_fin] using
      (integral_fintype_prod_eq_pow (ι := Fin k) (μ := ρ ω) (fun x => v (ω, x))).symm
  exact cavity_floored_log_tendsto P Q _ _
    (fun n => measurable_cavityWeightNormalizer (ν n) (hν n) (w n) (hw n))
    (measurable_cavityWeightNormalizer ρ hρ v hv) hδ
    (fun n ω => cavityWeightNormalizer_mem (ν n ω) _ ((hw n).comp measurable_prodMk_left)
      le_rfl (hwb n ω))
    (fun ω => cavityWeightNormalizer_mem (ρ ω) _ (hv.comp measurable_prodMk_left) le_rfl (hvb ω))
    (fun k => by simpa only [hp, hq] using hmom k)

end InvariantIsing

end

end OAI
