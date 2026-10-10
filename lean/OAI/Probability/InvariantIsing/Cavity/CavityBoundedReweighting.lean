import OAI.Probability.InvariantIsing.Cavity.CavityExtraReplicas
import OAI.Probability.IsingPerceptron.RetainedDisplacement

namespace OAI

/-! Bounded positive reweighting of random probability priors.  Its
replica-test limit follows from the unreweighted extra-replica limits. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology

namespace InvariantIsing

def cavityWeightNormalizer {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (w : X → ℝ) : ℝ := ∫ x, w x ∂ν

def cavityWeightNumerator {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (w : X → ℝ) {r : ℕ} (F : (Fin r → X) → ℝ) : ℝ :=
  ∫ σ : Fin r → X, (∏ i, w (σ i)) * F σ ∂Measure.pi (fun _ => ν)

def cavityWeightedReplicaMean {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (w : X → ℝ) {r : ℕ} (F : (Fin r → X) → ℝ) : ℝ :=
  cavityWeightNumerator ν w F / cavityWeightNormalizer ν w ^ r

lemma measurable_cavityWeightNormalizer {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (w : Ω × X → ℝ) (hw : Measurable w) :
    Measurable (fun ω => cavityWeightNormalizer (ν ω) (fun x => w (ω, x))) := by
  let κ : Kernel Ω X := ⟨ν, hν⟩
  let : IsMarkovKernel κ := ⟨fun ω => inferInstanceAs (IsProbabilityMeasure (ν ω))⟩
  exact (hw.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable

lemma measurable_cavityWeightNumerator {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (w : Ω × X → ℝ) (hw : Measurable w) {r : ℕ}
    (F : Ω × (Fin r → X) → ℝ) (hF : Measurable F) :
    Measurable (fun ω => cavityWeightNumerator (ν ω) (fun x => w (ω, x)) (fun σ => F (ω, σ))) := by
  let κ : Kernel Ω (Fin r → X) :=
    ⟨fun ω => Measure.pi (fun _ : Fin r => ν ω), measurable_probability_pi hν⟩
  let : IsMarkovKernel κ := ⟨fun ω =>
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin r => ν ω)))⟩
  have hm : Measurable (fun p : Ω × (Fin r → X) => (∏ i, w (p.1, p.2 i)) * F p) :=
    (Finset.measurable_prod _ fun i _ => hw.comp
      (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))).mul hF
  exact (hm.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable

lemma cavityWeightNormalizer_mem {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (w : X → ℝ) (hw : Measurable w)
    {a b : ℝ} (ha : 0 ≤ a) (hwb : ∀ x, w x ∈ Icc a b) :
    cavityWeightNormalizer ν w ∈ Icc a b := by
  have hi : Integrable w ν := Integrable.of_bound hw.aestronglyMeasurable b
    (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (ha.trans (hwb x).1)]
      exact (hwb x).2)
  constructor
  · simpa only [cavityWeightNormalizer, integral_const, probReal_univ, one_smul] using
      integral_mono (integrable_const a) hi (fun x => (hwb x).1)
  · simpa only [cavityWeightNormalizer, integral_const, probReal_univ, one_smul] using
      integral_mono hi (integrable_const b) (fun x => (hwb x).2)

lemma cavityWeightNumerator_abs_le {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (w : X → ℝ) {r : ℕ}
    (F : (Fin r → X) → ℝ) {M B : ℝ} (hM : 0 ≤ M) (_hB : 0 ≤ B)
    (hw : ∀ x, |w x| ≤ M) (hF : ∀ σ, |F σ| ≤ B) :
    |cavityWeightNumerator ν w F| ≤ B * M ^ r := by
  have hp (σ : Fin r → X) : |∏ i, w (σ i)| ≤ M ^ r := by
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ _ : Fin r, M := Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
        (fun i _ => hw (σ i))
      _ = _ := by simp
  have ht := norm_integral_le_of_norm_le_const
    (μ := Measure.pi (fun _ : Fin r => ν))
    (f := fun σ => (∏ i, w (σ i)) * F σ) (C := B * M ^ r)
    (ae_of_all _ fun σ => by
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul (hp σ) (hF σ) (abs_nonneg _) (pow_nonneg hM r)).trans_eq (mul_comm _ _))
  simpa only [cavityWeightNumerator, Real.norm_eq_abs, probReal_univ, mul_one] using ht

lemma cavityWeightNumerator_mul_normalizer {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν]
    (w : X → ℝ) {r : ℕ} (F : (Fin r → X) → ℝ) (hw : Measurable w) (hF : Measurable F) (k : ℕ) :
    cavityWeightNumerator ν w F * cavityWeightNormalizer ν w ^ k =
      ∫ ξ : (Fin r ⊕ Fin k) → X, (∏ i, w (ξ i)) * F (fun i => ξ (.inl i))
        ∂Measure.pi (fun _ => ν) := cavity_extra_replica_identity ν w F hw hF k

theorem cavity_bounded_reweighted_test_tendsto
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
    (hwb : ∀ n ω x, w n (ω, x) ∈ Icc δ M) (hvb : ∀ ω x, v (ω, x) ∈ Icc δ M)
    (hFb : ∀ n ω σ, |F n (ω, σ)| ≤ B) (hGb : ∀ ω σ, |G (ω, σ)| ≤ B)
    (hmom : ∀ k : ℕ, Tendsto
      (fun n => ∫ ω, ∫ ξ : (Fin r ⊕ Fin k) → X n,
        (∏ i, w n (ω, ξ i)) * F n (ω, fun i => ξ (.inl i))
          ∂Measure.pi (fun _ => ν n ω) ∂P n) atTop
      (𝓝 (∫ ω, ∫ ξ : (Fin r ⊕ Fin k) → X₀,
        (∏ i, v (ω, ξ i)) * G (ω, fun i => ξ (.inl i))
          ∂Measure.pi (fun _ => ρ ω) ∂Q))) :
    Tendsto (fun n => ∫ ω, cavityWeightedReplicaMean (ν n ω)
        (fun x => w n (ω, x)) (fun σ => F n (ω, σ)) ∂P n) atTop
      (𝓝 (∫ ω, cavityWeightedReplicaMean (ρ ω)
        (fun x => v (ω, x)) (fun σ => G (ω, σ)) ∂Q)) := by
  have hwabs n ω x : |w n (ω, x)| ≤ M := by
    rw [abs_of_pos (hδ.trans_le (hwb n ω x).1)]
    exact (hwb n ω x).2
  have hvabs ω x : |v (ω, x)| ≤ M := by
    rw [abs_of_pos (hδ.trans_le (hvb ω x).1)]
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
  exact cavity_reciprocal_normalizer_tendsto P Q _ _ _ _
    (fun n => measurable_cavityWeightNormalizer (ν n) (hν n) (w n) (hw n))
    (fun n => measurable_cavityWeightNumerator (ν n) (hν n) (w n) (hw n) (F n) (hF n))
    (measurable_cavityWeightNormalizer ρ hρ v hv)
    (measurable_cavityWeightNumerator ρ hρ v hv G hG) hδ (mul_nonneg hB (pow_nonneg hM r))
    (fun n ω => cavityWeightNormalizer_mem (ν n ω) _ ((hw n).comp measurable_prodMk_left)
      hδ.le (hwb n ω))
    (fun ω => cavityWeightNormalizer_mem (ρ ω) _ (hv.comp measurable_prodMk_left) hδ.le (hvb ω))
    (fun n ω => cavityWeightNumerator_abs_le (ν n ω) _ _ hM hB (hwabs n ω) (hFb n ω))
    (fun ω => cavityWeightNumerator_abs_le (ρ ω) _ _ hM hB (hvabs ω) (hGb ω)) hmixed r

theorem cavity_bounded_log_normalizer_tendsto
    {Ω X : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (X n)]
    {Ω₀ X₀ : Type*} [MeasurableSpace Ω₀] [MeasurableSpace X₀]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Q : Measure Ω₀) [IsProbabilityMeasure Q]
    (ν : (n : ℕ) → Ω n → Measure (X n)) (hν : ∀ n, Measurable (ν n))
    [∀ n ω, IsProbabilityMeasure (ν n ω)]
    (ρ : Ω₀ → Measure X₀) (hρ : Measurable ρ) [∀ ω, IsProbabilityMeasure (ρ ω)]
    (w : (n : ℕ) → Ω n × X n → ℝ) (hw : ∀ n, Measurable (w n))
    (v : Ω₀ × X₀ → ℝ) (hv : Measurable v)
    {δ M : ℝ} (hδ : 0 < δ) (hδM : δ ≤ M)
    (hwb : ∀ n ω x, w n (ω, x) ∈ Icc δ M) (hvb : ∀ ω x, v (ω, x) ∈ Icc δ M)
    (hmom : ∀ k : ℕ, Tendsto
      (fun n => ∫ ω, ∫ ξ : Fin k → X n, ∏ i, w n (ω, ξ i)
        ∂Measure.pi (fun _ => ν n ω) ∂P n) atTop
      (𝓝 (∫ ω, ∫ ξ : Fin k → X₀, ∏ i, v (ω, ξ i)
        ∂Measure.pi (fun _ => ρ ω) ∂Q))) :
    Tendsto (fun n => ∫ ω, Real.log (cavityWeightNormalizer (ν n ω)
      (fun x => w n (ω, x))) ∂P n) atTop
      (𝓝 (∫ ω, Real.log (cavityWeightNormalizer (ρ ω) (fun x => v (ω, x))) ∂Q)) := by
  apply tendsto_integral_log_of_moments P Q _ _
    (fun n => measurable_cavityWeightNormalizer (ν n) (hν n) (w n) (hw n))
    (measurable_cavityWeightNormalizer ρ hρ v hv) hδ hδM
    (fun n ω => cavityWeightNormalizer_mem (ν n ω) _ ((hw n).comp measurable_prodMk_left)
      hδ.le (hwb n ω))
    (fun ω => cavityWeightNormalizer_mem (ρ ω) _ (hv.comp measurable_prodMk_left) hδ.le (hvb ω))
  intro k
  have hp n ω : (∫ ξ : Fin k → X n, ∏ i, w n (ω, ξ i)
      ∂Measure.pi (fun _ => ν n ω)) = cavityWeightNormalizer (ν n ω) (fun x => w n (ω, x)) ^ k := by
    simpa only [Fintype.card_fin, cavityWeightNormalizer] using
      integral_fintype_prod_eq_pow (ι := Fin k) (μ := ν n ω) (fun x => w n (ω, x))
  have hq ω : (∫ ξ : Fin k → X₀, ∏ i, v (ω, ξ i)
      ∂Measure.pi (fun _ => ρ ω)) = cavityWeightNormalizer (ρ ω) (fun x => v (ω, x)) ^ k := by
    simpa only [Fintype.card_fin, cavityWeightNormalizer] using
      integral_fintype_prod_eq_pow (ι := Fin k) (μ := ρ ω) (fun x => v (ω, x))
  simpa only [hp, hq] using hmom k

end InvariantIsing

end

end OAI
