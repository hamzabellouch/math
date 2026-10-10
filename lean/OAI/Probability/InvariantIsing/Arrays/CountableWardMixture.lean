import OAI.Probability.InvariantIsing.Arrays.CountableWardFunctional

namespace OAI

/-! Uniform fixed-prior Ward bounds survive a measurable mixture of
countable reference measures. -/

noncomputable section

open MeasureTheory IsingPerceptron

namespace InvariantIsing

lemma measurable_mixtureReplicaMean {T Ω X : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ν : T → Measure X) [∀ t, IsProbabilityMeasure (ν t)] (hν : Measurable ν)
    (H : Ω × X → ℝ) (hH : Measurable H) {r : ℕ}
    (D : Ω × (Fin r → X) → ℝ) (hD : Measurable D) :
    Measurable (fun p : T × Ω =>
      referenceReplicaMean (ν p.1) (fun x => H (p.2,x)) (fun σ => D (p.2,σ))) := by
  have : ∀ p : T × Ω, IsProbabilityMeasure ((ν ∘ Prod.fst) p) := fun p => by
    change IsProbabilityMeasure (ν p.1)
    infer_instance
  exact measurable_random_referenceReplicaMean (hν.comp measurable_fst)
    (hH.comp (measurable_fst.snd.prodMk measurable_snd))
    (hD.comp (measurable_fst.snd.prodMk measurable_snd))

lemma measurable_integral_mixtureReplicaMean {T Ω X : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (P : Measure Ω) [SFinite P]
    (ν : T → Measure X) [∀ t, IsProbabilityMeasure (ν t)] (hν : Measurable ν)
    (H : Ω × X → ℝ) (hH : Measurable H) {r : ℕ}
    (D : Ω × (Fin r → X) → ℝ) (hD : Measurable D) :
    Measurable (fun t => ∫ ω,
      referenceReplicaMean (ν t) (fun x => H (ω,x)) (fun σ => D (ω,σ)) ∂P) :=
  (measurable_mixtureReplicaMean ν hν H hH D hD).stronglyMeasurable.integral_prod_right'.measurable

lemma integrable_mixtureReplicaMean {T Ω X : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ξ : Measure T) [IsProbabilityMeasure ξ] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : T → Measure X) [∀ t, IsProbabilityMeasure (ν t)] (hν : Measurable ν)
    (H : Ω × X → ℝ) (hH : Measurable H) {r : ℕ}
    (D : Ω × (Fin r → X) → ℝ) (hD : Measurable D)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ z, |D z| ≤ B) :
    Integrable (fun t => ∫ ω,
      referenceReplicaMean (ν t) (fun x => H (ω,x)) (fun σ => D (ω,σ)) ∂P) ξ := by
  have hm := measurable_integral_mixtureReplicaMean P ν hν H hH D hD
  apply integrable_of_measurable_abs_le (c := B) hm
  intro t
  apply abs_integral_le_const_of_bound (c := B)
    ((measurable_mixtureReplicaMean ν hν H hH D hD).comp (measurable_const.prodMk measurable_id))
  intro ω
  change |referenceReplicaMean (ν t) (fun x => H (ω,x)) (fun σ => D (ω,σ))| ≤ B
  exact referenceReplicaMean_abs_le (ν t) _ _ (measurable_of_countable _) hB (fun σ => hb (ω,σ))

 theorem expectedReplicaWard_mixture_abs_le {T Ω X : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ξ : Measure T) [IsProbabilityMeasure ξ] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : T → Measure X) [∀ t, IsProbabilityMeasure (ν t)] (hν : Measurable ν)
    (H : Ω × X → ℝ) (hH : Measurable H)
    (D₂ : Ω × (Fin 2 → X) → ℝ) (hD₂ : Measurable D₂)
    (D₃ : Ω × (Fin 3 → X) → ℝ) (hD₃ : Measurable D₃)
    {B₂ B₃ : ℝ} (hB₂ : 0 ≤ B₂) (hB₃ : 0 ≤ B₃)
    (hb₂ : ∀ z, |D₂ z| ≤ B₂) (hb₃ : ∀ z, |D₃ z| ≤ B₃)
    {ε : ℝ} (hward : ∀ t, |expectedReplicaWard P (ν t) H D₂ D₃| ≤ ε) :
    |(∫ t, (∫ ω, referenceReplicaMean (ν t) (fun x => H (ω,x)) (fun σ => D₂ (ω,σ)) ∂P) ∂ ξ) -
      2 * (∫ t, (∫ ω, referenceReplicaMean (ν t) (fun x => H (ω,x)) (fun σ => D₃ (ω,σ)) ∂P) ∂ ξ)| ≤ ε := by
  have hi₂ := integrable_mixtureReplicaMean ξ P ν hν H hH D₂ hD₂ hB₂ hb₂
  have hi₃ := integrable_mixtureReplicaMean ξ P ν hν H hH D₃ hD₃ hB₃ hb₃
  rw [← integral_const_mul, ← integral_sub hi₂ (hi₃.const_mul 2)]
  apply abs_integral_le_const_of_bound
    ((measurable_integral_mixtureReplicaMean P ν hν H hH D₂ hD₂).sub
      ((measurable_integral_mixtureReplicaMean P ν hν H hH D₃ hD₃).const_mul 2))
  exact hward

end InvariantIsing

end

end OAI
