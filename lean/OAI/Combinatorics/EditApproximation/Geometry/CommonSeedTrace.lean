import OAI.Combinatorics.EditApproximation.Probability.AdaptiveMarginalLaw

namespace OAI

/-! Adaptive seed passes driven by common per-pass random sources. The
trace stores one source for the actual pass, with no seed-indexed family.
Its returned seed has the original adaptive law. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

def CommonSeedTrace (Seed : Type) (Ω : ℕ → Type) : ℕ → Type
  | 0 => Seed
  | pass + 1 => CommonSeedTrace Seed Ω pass × Ω pass

instance commonSeedTraceFintype (Seed : Type) (Ω : ℕ → Type)
    [Fintype Seed] [∀ pass, Fintype (Ω pass)] : (pass : ℕ) → Fintype (CommonSeedTrace Seed Ω pass)
  | 0 => inferInstanceAs (Fintype Seed)
  | pass + 1 =>
    letI := commonSeedTraceFintype Seed Ω pass
    inferInstanceAs (Fintype (CommonSeedTrace Seed Ω pass × Ω pass))

instance commonSeedTraceMeasurable (Seed : Type) (Ω : ℕ → Type)
    [MeasurableSpace Seed] [∀ pass, MeasurableSpace (Ω pass)] :
    (pass : ℕ) → MeasurableSpace (CommonSeedTrace Seed Ω pass)
  | 0 => inferInstanceAs (MeasurableSpace Seed)
  | pass + 1 =>
    letI := commonSeedTraceMeasurable Seed Ω pass
    inferInstanceAs (MeasurableSpace (CommonSeedTrace Seed Ω pass × Ω pass))

instance commonSeedTraceSingleton (Seed : Type) (Ω : ℕ → Type)
    [MeasurableSpace Seed] [MeasurableSingletonClass Seed]
    [∀ pass, MeasurableSpace (Ω pass)] [∀ pass, MeasurableSingletonClass (Ω pass)] :
    (pass : ℕ) → MeasurableSingletonClass (CommonSeedTrace Seed Ω pass)
  | 0 => inferInstanceAs (MeasurableSingletonClass Seed)
  | pass + 1 =>
    letI := commonSeedTraceSingleton Seed Ω pass
    inferInstanceAs (MeasurableSingletonClass (CommonSeedTrace Seed Ω pass × Ω pass))

section Common

variable {Seed : Type} [Fintype Seed] [DecidableEq Seed]
  [MeasurableSpace Seed] [MeasurableSingletonClass Seed]
  {Draw : ℕ → Seed → Type} [∀ pass seed, Fintype (Draw pass seed)]
  [∀ pass seed, MeasurableSpace (Draw pass seed)]
  [∀ pass seed, MeasurableSingletonClass (Draw pass seed)]
  {Ω : ℕ → Type} [∀ pass, Fintype (Ω pass)]
  [∀ pass, MeasurableSpace (Ω pass)] [∀ pass, MeasurableSingletonClass (Ω pass)]
  (drawLaw : ∀ pass seed, Measure (Draw pass seed))
  [∀ pass seed, IsProbabilityMeasure (drawLaw pass seed)]
  (randomLaw : ∀ pass, Measure (Ω pass)) [∀ pass, IsProbabilityMeasure (randomLaw pass)]
  (sample : ∀ pass seed, Ω pass → Draw pass seed)
  (next : ∀ pass seed, Draw pass seed → Seed)

noncomputable def commonTraceValue : (pass : ℕ) → CommonSeedTrace Seed Ω pass → Seed
  | 0, seed => seed
  | pass + 1, trace =>
    let seed := commonTraceValue pass trace.1
    next pass seed (sample pass seed trace.2)

noncomputable def commonTraceLaw (incoming : Measure Seed) :
    (pass : ℕ) → Measure (CommonSeedTrace Seed Ω pass)
  | 0 => incoming
  | pass + 1 => (commonTraceLaw incoming pass).prod (randomLaw pass)

instance commonTraceLaw_probability (incoming : Measure Seed) [IsProbabilityMeasure incoming]
    (pass : ℕ) : IsProbabilityMeasure (commonTraceLaw randomLaw incoming pass) := by
  induction pass with
  | zero => exact inferInstanceAs (IsProbabilityMeasure incoming)
  | succ pass ih =>
    let := ih
    exact inferInstanceAs (IsProbabilityMeasure
      ((commonTraceLaw randomLaw incoming pass).prod (randomLaw pass)))

theorem commonTraceLaw_map (incoming : Measure Seed) [IsProbabilityMeasure incoming]
    (hmarginal : ∀ pass seed, (randomLaw pass).map (sample pass seed) = drawLaw pass seed)
    (passes : ℕ) :
    (commonTraceLaw randomLaw incoming passes).map (commonTraceValue sample next passes) =
      adaptiveSeedSequence drawLaw incoming next passes := by
  induction passes with
  | zero => exact Measure.map_id
  | succ pass ih =>
    let reindex : CommonSeedTrace Seed Ω pass × Ω pass → Seed × Ω pass :=
      Prod.map (commonTraceValue sample next pass) id
    let step : Seed × Ω pass → Seed := fun pair => next pass pair.1 (sample pass pair.1 pair.2)
    have hvalue : commonTraceValue sample next (pass + 1) = step ∘ reindex := rfl
    have hproduct : ((commonTraceLaw randomLaw incoming pass).prod (randomLaw pass)).map reindex =
        ((commonTraceLaw randomLaw incoming pass).map (commonTraceValue sample next pass)).prod
          (randomLaw pass) := by
      simpa only [Measure.map_id] using
        (Measure.map_prod_map (commonTraceLaw randomLaw incoming pass) (randomLaw pass)
          (measurable_of_finite (commonTraceValue sample next pass)) measurable_id).symm
    change ((commonTraceLaw randomLaw incoming pass).prod (randomLaw pass)).map _ = _
    rw [hvalue, ← Measure.map_map (measurable_of_finite _) (measurable_of_finite _), hproduct, ih]
    exact adaptiveSeedLaw_eq_of_marginals (drawLaw pass) (randomLaw pass) (sample pass)
      (hmarginal pass) (adaptiveSeedSequence drawLaw incoming next pass) (next pass)

end Common

end EditApproximation

end OAI
