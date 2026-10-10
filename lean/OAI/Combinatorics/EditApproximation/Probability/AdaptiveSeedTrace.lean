import OAI.Combinatorics.EditApproximation.Probability.AdaptiveSeedLaw

namespace OAI

/-! Preserve the finite draw history of adaptive seed passes. The final
seed has exactly the existing sequential law, while the history remains
available to the lazy evaluator when it asks for an earlier pass. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

def AdaptiveSeedTrace (Seed : Type) (Draw : ℕ → Seed → Type) : ℕ → Type
  | 0 => Seed
  | pass + 1 => AdaptiveSeedTrace Seed Draw pass × (∀ seed, Draw pass seed)

instance adaptiveSeedTraceFintype (Seed : Type) (Draw : ℕ → Seed → Type)
    [Fintype Seed] [DecidableEq Seed] [∀ pass seed, Fintype (Draw pass seed)] :
    (pass : ℕ) → Fintype (AdaptiveSeedTrace Seed Draw pass)
  | 0 => inferInstanceAs (Fintype Seed)
  | pass + 1 =>
    letI := adaptiveSeedTraceFintype Seed Draw pass
    inferInstanceAs (Fintype (AdaptiveSeedTrace Seed Draw pass × (∀ seed, Draw pass seed)))

instance adaptiveSeedTraceMeasurable (Seed : Type) (Draw : ℕ → Seed → Type)
    [MeasurableSpace Seed] [∀ pass seed, MeasurableSpace (Draw pass seed)] :
    (pass : ℕ) → MeasurableSpace (AdaptiveSeedTrace Seed Draw pass)
  | 0 => inferInstanceAs (MeasurableSpace Seed)
  | pass + 1 =>
    letI := adaptiveSeedTraceMeasurable Seed Draw pass
    inferInstanceAs (MeasurableSpace (AdaptiveSeedTrace Seed Draw pass × (∀ seed, Draw pass seed)))

instance adaptiveSeedTraceSingleton (Seed : Type) (Draw : ℕ → Seed → Type)
    [MeasurableSpace Seed] [MeasurableSingletonClass Seed]
    [∀ pass seed, MeasurableSpace (Draw pass seed)] [∀ pass seed, MeasurableSingletonClass (Draw pass seed)]
    [Fintype Seed] : (pass : ℕ) → MeasurableSingletonClass (AdaptiveSeedTrace Seed Draw pass)
  | 0 => inferInstanceAs (MeasurableSingletonClass Seed)
  | pass + 1 =>
    letI := adaptiveSeedTraceSingleton Seed Draw pass
    inferInstanceAs (MeasurableSingletonClass (AdaptiveSeedTrace Seed Draw pass × (∀ seed, Draw pass seed)))

section Trace

variable {Seed : Type} [Fintype Seed] [DecidableEq Seed]
  [MeasurableSpace Seed] [MeasurableSingletonClass Seed]
  {Draw : ℕ → Seed → Type} [∀ pass seed, Fintype (Draw pass seed)]
  [∀ pass seed, MeasurableSpace (Draw pass seed)]
  [∀ pass seed, MeasurableSingletonClass (Draw pass seed)]
  (drawLaw : ∀ pass seed, Measure (Draw pass seed))
  [∀ pass seed, IsProbabilityMeasure (drawLaw pass seed)]
  (incoming : Measure Seed) [IsProbabilityMeasure incoming]
  (next : ∀ pass seed, Draw pass seed → Seed)

def adaptiveTraceValue : (pass : ℕ) → AdaptiveSeedTrace Seed Draw pass → Seed
  | 0, seed => seed
  | pass + 1, trace =>
    let seed := adaptiveTraceValue pass trace.1
    next pass seed (trace.2 seed)

noncomputable def adaptiveTraceLaw : (pass : ℕ) → Measure (AdaptiveSeedTrace Seed Draw pass)
  | 0 => incoming
  | pass + 1 => (adaptiveTraceLaw pass).prod (Measure.pi (drawLaw pass))

instance adaptiveTraceLaw_probability (pass : ℕ) :
    IsProbabilityMeasure (adaptiveTraceLaw drawLaw incoming pass) := by
  induction pass with
  | zero => exact inferInstanceAs (IsProbabilityMeasure incoming)
  | succ pass ih =>
    have := ih
    exact inferInstanceAs (IsProbabilityMeasure
      ((adaptiveTraceLaw drawLaw incoming pass).prod (Measure.pi (drawLaw pass))))

omit [∀ pass seed, IsProbabilityMeasure (drawLaw pass seed)] [IsProbabilityMeasure incoming] in
theorem adaptiveTraceLaw_map (pass : ℕ) :
    (adaptiveTraceLaw drawLaw incoming pass).map (adaptiveTraceValue next pass) =
      adaptiveSeedSequence drawLaw incoming next pass := by
  induction pass with
  | zero => exact Measure.map_id
  | succ pass ih =>
    let reindex : AdaptiveSeedTrace Seed Draw pass × (∀ seed, Draw pass seed) →
        Seed × (∀ seed, Draw pass seed) := Prod.map (adaptiveTraceValue next pass) id
    have hvalue : adaptiveTraceValue next (pass + 1) = adaptiveSeedStep (next pass) ∘ reindex := rfl
    have hproduct : ((adaptiveTraceLaw drawLaw incoming pass).prod (Measure.pi (drawLaw pass))).map reindex =
        ((adaptiveTraceLaw drawLaw incoming pass).map (adaptiveTraceValue next pass)).prod
          (Measure.pi (drawLaw pass)) := by
      simpa only [Measure.map_id] using
        (Measure.map_prod_map (adaptiveTraceLaw drawLaw incoming pass) (Measure.pi (drawLaw pass))
          (measurable_of_finite (adaptiveTraceValue next pass)) measurable_id).symm
    change ((adaptiveTraceLaw drawLaw incoming pass).prod (Measure.pi (drawLaw pass))).map _ = _
    rw [hvalue, ← Measure.map_map (measurable_of_finite _) (measurable_of_finite _), hproduct, ih]
    rfl

end Trace

end EditApproximation

end OAI
