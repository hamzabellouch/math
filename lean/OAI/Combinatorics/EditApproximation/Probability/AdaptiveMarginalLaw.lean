import OAI.Combinatorics.EditApproximation.Probability.AdaptiveSeedLaw

namespace OAI

/-! Adaptive passes need the correct marginal for the actual incoming
seed. Independence between unused, counterfactual seed-indexed draws is
unnecessary. This permits one common keyed random source. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Marginal

variable {Seed : Type*} [Fintype Seed] [DecidableEq Seed]
  [MeasurableSpace Seed] [MeasurableSingletonClass Seed]
  {Draw : Seed → Type*} [∀ seed, Fintype (Draw seed)]
  [∀ seed, MeasurableSpace (Draw seed)] [∀ seed, MeasurableSingletonClass (Draw seed)]
  (drawLaw : ∀ seed, Measure (Draw seed)) [∀ seed, IsProbabilityMeasure (drawLaw seed)]
  {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  (randomLaw : Measure Ω) [IsProbabilityMeasure randomLaw]
  (sample : ∀ seed, Ω → Draw seed)
  (hmarginal : ∀ seed, randomLaw.map (sample seed) = drawLaw seed)

include hmarginal in
/-- The common random source can correlate draws for distinct hypothetical
incoming seeds; only its independence from the actual incoming seed matters. -/
theorem adaptiveSeedLaw_eq_of_marginals (incoming : Measure Seed) [IsProbabilityMeasure incoming]
    (next : ∀ seed, Draw seed → Seed) :
    (incoming.prod randomLaw).map
        (fun pair : Seed × Ω => next pair.1 (sample pair.1 pair.2)) =
      adaptiveSeedLaw drawLaw incoming next := by
  classical
  apply Measure.ext
  intro event hevent
  apply (measureReal_eq_measureReal_iff).mp
  rw [adaptiveSeedLaw, map_measureReal_apply (measurable_of_finite _) hevent,
    map_measureReal_apply (measurable_of_finite _) hevent]
  change (incoming.prod randomLaw).real
      {pair : Seed × Ω | next pair.1 (sample pair.1 pair.2) ∈ event} =
    (incoming.prod (Measure.pi drawLaw)).real
      {pair : Seed × (∀ seed, Draw seed) | next pair.1 (pair.2 pair.1) ∈ event}
  rw [← finite_integral_test (incoming.prod randomLaw)
      (fun pair : Seed × Ω => next pair.1 (sample pair.1 pair.2) ∈ event),
    ← finite_integral_test (incoming.prod (Measure.pi drawLaw))
      (fun pair : Seed × (∀ seed, Draw seed) => next pair.1 (pair.2 pair.1) ∈ event)]
  rw [integral_prod _ (.of_finite), integral_prod _ (.of_finite)]
  apply integral_congr_ae
  filter_upwards [] with seed
  have hmap := integral_map (μ := randomLaw) (φ := sample seed)
    (measurable_of_finite _).aemeasurable
    (f := fun draw => if next seed draw ∈ event then (1 : ℝ) else 0)
    (measurable_of_finite _).aestronglyMeasurable
  rw [hmarginal seed] at hmap
  rw [← hmap]
  symm
  exact integral_comp_eval (μ := drawLaw) (i := seed)
    (f := fun draw => if next seed draw ∈ event then (1 : ℝ) else 0)
    (measurable_of_finite _).aestronglyMeasurable

include hmarginal in
/-- The same replacement preserves the final integer answer law, rather
than only a seed transition. -/
theorem adaptiveAnswerLaw_eq_of_marginals (incoming : Measure Seed) [IsProbabilityMeasure incoming]
    (answer : ∀ seed, Draw seed → ℕ) :
    (incoming.prod randomLaw).map
        (fun pair : Seed × Ω => answer pair.1 (sample pair.1 pair.2)) =
      (incoming.prod (Measure.pi drawLaw)).map
        (fun pair : Seed × (∀ seed, Draw seed) => answer pair.1 (pair.2 pair.1)) := by
  classical
  apply Measure.ext
  intro event hevent
  apply (measureReal_eq_measureReal_iff).mp
  rw [map_measureReal_apply (measurable_of_finite _) hevent,
    map_measureReal_apply (measurable_of_finite _) hevent]
  change (incoming.prod randomLaw).real
      {pair : Seed × Ω | answer pair.1 (sample pair.1 pair.2) ∈ event} =
    (incoming.prod (Measure.pi drawLaw)).real
      {pair : Seed × (∀ seed, Draw seed) | answer pair.1 (pair.2 pair.1) ∈ event}
  rw [← finite_integral_test (incoming.prod randomLaw)
      (fun pair : Seed × Ω => answer pair.1 (sample pair.1 pair.2) ∈ event),
    ← finite_integral_test (incoming.prod (Measure.pi drawLaw))
      (fun pair : Seed × (∀ seed, Draw seed) => answer pair.1 (pair.2 pair.1) ∈ event)]
  rw [integral_prod _ (.of_finite), integral_prod _ (.of_finite)]
  apply integral_congr_ae
  filter_upwards [] with seed
  have hmap := integral_map (μ := randomLaw) (φ := sample seed)
    (measurable_of_finite _).aemeasurable
    (f := fun draw => if answer seed draw ∈ event then (1 : ℝ) else 0)
    (measurable_of_finite _).aestronglyMeasurable
  rw [hmarginal seed] at hmap
  rw [← hmap]
  symm
  exact integral_comp_eval (μ := drawLaw) (i := seed)
    (f := fun draw => if answer seed draw ∈ event then (1 : ℝ) else 0)
    (measurable_of_finite _).aestronglyMeasurable

end Marginal

end EditApproximation

end OAI
