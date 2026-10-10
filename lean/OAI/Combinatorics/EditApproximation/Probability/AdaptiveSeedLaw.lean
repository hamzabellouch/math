import OAI.Combinatorics.EditApproximation.Probability.FiniteResampling

namespace OAI

/-! Fresh streams indexed by every possible incoming seed make adaptive
seed-dependent draw types compatible with a single finite product law. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

theorem finite_integral_test {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) (test : Ω → Prop) [DecidablePred test] :
    (∫ ω, if test ω then (1 : ℝ) else 0 ∂μ) = μ.real {ω | test ω} := by
  have h := integral_indicator_one (μ := μ) (Set.toFinite {ω | test ω}).measurableSet
  simpa only [Set.indicator, Set.mem_ofPred_eq, Pi.one_apply] using h

section Step

variable {Seed : Type*} [Fintype Seed] [DecidableEq Seed]
  [MeasurableSpace Seed] [MeasurableSingletonClass Seed]
  {Draw : Seed → Type*} [∀ seed, Fintype (Draw seed)]
  [∀ seed, MeasurableSpace (Draw seed)] [∀ seed, MeasurableSingletonClass (Draw seed)]
  (drawLaw : ∀ seed, Measure (Draw seed)) [∀ seed, IsProbabilityMeasure (drawLaw seed)]

/-- Only the coordinate belonging to the actual incoming table is consumed.
All states within that coordinate retain their shared copy streams. -/
def adaptiveSeedStep (next : ∀ seed, Draw seed → Seed) (pair : Seed × (∀ seed, Draw seed)) : Seed :=
  next pair.1 (pair.2 pair.1)

noncomputable def adaptiveSeedLaw (incoming : Measure Seed) (next : ∀ seed, Draw seed → Seed) : Measure Seed :=
  (incoming.prod (Measure.pi drawLaw)).map (adaptiveSeedStep next)

instance adaptiveSeedLaw_probability (incoming : Measure Seed) [IsProbabilityMeasure incoming]
    (next : ∀ seed, Draw seed → Seed) : IsProbabilityMeasure (adaptiveSeedLaw drawLaw incoming next) := by
  unfold adaptiveSeedLaw
  infer_instance

theorem adaptiveSeedLaw_failure (incoming : Measure Seed) [IsProbabilityMeasure incoming]
    (next : ∀ seed, Draw seed → Seed) (good nextGood : Seed → Prop)
    [DecidablePred good] [DecidablePred nextGood] (q : ℝ) (hq : 0 ≤ q)
    (hstep : ∀ seed, good seed → (drawLaw seed).real {draw | ¬ nextGood (next seed draw)} ≤ q) :
    (adaptiveSeedLaw drawLaw incoming next).real {seed | ¬ nextGood seed} ≤
      incoming.real {seed | ¬ good seed} + q := by
  classical
  rw [adaptiveSeedLaw, map_measureReal_apply (measurable_of_finite _) (Set.toFinite _).measurableSet]
  change (incoming.prod (Measure.pi drawLaw)).real
    {pair : Seed × (∀ seed, Draw seed) | ¬ nextGood (next pair.1 (pair.2 pair.1))} ≤ _
  rw [← finite_integral_test (incoming.prod (Measure.pi drawLaw))
    (fun pair : Seed × (∀ seed, Draw seed) => ¬ nextGood (next pair.1 (pair.2 pair.1)))]
  change (∫ pair : Seed × (∀ seed, Draw seed),
    if ¬ nextGood (next pair.1 (pair.2 pair.1)) then (1 : ℝ) else 0
      ∂incoming.prod (Measure.pi drawLaw)) ≤ _
  rw [integral_prod _ (.of_finite)]
  have hinner (seed : Seed) :
      (∫ draws : ∀ seed, Draw seed, if ¬ nextGood (next seed (draws seed)) then (1 : ℝ) else 0
        ∂Measure.pi drawLaw) = (drawLaw seed).real {draw | ¬ nextGood (next seed draw)} := by
    rw [integral_comp_eval (μ := drawLaw) (i := seed)
      (f := fun draw => if ¬ nextGood (next seed draw) then (1 : ℝ) else 0)
      (measurable_of_finite _).aestronglyMeasurable]
    exact finite_integral_test _ _
  simp_rw [hinner]
  have hpoint (seed : Seed) : (drawLaw seed).real {draw | ¬ nextGood (next seed draw)} ≤
      (if ¬ good seed then (1 : ℝ) else 0) + q := by
    by_cases hg : good seed
    · simpa only [hg, not_true_eq_false, ite_false, zero_add] using hstep seed hg
    · have hprob : (drawLaw seed).real {draw | ¬ nextGood (next seed draw)} ≤ 1 := measureReal_le_one
      simpa only [hg, not_false_eq_true, ite_true] using hprob.trans (le_add_of_nonneg_right hq)
  have h := integral_mono (μ := incoming) (.of_finite) (.of_finite) hpoint
  rw [integral_add (.of_finite) (integrable_const _), finite_integral_test,
    integral_const, probReal_univ, one_smul] at h
  exact h

end Step

section Sequence

variable {Seed : Type*} [Fintype Seed] [DecidableEq Seed]
  [MeasurableSpace Seed] [MeasurableSingletonClass Seed]
  {Draw : ℕ → Seed → Type*} [∀ pass seed, Fintype (Draw pass seed)]
  [∀ pass seed, MeasurableSpace (Draw pass seed)]
  [∀ pass seed, MeasurableSingletonClass (Draw pass seed)]
  (drawLaw : ∀ pass seed, Measure (Draw pass seed))
  [∀ pass seed, IsProbabilityMeasure (drawLaw pass seed)]
  (incoming : Measure Seed) (next : ∀ pass seed, Draw pass seed → Seed)

noncomputable def adaptiveSeedSequence : ℕ → Measure Seed
  | 0 => incoming
  | pass + 1 => adaptiveSeedLaw (drawLaw pass) (adaptiveSeedSequence pass) (next pass)

instance adaptiveSeedSequence_probability [IsProbabilityMeasure incoming] (pass : ℕ) :
    IsProbabilityMeasure (adaptiveSeedSequence drawLaw incoming next pass) := by
  induction pass with
  | zero => exact inferInstanceAs (IsProbabilityMeasure incoming)
  | succ pass ih =>
    let := ih
    exact inferInstanceAs (IsProbabilityMeasure
      (adaptiveSeedLaw (drawLaw pass) (adaptiveSeedSequence drawLaw incoming next pass) (next pass)))

theorem adaptiveSeedSequence_failure [IsProbabilityMeasure incoming]
    (good : ℕ → Seed → Prop) [∀ pass, DecidablePred (good pass)]
    (q : ℕ → ℝ) (hq : ∀ pass, 0 ≤ q pass) (passes : ℕ)
    (hstep : ∀ pass < passes, ∀ seed, good pass seed →
      (drawLaw pass seed).real {draw | ¬ good (pass + 1) (next pass seed draw)} ≤ q pass) :
    (adaptiveSeedSequence drawLaw incoming next passes).real {seed | ¬ good passes seed} ≤
      incoming.real {seed | ¬ good 0 seed} + ∑ pass ∈ Finset.range passes, q pass := by
  induction passes with
  | zero => simp only [adaptiveSeedSequence, Finset.sum_range_zero, add_zero, le_refl]
  | succ passes ih =>
    have hprevious := ih (fun pass hp seed hg => hstep pass (by omega) seed hg)
    have hnext := adaptiveSeedLaw_failure (drawLaw passes)
      (adaptiveSeedSequence drawLaw incoming next passes) (next passes)
      (good passes) (good (passes + 1)) (q passes) (hq passes)
      (hstep passes (by omega))
    apply hnext.trans
    rw [Finset.sum_range_succ]
    linarith only [hprevious]

end Sequence

end EditApproximation

end OAI
