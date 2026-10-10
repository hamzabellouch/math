import OAI.Combinatorics.EditApproximation.Probability.AdaptiveSeedLaw
import OAI.Combinatorics.EditApproximation.Geometry.Accuracy

namespace OAI

/-! The final fresh draw selects the coordinate of the actual incoming seed.
This keeps the dependence of the finite draw type on that table explicit. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Final

variable {Seed : Type*} [Fintype Seed]
  [MeasurableSpace Seed] [MeasurableSingletonClass Seed]
  {Draw : Seed → Type*} [∀ seed, Finite (Draw seed)]
  [∀ seed, MeasurableSpace (Draw seed)] [∀ seed, MeasurableSingletonClass (Draw seed)]
  (drawLaw : ∀ seed, Measure (Draw seed)) [∀ seed, IsProbabilityMeasure (drawLaw seed)]
  (incoming : Measure Seed) [IsProbabilityMeasure incoming]

def freshSeedValue (value : ∀ seed, Draw seed → ℝ)
    (pair : Seed × (∀ seed, Draw seed)) : ℝ := value pair.1 (pair.2 pair.1)

theorem freshSeed_bad_probability (good : Seed → Prop) :
    (incoming.prod (Measure.pi drawLaw)).real
      {pair : Seed × (∀ seed, Draw seed) | ¬ good pair.1} = incoming.real {seed | ¬ good seed} := by
  classical
  let : Fintype (Seed × (∀ seed, Draw seed)) := Fintype.ofFinite _
  rw [← finite_integral_test (incoming.prod (Measure.pi drawLaw)) (fun pair => ¬ good pair.1)]
  rw [integral_prod _ (.of_finite)]
  change (∫ seed, (∫ _ : ∀ seed, Draw seed, if ¬ good seed then (1 : ℝ) else 0
    ∂Measure.pi drawLaw) ∂incoming) = _
  simp only [integral_const, probReal_univ, one_smul]
  exact finite_integral_test incoming (fun seed => ¬ good seed)

theorem freshSeed_good_excess (good : Seed → Prop) (value : ∀ seed, Draw seed → ℝ)
    (D : ℕ) (ell : ℝ) (hell : 0 < ell)
    (hmoment : ∀ seed, good seed →
      (∫ draw, max (value seed draw - D) 0 ∂drawLaw seed) ≤ (D : ℝ) / ell) :
    (∫ pair, goodExcess {pair : Seed × (∀ seed, Draw seed) | good pair.1}
      (freshSeedValue value) D pair ∂incoming.prod (Measure.pi drawLaw)) ≤ (D : ℝ) / ell := by
  classical
  rw [integral_prod _ (.of_finite)]
  have hinner (seed : Seed) :
      (∫ draws : ∀ seed, Draw seed,
        goodExcess {pair : Seed × (∀ seed, Draw seed) | good pair.1}
          (freshSeedValue value) D (seed, draws) ∂Measure.pi drawLaw) ≤ (D : ℝ) / ell := by
    by_cases hg : good seed
    · simp only [goodExcess, Set.indicator, Set.mem_ofPred_eq, hg, ite_true,
        freshSeedValue]
      rw [integral_comp_eval (μ := drawLaw) (i := seed)
        (f := fun draw => max (value seed draw - D) 0)
        (measurable_of_finite _).aestronglyMeasurable]
      exact hmoment seed hg
    · simp only [goodExcess, Set.indicator, Set.mem_ofPred_eq, hg, ite_false,
        integral_zero]
      exact div_nonneg (Nat.cast_nonneg _) hell.le
  have h := integral_mono (μ := incoming) (.of_finite) (integrable_const _) hinner
  simpa only [integral_const, probReal_univ, one_smul] using h

theorem freshSeed_answer_accuracy (good : Seed → Prop) (value : ∀ seed, Draw seed → ℝ)
    {N D : ℕ} {ell epsilon : ℝ} (hDN : D ≤ N) (hD : 0 < D)
    (hell : 0 < ell) (hepsilon : 0 < epsilon) (haccuracy : 10 ≤ ell * epsilon)
    (hseed : incoming.real {seed | ¬ good seed} ≤ 1 / 10)
    (hlower : ∀ seed, good seed → ∀ draw, (D : ℝ) ≤ value seed draw)
    (hmoment : ∀ seed, good seed →
      (∫ draw, max (value seed draw - D) 0 ∂drawLaw seed) ≤ (D : ℝ) / ell) :
    (4 / 5 : ℝ) ≤ (incoming.prod (Measure.pi drawLaw)).real
      {pair | D ≤ integerAnswer N (freshSeedValue value pair) ∧
        (integerAnswer N (freshSeedValue value pair) : ℝ) ≤ (1 + epsilon) * D} := by
  classical
  apply final_answer_accuracy (incoming.prod (Measure.pi drawLaw)) (measurable_of_finite _)
    hDN hD hell hepsilon haccuracy
  · change (incoming.prod (Measure.pi drawLaw)).real {pair | ¬ good pair.1} ≤ 1 / 10
    rw [freshSeed_bad_probability]
    exact hseed
  · intro pair hg
    exact hlower pair.1 hg (pair.2 pair.1)
  · exact .of_finite
  · exact freshSeed_good_excess drawLaw incoming good value D ell hell hmoment

end Final

end EditApproximation

end OAI
