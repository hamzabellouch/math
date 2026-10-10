import OAI.Probability.InvariantIsing.Cavity.CavityNormalizerRegularization

namespace OAI

/-! A cutoff weight is bounded below whenever the discarded prior mass
is at most one half. The exceptional event is controlled by its mean. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Topology

namespace InvariantIsing

lemma cavity_cutoff_normalizer_lower {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (s : Set X) (hs : MeasurableSet s)
    (w : X → ℝ) (hw : Measurable w) {c M : ℝ} (hc : 0 ≤ c)
    (hwb : ∀ x ∈ s, w x ∈ Icc c M) :
    c * (1 - ν.real sᶜ) ≤ cavityWeightNormalizer ν (s.indicator w) := by
  have hwi : Integrable (s.indicator w) ν := by
    apply integrable_of_measurable_abs_le (hw.indicator hs) (c := max M 0)
    intro x
    by_cases hx : x ∈ s
    · rw [indicator_of_mem hx, abs_of_nonneg (hc.trans (hwb x hx).1)]
      exact (hwb x hx).2.trans (le_max_left _ _)
    · rw [indicator_of_notMem hx, abs_zero]
      exact le_max_right _ _
  have hlow := integral_mono ((integrable_const c).indicator hs) hwi (fun x => by
    change s.indicator (fun _ => c) x ≤ s.indicator w x
    by_cases hx : x ∈ s
    · simpa only [indicator_of_mem hx] using (hwb x hx).1
    · simp only [indicator_of_notMem hx, le_refl])
  rw [integral_indicator_const c hs, smul_eq_mul] at hlow
  change c * (1 - ν.real sᶜ) ≤ ∫ x, s.indicator w x ∂ν
  calc
    _ = ν.real s * c := by rw [measureReal_compl hs, probReal_univ]; ring
    _ ≤ _ := hlow

lemma cavity_cutoff_normalizer_half {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (s : Set X) (hs : MeasurableSet s)
    (w : X → ℝ) (hw : Measurable w) {c M : ℝ} (hc : 0 ≤ c)
    (hwb : ∀ x ∈ s, w x ∈ Icc c M) (htail : ν.real sᶜ ≤ 1 / 2) :
    c / 2 ≤ cavityWeightNormalizer ν (s.indicator w) := by
  have h := cavity_cutoff_normalizer_lower ν s hs w hw hc hwb
  nlinarith

lemma cavity_small_normalizer_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z t : Ω → ℝ)
    (hZ : Measurable Z) (_ht : Measurable t) (hti : Integrable t P) (ht0 : ∀ ω, 0 ≤ t ω)
    {a : ℝ} (hlow : ∀ ω, t ω ≤ 1 / 2 → a ≤ Z ω) :
    P.real {ω | Z ω < a} ≤ 2 * ∫ ω, t ω ∂P := by
  let E := {ω | Z ω < a}
  have hE : MeasurableSet E := measurableSet_lt hZ measurable_const
  have hi : Integrable (E.indicator (fun _ => (1 : ℝ))) P := (integrable_const _).indicator hE
  have hle := integral_mono hi (hti.const_mul 2) (fun ω => by
    change E.indicator (fun _ => (1 : ℝ)) ω ≤ 2 * t ω
    by_cases hω : ω ∈ E
    · rw [indicator_of_mem hω]
      have hlarge : 1 / 2 < t ω := by
        by_contra hh
        exact (not_le_of_gt hω) (hlow ω (le_of_not_gt hh))
      linarith
    · rw [indicator_of_notMem hω]
      exact mul_nonneg (by norm_num) (ht0 ω))
  simpa only [integral_indicator_const _ hE, smul_eq_mul, mul_one, integral_const_mul] using hle

end InvariantIsing

end

end OAI
