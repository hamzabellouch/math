import OAI.Probability.FreeIsing.Posterior.GaussianEnergy
import OAI.Probability.FreeIsing.Posterior.SqrtObservationDerivative

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Problem367.FinitePosterior

variable {S V : Type*} [Fintype S] [Nonempty S] [Fintype V] [DecidableEq V]
  [MeasurableSpace S] [MeasurableSingletonClass S] [StandardBorelSpace S]

theorem integral_finiteStandardEnergy
    (μ : Measure S) [IsProbabilityMeasure μ]
    (energy : S → ℝ)
    (hprior : ∀ s, μ.real {s} = Real.exp (energy s) / ∑ a, Real.exp (energy a))
    (spin : S → V → ℝ) (observable : S → ℝ)
    (A : ℝ) (hbound : ∀ s, |observable s| ≤ A)
    (hcoords : ∀ s v, spin s v = -1 ∨ spin s v = 1)
    {T : ℝ} (hT : 0 ≤ T) :
    let C : ℝ → ℝ := fun t => ∫ x, ∑ v, fieldCovariance energy spin observable
      (finiteStandardObservation spin t x) v ^ 2
      ∂μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))
    IntervalIntegrable C volume 0 T ∧
      (∫ t in 0..T, C t) =
        (∫ x, fieldMean energy spin observable (finiteStandardObservation spin T x) ^ 2
          ∂μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) -
        fieldMean energy spin observable 0 ^ 2 ∧
      0 ≤ (∫ t in 0..T, C t) ∧ (∫ t in 0..T, C t) ≤ A ^ 2 := by
  let ρ := μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))
  let E : ℝ → ℝ := fun t => ∫ x,
    fieldMean energy spin observable (finiteStandardObservation spin t x) ^ 2 ∂ρ
  let C : ℝ → ℝ := fun t => ∫ x, ∑ v, fieldCovariance energy spin observable
    (finiteStandardObservation spin t x) v ^ 2 ∂ρ
  have hE : Continuous E := by
    simpa only [E, finiteStandardObservation, gaussianObservationCurve, Pi.pow_apply, Function.comp_def] using
      (continuous_integral_sqrt_observation (P := ρ)
        (((measurable_of_finite spin).comp measurable_fst).aestronglyMeasurable)
        (measurable_snd.aestronglyMeasurable)
        ((continuous_fieldMean energy spin observable).pow 2)
        (fun x => abs_fieldMean_square_le energy spin observable x A hbound))
  have hd (t : ℝ) (ht : 0 < t) : HasDerivAt E (C t) t :=
    hasDerivAt_finiteStandardEnergy μ energy hprior spin observable A
      hbound hcoords ht
  have hCpos (t : ℝ) : 0 ≤ C t :=
    integral_nonneg fun x => Finset.sum_nonneg fun v _ => sq_nonneg _
  have hCI : IntervalIntegrable C volume 0 T := by
    apply intervalIntegral.intervalIntegrable_deriv_of_nonneg hE.continuousOn
    · intro t ht
      exact hd t (by simpa only [min_eq_left hT, max_eq_right hT] using ht.1)
    · exact fun t _ => hCpos t
  have hFTC : (∫ t in 0..T, C t) = E T - E 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT hE.continuousOn
      (fun t ht => hd t ht.1) hCI
  have hzero : E 0 = fieldMean energy spin observable 0 ^ 2 := by
    simp [E, finiteStandardObservation, gaussianObservationCurve, ρ]
  have hm : AEStronglyMeasurable
      (fun x => fieldMean energy spin observable (finiteStandardObservation spin T x) ^ 2) ρ :=
    (((continuous_fieldMean energy spin observable).pow 2).measurable.comp
      (measurable_finiteStandardObservation spin T)).aestronglyMeasurable
  have hb (x : S × (V → ℝ)) :
      |fieldMean energy spin observable (finiteStandardObservation spin T x) ^ 2| ≤ A ^ 2 :=
    abs_fieldMean_square_le energy spin observable _ A hbound
  have hInt : Integrable
      (fun x => fieldMean energy spin observable (finiteStandardObservation spin T x) ^ 2) ρ :=
    Integrable.of_bound hm (A ^ 2) (Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using hb x)
  have hEbound : E T ≤ A ^ 2 := by
    calc
      E T ≤ ∫ _x, A ^ 2 ∂ρ := integral_mono hInt (integrable_const _) fun x =>
        (le_abs_self _).trans (hb x)
      _ = A ^ 2 := by simp [ρ]
  refine ⟨hCI, ?_, intervalIntegral.integral_nonneg_of_forall hT hCpos, ?_⟩
  · simpa only [hzero] using hFTC
  · rw [hFTC, hzero]
    exact sub_le_self _ (sq_nonneg _) |>.trans hEbound

end Problem367.FinitePosterior

end

end OAI
