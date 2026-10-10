import OAI.Probability.FreeIsing.Conditioning.FiniteFieldEntropyExpectation
import OAI.Probability.FreeIsing.Posterior.LipschitzObservationDerivative

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal

namespace Problem367.FinitePosterior

variable {S V : Type*} [Fintype S] [Nonempty S] [Fintype V] [DecidableEq V]
  [MeasurableSpace S] [MeasurableSingletonClass S] [StandardBorelSpace S]

theorem hasDerivAt_finiteStandardEntropyEnergy
    (μ : Measure S) [IsProbabilityMeasure μ] (energy : S → ℝ)
    (hprior : ∀ s, μ.real {s} = Real.exp (energy s) / ∑ a, Real.exp (energy a))
    (spin : S → V → ℝ) (observable : S → ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1)
    (hcoords : ∀ s v, spin s v = -1 ∨ spin s v = 1)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun r => ∫ x, fieldEntropy energy spin observable (finiteStandardObservation spin r x)
        ∂μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1)))
      (∫ x, (1 + fieldMean energy spin observable (finiteStandardObservation spin t x) ^ 2) *
          ∑ v, normalizedFieldCovariance energy spin observable
            (finiteStandardObservation spin t x) v ^ 2
        ∂μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) t := by
  have hd := hasDerivAt_integral_gaussianObservationCurve_of_integrable
    (μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1)))
    (fieldEntropy energy spin observable) (fieldEntropyGradient energy spin observable)
    (fun x => hasFDerivAt_fieldEntropy energy spin observable x hspin hneg hpos)
    (fun v => continuous_fieldEntropyGradient energy spin observable v hspin hneg hpos)
    2 (by norm_num)
    (fun x v => abs_fieldEntropyGradient_le energy spin observable x v hspin hneg hpos
      (fun s => (abs_spin_eq_one (fun s => spin s v) (fun s => hcoords s v) s).le))
    (fun x : S × (V → ℝ) => spin x.1) Prod.snd
    ((measurable_of_finite spin).comp measurable_fst) measurable_snd
    (fun x v => (abs_spin_eq_one (fun s => spin s v) (fun s => hcoords s v) x.1).le)
    (fun v => integrable_finiteStandardNoise μ v) ht
    (integrable_finiteStandardEntropy μ energy spin observable hspin hneg hpos hcoords t)
  apply hd.congr_deriv
  exact integral_finiteStandardEntropyVelocity μ energy hprior spin observable hspin hneg hpos hcoords ht

theorem integral_finiteStandardEntropyEnergy
    (μ : Measure S) [IsProbabilityMeasure μ] (energy : S → ℝ)
    (hprior : ∀ s, μ.real {s} = Real.exp (energy s) / ∑ a, Real.exp (energy a))
    (spin : S → V → ℝ) (observable : S → ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1)
    (hcoords : ∀ s v, spin s v = -1 ∨ spin s v = 1)
    {T : ℝ} (hT : 0 ≤ T) :
    let C : ℝ → ℝ := fun t => ∫ x,
      (1 + fieldMean energy spin observable (finiteStandardObservation spin t x) ^ 2) *
        ∑ v, normalizedFieldCovariance energy spin observable
          (finiteStandardObservation spin t x) v ^ 2
      ∂μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))
    IntervalIntegrable C volume 0 T ∧
      (∫ t in 0..T, C t) =
        (∫ x, fieldEntropy energy spin observable (finiteStandardObservation spin T x)
          ∂μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) -
        fieldEntropy energy spin observable 0 ∧
      0 ≤ (∫ t in 0..T, C t) := by
  let ρ := μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))
  let E : ℝ → ℝ := fun t => ∫ x,
    fieldEntropy energy spin observable (finiteStandardObservation spin t x) ∂ρ
  let C : ℝ → ℝ := fun t => ∫ x,
    (1 + fieldMean energy spin observable (finiteStandardObservation spin t x) ^ 2) *
      ∑ v, normalizedFieldCovariance energy spin observable (finiteStandardObservation spin t x) v ^ 2 ∂ρ
  have hG : Integrable (Prod.snd : S × (V → ℝ) → (V → ℝ)) ρ :=
    Integrable.of_eval (fun v => integrable_finiteStandardNoise μ v)
  have hE : Continuous E := by
    simpa only [E, finiteStandardObservation, gaussianObservationCurve] using
      continuous_integral_sqrt_observation_lipschitz
        (integrable_finiteStandardSignal μ spin hcoords) hG
        (lipschitzWith_fieldEntropy energy spin observable hspin hneg hpos
          (fun s v => (abs_spin_eq_one (fun s => spin s v) (fun s => hcoords s v) s).le))
  have hd (t : ℝ) (ht : 0 < t) : HasDerivAt E (C t) t :=
    hasDerivAt_finiteStandardEntropyEnergy μ energy hprior spin observable hspin hneg hpos hcoords ht
  have hCpos (t : ℝ) : 0 ≤ C t := integral_nonneg fun x =>
    mul_nonneg (by positivity) (Finset.sum_nonneg (fun v _ => sq_nonneg _))
  have hCI : IntervalIntegrable C volume 0 T := by
    apply intervalIntegral.intervalIntegrable_deriv_of_nonneg hE.continuousOn
    · intro t ht
      exact hd t (by simpa only [min_eq_left hT, max_eq_right hT] using ht.1)
    · exact fun t _ => hCpos t
  have hFTC : (∫ t in 0..T, C t) = E T - E 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT hE.continuousOn
      (fun t ht => hd t ht.1) hCI
  have hzero : E 0 = fieldEntropy energy spin observable 0 := by
    simp [E, finiteStandardObservation, gaussianObservationCurve, ρ]
  exact ⟨hCI, by simpa only [hzero] using hFTC,
    intervalIntegral.integral_nonneg_of_forall hT hCpos⟩

omit [DecidableEq V] [StandardBorelSpace S] in
theorem continuous_finiteStandardNormalizedEnergy
    (μ : Measure S) [IsFiniteMeasure μ] (energy : S → ℝ)
    (spin : S → V → ℝ) (observable : S → ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1)
    (hcoords : ∀ s v, spin s v = -1 ∨ spin s v = 1) :
    Continuous (fun t : ℝ => ∫ x, ∑ v, normalizedFieldCovariance energy spin observable
      (finiteStandardObservation spin t x) v ^ 2
        ∂μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) := by
  simpa only [finiteStandardObservation, gaussianObservationCurve, Function.comp_def] using
    continuous_integral_sqrt_observation
      (((measurable_of_finite spin).comp measurable_fst).aestronglyMeasurable)
      (measurable_snd.aestronglyMeasurable)
      (continuous_normalizedRowEnergy energy spin observable hspin hneg hpos)
      (fun x => abs_normalizedRowEnergy_le_card energy spin observable x hspin hneg hpos
        (fun s v => (abs_spin_eq_one (fun s => spin s v) (fun s => hcoords s v) s).le))

theorem integral_finiteStandardNormalizedEnergy_le
    (μ : Measure S) [IsProbabilityMeasure μ] (energy : S → ℝ)
    (hprior : ∀ s, μ.real {s} = Real.exp (energy s) / ∑ a, Real.exp (energy a))
    (spin : S → V → ℝ) (observable : S → ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1)
    (hcoords : ∀ s v, spin s v = -1 ∨ spin s v = 1)
    {T : ℝ} (hT : 0 ≤ T) :
    let Q : ℝ → ℝ := fun t => ∫ x, ∑ v, normalizedFieldCovariance energy spin observable
      (finiteStandardObservation spin t x) v ^ 2
      ∂μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))
    IntervalIntegrable Q volume 0 T ∧
      (∫ t in 0..T, Q t) ≤
        (∫ x, fieldEntropy energy spin observable (finiteStandardObservation spin T x)
          ∂μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) -
        fieldEntropy energy spin observable 0 ∧
      0 ≤ (∫ t in 0..T, Q t) := by
  let ρ := μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))
  let Q : ℝ → ℝ := fun t => ∫ x, ∑ v, normalizedFieldCovariance energy spin observable
    (finiteStandardObservation spin t x) v ^ 2 ∂ρ
  let C : ℝ → ℝ := fun t => ∫ x,
    (1 + fieldMean energy spin observable (finiteStandardObservation spin t x) ^ 2) *
      ∑ v, normalizedFieldCovariance energy spin observable (finiteStandardObservation spin t x) v ^ 2 ∂ρ
  have hsignal : ∀ s v, |spin s v| ≤ 1 :=
    fun s v => (abs_spin_eq_one (fun s => spin s v) (fun s => hcoords s v) s).le
  have hQI : IntervalIntegrable Q volume 0 T :=
    (continuous_finiteStandardNormalizedEnergy μ energy spin observable hspin hneg hpos hcoords).intervalIntegrable 0 T
  have hFTC := integral_finiteStandardEntropyEnergy μ energy hprior spin observable
    hspin hneg hpos hcoords hT
  have hmono (t : ℝ) : Q t ≤ C t := by
    let Y := finiteStandardObservation spin t
    let q := fun x => ∑ v, normalizedFieldCovariance energy spin observable (Y x) v ^ 2
    let a := fun x => 1 + fieldMean energy spin observable (Y x) ^ 2
    have hY : Measurable Y := measurable_finiteStandardObservation spin t
    have hq : Integrable q ρ := by
      apply Integrable.of_bound
        (((continuous_normalizedRowEnergy energy spin observable hspin hneg hpos).measurable.comp hY).aestronglyMeasurable)
        (Fintype.card V : ℝ)
      exact Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs, Function.comp_def] using
          abs_normalizedRowEnergy_le_card energy spin observable (Y x) hspin hneg hpos hsignal
    have ha : AEStronglyMeasurable a ρ :=
      ((continuous_const.add ((continuous_fieldMean energy spin observable).pow 2)).measurable.comp hY).aestronglyMeasurable
    have hbound : ∀ x, ‖a x‖ ≤ 2 := by
      intro x
      have hm := abs_fieldMean_le energy spin observable (Y x) 1
        (fun s => (abs_spin_eq_one observable hspin s).le)
      have hm2 := (sq_le_one_iff_abs_le_one _).mpr hm
      simp only [a, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 + fieldMean energy spin observable (Y x) ^ 2)]
      linarith
    have hCInt : Integrable (fun x => a x * q x) ρ := by
      simpa only [mul_comm] using hq.mul_bdd ha (Filter.Eventually.of_forall hbound)
    apply integral_mono hq hCInt
    intro x
    have hqpos : 0 ≤ q x := Finset.sum_nonneg fun v _ => sq_nonneg _
    have hp := mul_nonneg (sq_nonneg (fieldMean energy spin observable (Y x))) hqpos
    dsimp [a]
    nlinarith
  have hQC : (∫ t in 0..T, Q t) ≤ ∫ t in 0..T, C t :=
    intervalIntegral.integral_mono hT hQI hFTC.1 hmono
  refine ⟨hQI, hQC.trans_eq hFTC.2.1, ?_⟩
  exact intervalIntegral.integral_nonneg_of_forall hT fun t =>
    integral_nonneg fun x => Finset.sum_nonneg fun v _ => sq_nonneg _

end Problem367.FinitePosterior

end

end OAI
