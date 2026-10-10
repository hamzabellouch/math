import OAI.Probability.FreeIsing.Gaussian.FiniteFieldGaussianEnergy

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.FinitePosterior

variable {S V : Type*} [Fintype S] [Nonempty S] [Fintype V] [DecidableEq V]

theorem integral_fieldEntropyGradient_mul_noise
    (energy : S → ℝ) (spin : S → V → ℝ) (observable : S → ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1)
    (hcoords : ∀ s v, spin s v = -1 ∨ spin s v = 1)
    (signal : V → ℝ) (t : ℝ) (v : V) :
    (∫ z, fieldEntropyGradient energy spin observable
      (gaussianObservationCurve signal z t) v * z v
      ∂Measure.pi (fun _ : V => gaussianReal 0 1)) =
    Real.sqrt t * ∫ z, fieldEntropyHessianDiagonal energy spin observable
      (gaussianObservationCurve signal z t) v
      ∂Measure.pi (fun _ : V => gaussianReal 0 1) := by
  have h := Problem367.gaussian_pi_integral_mul_affine_of_bounded_deriv
    (fun j => t * signal j) (fun _ => Real.sqrt t) v
    (continuous_fieldEntropyGradient energy spin observable v hspin hneg hpos)
    (continuous_fieldEntropyHessianDiagonal energy spin observable v hspin hneg hpos)
    (fun z r => hasDerivAt_fieldEntropyGradient_update energy spin observable z v r
      (fun s => hcoords s v) hspin hneg hpos)
    (fun z => abs_fieldEntropyGradient_le energy spin observable z v hspin hneg hpos
      (fun s => (abs_spin_eq_one (fun s => spin s v) (fun s => hcoords s v) s).le))
    (fun z => abs_fieldEntropyHessianDiagonal_le energy spin observable z v hspin hneg hpos
      (fun s => (abs_spin_eq_one (fun s => spin s v) (fun s => hcoords s v) s).le))
  simpa only [gaussianObservationCurve, Pi.add_def, Pi.smul_def, smul_eq_mul,
    mul_comm] using h

section Planted

variable [MeasurableSpace S] [MeasurableSingletonClass S]

omit [DecidableEq V] in
private theorem integrable_bounded_entropy_test
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → V → ℝ) (hX : Measurable X) (f : (V → ℝ) → ℝ)
    (hf : Continuous f) (C : ℝ) (hbound : ∀ z, |f z| ≤ C) :
    Integrable (fun x => f (X x)) μ := by
  apply Integrable.of_bound (hf.measurable.comp hX).aestronglyMeasurable C
  exact Filter.Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs, Function.comp_def] using hbound (X x)

omit [DecidableEq V] in
theorem integrable_finiteStandardEntropyGradient (μ : Measure S) [IsFiniteMeasure μ]
    (energy : S → ℝ) (spin : S → V → ℝ) (observable : S → ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1)
    (hcoords : ∀ s v, spin s v = -1 ∨ spin s v = 1) (t : ℝ) (v : V) :
    Integrable (fun x => fieldEntropyGradient energy spin observable
      (finiteStandardObservation spin t x) v)
      (μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) :=
  integrable_bounded_entropy_test _ _ (measurable_finiteStandardObservation spin t) _
    (continuous_fieldEntropyGradient energy spin observable v hspin hneg hpos) 2
    (fun z => abs_fieldEntropyGradient_le energy spin observable z v hspin hneg hpos
      (fun s => (abs_spin_eq_one (fun s => spin s v) (fun s => hcoords s v) s).le))

omit [DecidableEq V] in
theorem integrable_finiteStandardEntropyHessian (μ : Measure S) [IsFiniteMeasure μ]
    (energy : S → ℝ) (spin : S → V → ℝ) (observable : S → ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1)
    (hcoords : ∀ s v, spin s v = -1 ∨ spin s v = 1) (t : ℝ) (v : V) :
    Integrable (fun x => fieldEntropyHessianDiagonal energy spin observable
      (finiteStandardObservation spin t x) v)
      (μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) :=
  integrable_bounded_entropy_test _ _ (measurable_finiteStandardObservation spin t) _
    (continuous_fieldEntropyHessianDiagonal energy spin observable v hspin hneg hpos) 8
    (fun z => abs_fieldEntropyHessianDiagonal_le energy spin observable z v hspin hneg hpos
      (fun s => (abs_spin_eq_one (fun s => spin s v) (fun s => hcoords s v) s).le))

omit [DecidableEq V] in
theorem integrable_finiteStandardEntropyGradient_mul_noise
    (μ : Measure S) [IsFiniteMeasure μ]
    (energy : S → ℝ) (spin : S → V → ℝ) (observable : S → ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1)
    (hcoords : ∀ s v, spin s v = -1 ∨ spin s v = 1) (t : ℝ) (v : V) :
    Integrable (fun x => fieldEntropyGradient energy spin observable
      (finiteStandardObservation spin t x) v * x.2 v)
      (μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) := by
  have hg := integrable_finiteStandardEntropyGradient μ energy spin observable hspin hneg hpos hcoords t v
  have h := (integrable_finiteStandardNoise μ v).mul_bdd hg.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, Function.comp_def] using abs_fieldEntropyGradient_le energy spin observable
        (finiteStandardObservation spin t x) v hspin hneg hpos
        (fun s => (abs_spin_eq_one (fun s => spin s v) (fun s => hcoords s v) s).le))
  simpa only [mul_comm] using h

theorem integral_finiteStandardEntropyGradient_mul_noise
    (μ : Measure S) [IsFiniteMeasure μ]
    (energy : S → ℝ) (spin : S → V → ℝ) (observable : S → ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1)
    (hcoords : ∀ s v, spin s v = -1 ∨ spin s v = 1) (t : ℝ) (v : V) :
    (∫ x, fieldEntropyGradient energy spin observable
      (finiteStandardObservation spin t x) v * x.2 v
      ∂μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) =
    Real.sqrt t * ∫ x, fieldEntropyHessianDiagonal energy spin observable
      (finiteStandardObservation spin t x) v
      ∂μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1)) := by
  rw [integral_prod _ (integrable_finiteStandardEntropyGradient_mul_noise
    μ energy spin observable hspin hneg hpos hcoords t v),
    integral_prod _ (integrable_finiteStandardEntropyHessian
    μ energy spin observable hspin hneg hpos hcoords t v), ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun s =>
    integral_fieldEntropyGradient_mul_noise energy spin observable hspin hneg hpos hcoords (spin s) t v

theorem integral_finiteStandardEntropyVelocity [StandardBorelSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (energy : S → ℝ)
    (hprior : ∀ s, μ.real {s} = Real.exp (energy s) / ∑ a, Real.exp (energy a))
    (spin : S → V → ℝ) (observable : S → ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1)
    (hcoords : ∀ s v, spin s v = -1 ∨ spin s v = 1)
    {t : ℝ} (ht : 0 < t) :
    (∫ x, ∑ v, fieldEntropyGradient energy spin observable
      (finiteStandardObservation spin t x) v *
        gaussianObservationVelocity (spin x.1) x.2 t v
      ∂μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) =
    ∫ x, (1 + fieldMean energy spin observable (finiteStandardObservation spin t x) ^ 2) *
        ∑ v, normalizedFieldCovariance energy spin observable
          (finiteStandardObservation spin t x) v ^ 2
      ∂μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1)) := by
  have hposterior (v : V) :
      (∫ x, fieldEntropyGradient energy spin observable
        (finiteStandardObservation spin t x) v * spin x.1 v
        ∂μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) =
      ∫ x, fieldEntropyGradient energy spin observable
        (finiteStandardObservation spin t x) v *
          fieldMean energy spin (fun s => spin s v) (finiteStandardObservation spin t x)
        ∂μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1)) := by
    have hsq : ∀ s i, spin s i ^ 2 = 1 := by
      intro s i
      rcases hcoords s i with h | h <;> simp [h]
    have htest (z : V → ℝ) : ‖fieldEntropyGradient energy spin observable z v‖ ≤ 2 := by
      rw [Real.norm_eq_abs]
      exact abs_fieldEntropyGradient_le energy spin observable z v hspin hneg hpos
        (fun s => (abs_spin_eq_one (fun s => spin s v) (fun s => hcoords s v) s).le)
    exact Problem367.finiteStandardGaussianPlanted_integral_test_fieldMean μ energy hprior t ht.le
      spin hsq (fun s => spin s v) (fun z => fieldEntropyGradient energy spin observable z v)
      (continuous_fieldEntropyGradient energy spin observable v hspin hneg hpos).measurable 2 htest
  let ρ := μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))
  let Y := finiteStandardObservation spin t
  let g := fun x v => fieldEntropyGradient energy spin observable (Y x) v
  let H := fun x v => fieldEntropyHessianDiagonal energy spin observable (Y x) v
  let p := fun x v => fieldMean energy spin (fun s => spin s v) (Y x)
  let c := 1 / (2 * Real.sqrt t)
  have hy : Measurable Y := measurable_finiteStandardObservation spin t
  have hg (v : V) : Integrable (fun x => g x v) ρ :=
    integrable_finiteStandardEntropyGradient μ energy spin observable hspin hneg hpos hcoords t v
  have hH (v : V) : Integrable (fun x => H x v) ρ :=
    integrable_finiteStandardEntropyHessian μ energy spin observable hspin hneg hpos hcoords t v
  have hn (v : V) : Integrable (fun x => g x v * x.2 v) ρ :=
    integrable_finiteStandardEntropyGradient_mul_noise μ energy spin observable hspin hneg hpos hcoords t v
  have hs (v : V) : Integrable (fun x => g x v * spin x.1 v) ρ := by
    apply (hg v).mul_bdd
      (((measurable_of_finite (fun s => spin s v)).comp measurable_fst).aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, Function.comp_def] using
        (abs_spin_eq_one (fun s => spin s v) (fun s => hcoords s v) x.1).le
  have hp (v : V) : Integrable (fun x => g x v * p x v) ρ := by
    apply (hg v).mul_bdd
      (((continuous_fieldMean energy spin (fun s => spin s v)).measurable.comp hy).aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, Function.comp_def] using abs_fieldMean_le energy spin (fun s => spin s v)
        (Y x) 1 (fun s => (abs_spin_eq_one (fun s => spin s v) (fun s => hcoords s v) s).le)
  have hvEq (v : V) :
      (fun x : S × (V → ℝ) => g x v * gaussianObservationVelocity (spin x.1) x.2 t v) =
        (fun x => g x v * spin x.1 v + c * (g x v * x.2 v)) := by
    funext x
    change g x v * (spin x.1 v + c * x.2 v) = _
    ring
  have hv (v : V) : Integrable
      (fun x => g x v * gaussianObservationVelocity (spin x.1) x.2 t v) ρ := by
    rw [hvEq]
    exact (hs v).add ((hn v).const_mul c)
  have hcancel (x : S × (V → ℝ)) (v : V) :
      g x v * p x v + (1 / 2 : ℝ) * H x v =
        (1 + fieldMean energy spin observable (Y x) ^ 2) *
        normalizedFieldCovariance energy spin observable (Y x) v ^ 2 := by
    dsimp [g, H, p, fieldEntropyGradient, fieldEntropyHessianDiagonal]
    ring
  have hc (v : V) : Integrable
      (fun x => (1 + fieldMean energy spin observable (Y x) ^ 2) *
        normalizedFieldCovariance energy spin observable (Y x) v ^ 2) ρ := by
    exact ((hp v).add ((hH v).const_mul (1 / 2 : ℝ))).congr
      (Filter.Eventually.of_forall fun x => hcancel x v)
  have hstep (v : V) :
      (∫ x, g x v * gaussianObservationVelocity (spin x.1) x.2 t v ∂ρ) =
        ∫ x, (1 + fieldMean energy spin observable (Y x) ^ 2) *
        normalizedFieldCovariance energy spin observable (Y x) v ^ 2 ∂ρ := by
    rw [hvEq, integral_add (hs v) ((hn v).const_mul c), integral_const_mul]
    have hnoise : (∫ x, g x v * x.2 v ∂ρ) = Real.sqrt t * ∫ x, H x v ∂ρ :=
      integral_finiteStandardEntropyGradient_mul_noise μ energy spin observable hspin hneg hpos hcoords t v
    rw [hnoise]
    have hcoef : c * Real.sqrt t = (1 / 2 : ℝ) := by
      dsimp [c]
      field_simp [ne_of_gt (Real.sqrt_pos.mpr ht)]
    rw [← mul_assoc, hcoef, hposterior v]
    rw [← integral_const_mul, ← integral_add (hp v) ((hH v).const_mul (1 / 2 : ℝ))]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => hcancel x v)
  change (∫ x, ∑ v, g x v * gaussianObservationVelocity (spin x.1) x.2 t v ∂ρ) = _
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun v _ => hv v), integral_finsetSum _ (fun v _ => hc v)]
  exact Finset.sum_congr rfl fun v _ => hstep v

omit [Nonempty S] [DecidableEq V] in
theorem integrable_finiteStandardSignal (μ : Measure S) [IsFiniteMeasure μ]
    (spin : S → V → ℝ) (hcoords : ∀ s v, spin s v = -1 ∨ spin s v = 1) :
    Integrable (fun x : S × (V → ℝ) => spin x.1)
      (μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) := by
  apply Integrable.of_eval
  intro v
  apply Integrable.of_bound
    (((measurable_of_finite (fun s => spin s v)).comp measurable_fst).aestronglyMeasurable) 1
  exact Filter.Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs, Function.comp_def] using
      (abs_spin_eq_one (fun s => spin s v) (fun s => hcoords s v) x.1).le

omit [Nonempty S] [DecidableEq V] in
theorem integrable_finiteStandardObservation (μ : Measure S) [IsFiniteMeasure μ]
    (spin : S → V → ℝ) (hcoords : ∀ s v, spin s v = -1 ∨ spin s v = 1) (t : ℝ) :
    Integrable (finiteStandardObservation spin t)
      (μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) := by
  have hn : Integrable (Prod.snd : S × (V → ℝ) → (V → ℝ))
      (μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) :=
    Integrable.of_eval (fun v => integrable_finiteStandardNoise μ v)
  exact ((integrable_finiteStandardSignal μ spin hcoords).smul t).add
    (hn.smul (Real.sqrt t))

omit [DecidableEq V] in
theorem integrable_finiteStandardEntropy (μ : Measure S) [IsFiniteMeasure μ]
    (energy : S → ℝ) (spin : S → V → ℝ) (observable : S → ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1)
    (hcoords : ∀ s v, spin s v = -1 ∨ spin s v = 1) (t : ℝ) :
    Integrable (fun x => fieldEntropy energy spin observable (finiteStandardObservation spin t x))
      (μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) :=
  integrable_fieldEntropy_comp _ energy spin observable hspin hneg hpos
    (fun s v => (abs_spin_eq_one (fun s => spin s v) (fun s => hcoords s v) s).le)
    (integrable_finiteStandardObservation μ spin hcoords t)

end Planted

omit [DecidableEq V] in
theorem continuous_normalizedRowEnergy (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1) :
    Continuous (fun x => ∑ v, normalizedFieldCovariance energy spin observable x v ^ 2) := by
  apply continuous_finsetSum
  intro v _
  exact (continuous_normalizedFieldCovariance_entropy energy spin observable v hspin hneg hpos).pow 2

omit [DecidableEq V] in
theorem abs_normalizedRowEnergy_le_card (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1)
    (hsignal : ∀ s v, |spin s v| ≤ 1) :
    |∑ v, normalizedFieldCovariance energy spin observable x v ^ 2| ≤ Fintype.card V := by
  rw [abs_of_nonneg (Finset.sum_nonneg (fun v _ => sq_nonneg _))]
  calc
    (∑ v, normalizedFieldCovariance energy spin observable x v ^ 2) ≤ ∑ _v : V, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro v _
      exact (sq_le_one_iff_abs_le_one _).mpr
        (abs_normalizedFieldCovariance_le_one_entropy energy spin observable x v
          hspin hneg hpos (fun s => hsignal s v))
    _ = _ := by simp

end Problem367.FinitePosterior

end

end OAI
