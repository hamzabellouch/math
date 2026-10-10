import Mathlib
import OAI.Analysis.CoulombIonization.Localization.ObservationSmooth
import OAI.Analysis.CoulombIonization.Localization.ScoreDirectional

namespace OAI

noncomputable section

namespace CoulombObservation

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_ObservationLikelihood_scope

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators ContDiff Convolution

def shiftedObservationEvent {ι : Type*} [Fintype ι] (s : Set (ι → ℝ)) (z : ι → ℝ) :
    Set (ι → ℝ) := (fun u => z + u) ⁻¹' s

lemma shiftedObservationEvent_measurable {ι : Type*} [Fintype ι]
    {s : Set (ι → ℝ)} (hs : MeasurableSet s) (z : ι → ℝ) :
    MeasurableSet (shiftedObservationEvent s z) :=
  hs.preimage (measurable_const.add measurable_id)

def observationLikelihood {ι : Type*} [Fintype ι] (s : Set (ι → ℝ)) : (ι → ℝ) → ℝ :=
  (s.indicator (fun _ => 1)) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] compactNoiseKernel

lemma observationLikelihood_eq_probability {ι : Type*} [Fintype ι]
    {s : Set (ι → ℝ)} (hs : MeasurableSet s) (z : ι → ℝ) :
    observationLikelihood s z =
      (Measure.pi (fun _ : ι => compactNoiseLaw)).real (shiftedObservationEvent s z) := by
  rw [observationLikelihood, convolution_def]
  simp only [ContinuousLinearMap.mul_apply']
  rw [← integral_add_left_eq_self _ z]
  have he : (fun u : ι → ℝ => s.indicator (fun _ => (1:ℝ)) (z + u) *
      compactNoiseKernel (z - (z + u))) =
      (fun u => compactNoiseKernel u * (shiftedObservationEvent s z).indicator 1 u) := by
    funext u
    rw [show z - (z+u) = -u by abel, compactNoiseKernel_even]
    by_cases hu : z + u ∈ s <;> simp [shiftedObservationEvent, hu, Set.mem_preimage]
  rw [he, ← compactNoiseLaw_pi_integral, integral_indicator_one
    (shiftedObservationEvent_measurable hs z)]

lemma observationLikelihood_nonneg {ι : Type*} [Fintype ι]
    {s : Set (ι → ℝ)} (hs : MeasurableSet s) (z : ι → ℝ) :
    0 ≤ observationLikelihood s z := by
  rw [observationLikelihood_eq_probability hs]
  exact measureReal_nonneg

lemma observationLikelihood_le_one {ι : Type*} [Fintype ι]
    {s : Set (ι → ℝ)} (hs : MeasurableSet s) (z : ι → ℝ) :
    observationLikelihood s z ≤ 1 := by
  rw [observationLikelihood_eq_probability hs]
  exact measureReal_le_one

lemma observationLikelihood_contDiff {ι : Type*} [Fintype ι]
    {s : Set (ι → ℝ)} (hs : MeasurableSet s) {n : ℕ∞} :
    ContDiff ℝ n (observationLikelihood s) :=
  compactNoiseKernel_compactSupport.contDiff_convolution_right _
    (continuous_const.locallyIntegrable.indicator hs) compactNoiseKernel_contDiff

lemma observationLikelihood_fderiv {ι : Type*} [Fintype ι]
    {s : Set (ι → ℝ)} (hs : MeasurableSet s) (z v : ι → ℝ) :
    fderiv ℝ (observationLikelihood s) z v =
      -(∫ u in shiftedObservationEvent s z, (∑ i, v i * compactNoiseScore (u i))
        ∂Measure.pi (fun _ : ι => compactNoiseLaw)) := by
  let L := ContinuousLinearMap.mul ℝ ℝ
  have hloc : LocallyIntegrable (s.indicator (fun _ => (1:ℝ))) volume :=
    continuous_const.locallyIntegrable.indicator hs
  have hder := compactNoiseKernel_compactSupport.hasFDerivAt_convolution_right L hloc
    (compactNoiseKernel_contDiff (n := 1)) z
  have hint := (compactNoiseKernel_compactSupport.fderiv ℝ).convolutionExists_right
    (L.precompR (ι → ℝ)) hloc
    ((compactNoiseKernel_contDiff (n := 1)).continuous_fderiv one_ne_zero) z
  change fderiv ℝ ((s.indicator (fun _ => (1:ℝ))) ⋆[L, volume] compactNoiseKernel) z v = _
  rw [hder.fderiv, convolution_def, ContinuousLinearMap.integral_apply hint v]
  simp only [ContinuousLinearMap.precompR_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.comp_apply, L, ContinuousLinearMap.mul_apply', compactNoiseKernel_fderiv_apply]
  rw [← integral_add_left_eq_self _ z]
  rw [← integral_indicator (shiftedObservationEvent_measurable hs z), compactNoiseLaw_pi_integral,
    ← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [show z - (z+u) = -u by abel, compactNoiseKernel_even]
  have hodd (r : ℝ) : compactNoiseScore (-r) = -compactNoiseScore r :=
    compactNoiseScore_odd r
  by_cases hu : z + u ∈ s <;>
    simp [Pi.neg_apply, hodd, shiftedObservationEvent, hu, Set.mem_preimage,
      mul_comm, Finset.sum_neg_distrib]

end Work_ObservationLikelihood_scope

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators ContDiff

def observationPlacement {J I : Type*} [Fintype J] [Fintype I] (b : J → ℝ) :
    (I → ℝ) →L[ℝ] (J × I → ℝ) :=
  ContinuousLinearMap.pi (fun q => b q.1 • (ContinuousLinearMap.proj q.2 : (I → ℝ) →L[ℝ] ℝ))

@[simp] lemma observationPlacement_apply {J I : Type*} [Fintype J] [Fintype I]
    (b : J → ℝ) (x : I → ℝ) (q : J × I) :
    observationPlacement b x q = b q.1 * x q.2 := rfl

def arrayLikelihood {J I : Type*} [Fintype J] [Fintype I]
    (b : J → ℝ) (s : Set (J × I → ℝ)) (x : I → ℝ) : ℝ :=
  observationLikelihood s (observationPlacement b x)

def arrayScore {J I : Type*} [Fintype J] [Fintype I]
    (b : J → ℝ) (s : Set (J × I → ℝ)) (x : I → ℝ) : I → ℝ :=
  eventScore b (shiftedObservationEvent s (observationPlacement b x))

lemma arrayLikelihood_eq_probability {J I : Type*} [Fintype J] [Fintype I]
    (b : J → ℝ) {s : Set (J × I → ℝ)} (hs : MeasurableSet s) (x : I → ℝ) :
    arrayLikelihood b s x = (Measure.pi (fun _ : J × I => compactNoiseLaw)).real
      (shiftedObservationEvent s (observationPlacement b x)) :=
  observationLikelihood_eq_probability hs _

lemma arrayLikelihood_nonneg {J I : Type*} [Fintype J] [Fintype I]
    (b : J → ℝ) {s : Set (J × I → ℝ)} (hs : MeasurableSet s) (x : I → ℝ) :
    0 ≤ arrayLikelihood b s x := observationLikelihood_nonneg hs _

lemma arrayLikelihood_le_one {J I : Type*} [Fintype J] [Fintype I]
    (b : J → ℝ) {s : Set (J × I → ℝ)} (hs : MeasurableSet s) (x : I → ℝ) :
    arrayLikelihood b s x ≤ 1 := observationLikelihood_le_one hs _

lemma arrayLikelihood_contDiff {J I : Type*} [Fintype J] [Fintype I]
    (b : J → ℝ) {s : Set (J × I → ℝ)} (hs : MeasurableSet s) {n : ℕ∞} :
    ContDiff ℝ n (arrayLikelihood b s) :=
  (observationLikelihood_contDiff hs).comp (observationPlacement (I := I) b).contDiff

lemma arrayLikelihood_fderiv {J I : Type*} [Fintype J] [Fintype I]
    (b : J → ℝ) {s : Set (J × I → ℝ)} (hs : MeasurableSet s) (x v : I → ℝ) :
    fderiv ℝ (arrayLikelihood b s) x v = -∑ i, v i * arrayScore b s x i := by
  have hh := ((observationLikelihood_contDiff hs (n := 1)).differentiable one_ne_zero
    (observationPlacement b x)).hasFDerivAt.comp x (observationPlacement b).hasFDerivAt
  change fderiv ℝ (observationLikelihood s ∘ observationPlacement b) x v = _
  rw [hh.fderiv, ContinuousLinearMap.comp_apply, observationLikelihood_fderiv hs]
  simp only [observationPlacement_apply]
  rw [eventScore_direction]
  rfl

lemma eventScore_zero {J I : Type*} [Fintype J] [Fintype I]
    (b : J → ℝ) (s : Set (J × I → ℝ))
    (hp : (Measure.pi (fun _ : J × I => compactNoiseLaw)).real s = 0) (i : I) :
    eventScore b s i = 0 := by
  have hμ := (measureReal_eq_zero_iff (μ := Measure.pi (fun _ : J × I => compactNoiseLaw))).mp hp
  simp [eventScore, Measure.restrict_eq_zero.mpr hμ]

lemma arrayScore_sq {J I : Type*} [Fintype J] [Fintype I]
    (b : J → ℝ) {s : Set (J × I → ℝ)} (hs : MeasurableSet s) (x : I → ℝ)
    {k : ℕ} (hk : 0 < k) :
    (∑ i, (arrayScore b s x i)^2) ≤
      observationMomentConstant * (k:ℝ)^5 * (∑ j, (b j)^2) *
        (arrayLikelihood b s x)^(2-(k:ℝ)⁻¹) := by
  rw [arrayLikelihood_eq_probability b hs]
  by_cases hp : 0 < (Measure.pi (fun _ : J × I => compactNoiseLaw)).real
      (shiftedObservationEvent s (observationPlacement b x))
  · exact compactNoise_eventScore_sq b _ hk hp
  have hz : (Measure.pi (fun _ : J × I => compactNoiseLaw)).real
      (shiftedObservationEvent s (observationPlacement b x)) = 0 :=
    le_antisymm (not_lt.mp hp) measureReal_nonneg
  simp only [arrayScore, eventScore_zero b _ hz, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, sum_const_zero]
  have hC := observationMomentConstant_pos
  positivity

lemma arrayScore_sq_one {J I : Type*} [Fintype J] [Fintype I]
    (b : J → ℝ) {s : Set (J × I → ℝ)} (hs : MeasurableSet s) (x : I → ℝ) :
    (∑ i, (arrayScore b s x i)^2) ≤
      observationMomentConstant * (∑ j, (b j)^2) * arrayLikelihood b s x := by
  simpa only [Nat.cast_one, one_pow, mul_one, inv_one, show (2:ℝ)-1=1 by norm_num, Real.rpow_one] using arrayScore_sq b hs x (k := 1) (by decide)

end CoulombObservation

end

end OAI
