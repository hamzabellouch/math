import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveSourceFormula
import OAI.MathematicalPhysics.Boltzmann.Branching.CharacteristicProductTest
import OAI.MathematicalPhysics.Boltzmann.Branching.DampedCollisionHistories
import OAI.MathematicalPhysics.Boltzmann.Branching.DampedBranchingBlocks
import OAI.MathematicalPhysics.Boltzmann.Branching.OccupationSliceIntegral
import OAI.MathematicalPhysics.Boltzmann.Branching.TruncatedExponential
import OAI.MathematicalPhysics.Boltzmann.Compactness.PhysicalEvolution
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakEntropyMarginal
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.Prod

namespace OAI

section

/-! # Each marked event is damped free waiting followed by physical collision -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem dampedMediumEventKernel_eq_comp (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ)
    (p : PhysicalFlightState) {T : ℝ} (hT : p.1 ≤ T) :
    dampedMediumEventKernel C b endTime T p =
      (dampedMediumStateCollision C b endTime ∘ₖ physicalWaitingKernel C) p := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [dampedMediumEventKernel_physical_lintegral C b endTime p hT hF,
    Kernel.lintegral_comp _ _ _ hF,
    physicalWaitingKernel_lintegral C p hF.lintegral_kernel]
  apply lintegral_congr
  intro s
  rw [dampedMediumStateCollision_lintegral C b endTime _ hF]
  simp only [physicalAdvance,mediumPoint]
  rw [show endTime-(p.1-s) = endTime-p.1+s by ring]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Constant damping exposes a positive measure source -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.WeakTime

def timeWeightedDensity (a b C : ℝ) (F : ℝ × Phase → ℝ) (z : ℝ × Phase) : ℝ :=
  slabExponential a b C z.1*F z

def timeWeightedSource (a b C : ℝ) (μ : Measure (ℝ × Phase)) : Measure (ℝ × Phase) :=
  positiveDensityMeasure μ (fun z => slabExponential a b C z.1)

def dampedResidual (a b C : ℝ) (F L : ℝ × Phase → ℝ) (z : ℝ × Phase) : ℝ :=
  slabExponential a b C z.1*(C*F z-L z)

theorem timeWeightedDensity_integrable {a b C : ℝ} (hC : 0 ≤ C)
    {F : ℝ × Phase → ℝ} (hi : Integrable F) : Integrable (timeWeightedDensity a b C F) :=
  hi.bdd_mul ((slabExponential_measurable a b C).comp measurable_fst).aestronglyMeasurable
    (ae_of_all _ (fun z => slabExponential_bound a b hC z.1))

theorem timeWeightedSource_finite (a b : ℝ) {C : ℝ} (hC : 0 ≤ C)
    (μ : Measure (ℝ × Phase)) [IsFiniteMeasure μ] : IsFiniteMeasure (timeWeightedSource a b C μ) := by
  apply positiveDensityMeasure_finite
  · exact (integrable_const (Real.exp (C*b))).mono'
      ((slabExponential_measurable a b C).comp measurable_fst).aestronglyMeasurable
      (ae_of_all _ (fun z => slabExponential_bound a b hC z.1))
  · exact ae_of_all _ (fun z => slabExponential_nonneg a b C z.1)

private theorem time_phase_integrable {F : ℝ × Phase → ℝ} (hi : Integrable F)
    {φ : Phase → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ)
    {θ : ℝ → ℝ} (hθ : Continuous θ) (hθc : HasCompactSupport θ) :
    Integrable (fun z => (θ z.1*φ z.2)*F z) := by
  obtain ⟨B,hB⟩ := hφ.bounded_above_of_compact_support hc
  obtain ⟨D,hD⟩ := hθ.bounded_above_of_compact_support hθc
  have hp := hi.bdd_mul (hφ.measurable.comp measurable_snd).aestronglyMeasurable
    (ae_of_all _ (fun z => hB z.2))
  simpa only [mul_assoc,Function.comp_def] using hp.bdd_mul
    (hθ.measurable.comp measurable_fst).aestronglyMeasurable (ae_of_all _ (fun z => hD z.1))

theorem ae_damped_measure_interval_balance {a b C : ℝ} (hab : a < b) (hC : 0 ≤ C)
    {F L : ℝ × Phase → ℝ} (hi : Integrable F (volume : Measure (ℝ × Phase)))
    (hL : Integrable L (volume : Measure (ℝ × Phase))) (hn : ∀ᵐ z ∂volume, 0 ≤ F z)
    (hbound : ∀ᵐ z ∂volume, z.1 ∈ Ioo a b → L z ≤ C*F z)
    (μ : Measure (ℝ × Phase)) [IsFiniteMeasure μ]
    (hw : ∀ φ : Phase → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∀ p, 0 ≤ φ p) → ∀ θ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ →
      HasCompactSupport θ → tsupport θ ⊆ Ioo a b →
      (∫ z, (deriv θ z.1*φ z.2)*F z)+
        (∫ z, θ z.1*φ z.2 ∂μ)-(∫ z, (θ z.1*φ z.2)*L z) = 0) :
    ∀ᵐ s ∂volume, ∀ᵐ t ∂volume,
      s ∈ Ioo a b → t ∈ Ioo a b → s ≤ t →
      phaseSlice (timeWeightedDensity a b C F) t =
        phaseSlice (timeWeightedDensity a b C F) s+
          phaseIncrement (timeWeightedSource a b C μ+
            positiveDensityMeasure volume (dampedResidual a b C F L)) s t := by
  let W := slabExponential a b C
  let r := dampedResidual a b C F L
  have hW : Measurable W := slabExponential_measurable a b C
  have hr : Integrable r := timeWeightedDensity_integrable hC ((hi.const_mul C).sub hL)
  have hrn : ∀ᵐ z ∂volume, 0 ≤ r z := by
    filter_upwards [hbound] with z hz
    by_cases hm : z.1 ∈ Ioo a b
    · exact mul_nonneg (slabExponential_nonneg a b C z.1) (sub_nonneg.mpr (hz hm))
    · simp [r,dampedResidual,slabExponential,hm]
  let _ := positiveDensityMeasure_finite hr hrn
  let _ := timeWeightedSource_finite a b hC μ
  let ρ := timeWeightedSource a b C μ+positiveDensityMeasure volume r
  have hFi := timeWeightedDensity_integrable (a := a) (b := b) hC hi
  have hFn : ∀ᵐ z ∂volume, 0 ≤ timeWeightedDensity a b C F z :=
    hn.mono (fun z hz => mul_nonneg (slabExponential_nonneg a b C z.1) hz)
  have hb := ae_measure_interval_balance hab hFi hFn ρ 0 ?_
  · simpa only [phaseIncrement,Measure.restrict_zero,Measure.map_zero,add_zero] using hb
  intro φ hφ hc hφn ψ hψ hψc hψs
  let θ : ℝ → ℝ := fun t => Real.exp (C*t)*ψ t
  have hθ : ContDiff ℝ (⊤ : ℕ∞) θ := by dsimp only [θ]; fun_prop
  have hθc : HasCompactSupport θ := hψc.mul_left
  have hθs : tsupport θ ⊆ Ioo a b := tsupport_mul_subset_right.trans hψs
  have hθeq (t : ℝ) : θ t = ψ t*W t := slabExponential_test hψs t
  have hdθ (t : ℝ) : deriv θ t = deriv ψ t*W t+C*(ψ t*W t) :=
    slabExponential_test_derivative hψ hψs t
  have hleft := time_phase_integrable hi hφ.continuous hc
    (hθ.continuous_deriv (by simp)) hθc.deriv
  have hloss := time_phase_integrable hL hφ.continuous hc hθ.continuous hθc
  have hright := time_phase_integrable hFi hφ.continuous hc
    (hψ.continuous_deriv (by simp)) hψc.deriv
  have hres := time_phase_integrable hr hφ.continuous hc hψ.continuous hψc
  have he : (∫ z, (deriv θ z.1*φ z.2)*F z)-(∫ z, (θ z.1*φ z.2)*L z) =
      (∫ z, (deriv ψ z.1*φ z.2)*timeWeightedDensity a b C F z)+
      (∫ z, (ψ z.1*φ z.2)*r z) := by
    rw [← integral_sub hleft hloss,← integral_add hright hres]
    apply integral_congr_ae
    exact ae_of_all _ (fun z => by
      dsimp only
      rw [hdθ,hθeq]
      dsimp only [timeWeightedDensity,r,dampedResidual,W]
      ring)
  have htest (m : Measure (ℝ × Phase)) [IsFiniteMeasure m] :
      Integrable (fun z : ℝ × Phase => ψ z.1*φ z.2) m :=
    (timePhaseTest_contDiff hψ hφ).continuous.integrable_of_hasCompactSupport
      (timePhaseTest_compact hψc hc)
  have hWm : AEMeasurable (fun z : ℝ × Phase => W z.1) μ := by
    simpa only [Function.comp_def] using (hW.comp measurable_fst).aemeasurable (μ := μ)
  have hh := hw φ hφ hc hφn θ hθ hθc hθs
  have hμeq : (∫ z, θ z.1*φ z.2 ∂μ) = ∫ z, (ψ z.1*φ z.2)*W z.1 ∂μ := by
    apply integral_congr_ae
    exact ae_of_all _ (fun z => by dsimp only; rw [hθeq]; ring)
  rw [hμeq] at hh
  simp only [integral_zero_measure,sub_zero]
  change _+(∫ z, ψ z.1*φ z.2 ∂(timeWeightedSource a b C μ+positiveDensityMeasure volume r)) = 0
  rw [integral_add_measure (htest _) (htest _)]
  change _+((∫ z, ψ z.1*φ z.2 ∂positiveDensityMeasure μ (fun z => W z.1))+
    (∫ z, ψ z.1*φ z.2 ∂positiveDensityMeasure volume r)) = 0
  rw [positiveDensityMeasure_integral hWm
      (ae_of_all _ (fun z => slabExponential_nonneg a b C z.1)),
    positiveDensityMeasure_integral hr.aemeasurable hrn]
  linarith only [he,hh]

end BoltzmannNonuniqueness.WeakTime

end

end

section

/-! # Removing the exponential weight from a positive measure balance -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.WeakTime

theorem positiveDensityMeasure_const_mul {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    positiveDensityMeasure μ (fun x => c*f x) = ENNReal.ofReal c • positiveDensityMeasure μ f := by
  unfold positiveDensityMeasure
  have he : (fun x => ENNReal.ofReal (c*f x)) = ENNReal.ofReal c • (fun x => ENNReal.ofReal (f x)) := by
    funext x
    exact ENNReal.ofReal_mul hc
  rw [he]
  exact withDensity_smul' _ _ ENNReal.ofReal_ne_top

theorem timeWeighted_phaseSlice (a b C : ℝ) (F : ℝ × Phase → ℝ) (t : ℝ) :
    phaseSlice (timeWeightedDensity a b C F) t =
      ENNReal.ofReal (slabExponential a b C t) • phaseSlice F t := by
  change positiveDensityMeasure volume (fun p : Phase => slabExponential a b C t*F (t,p)) =
    ENNReal.ofReal (slabExponential a b C t) • positiveDensityMeasure volume (fun p => F (t,p))
  exact positiveDensityMeasure_const_mul (X := Phase) volume (fun p => F (t,p))
    (c := slabExponential a b C t) (slabExponential_nonneg a b C t)

theorem phaseIncrement_add (μ ν : Measure (ℝ × Phase)) (s t : ℝ) :
    phaseIncrement (μ+ν) s t = phaseIncrement μ s t+phaseIncrement ν s t := by
  rw [phaseIncrement,Measure.restrict_add,Measure.map_add _ _ measurable_snd]
  rfl

theorem undamp_measure_balance {a b C s t : ℝ} (F : ℝ × Phase → ℝ)
    (μ : Measure Phase) (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b)
    (h : phaseSlice (timeWeightedDensity a b C F) t =
      phaseSlice (timeWeightedDensity a b C F) s+μ) :
    phaseSlice F t = ENNReal.ofReal (Real.exp (C*(s-t))) • phaseSlice F s+
      ENNReal.ofReal (Real.exp (-C*t)) • μ := by
  rw [timeWeighted_phaseSlice,timeWeighted_phaseSlice,
    slabExponential,indicator_of_mem ht,indicator_of_mem hs] at h
  have hh := congrArg (fun m : Measure Phase => ENNReal.ofReal (Real.exp (-C*t)) • m) h
  rw [smul_add,smul_smul,smul_smul,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← Real.exp_add,← Real.exp_add] at hh
  have hzero : -C*t+C*t = 0 := by ring
  have he : -C*t+C*s = C*(s-t) := by ring
  simpa only [hzero,he,Real.exp_zero,ENNReal.ofReal_one,one_smul] using hh

theorem undamp_measure_balance_add {a b C s t : ℝ} (F : ℝ × Phase → ℝ)
    (μ ν : Measure (ℝ × Phase)) (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b)
    (h : phaseSlice (timeWeightedDensity a b C F) t =
      phaseSlice (timeWeightedDensity a b C F) s+phaseIncrement (μ+ν) s t) :
    phaseSlice F t = ENNReal.ofReal (Real.exp (C*(s-t))) • phaseSlice F s+
      (ENNReal.ofReal (Real.exp (-C*t)) • phaseIncrement μ s t+
        ENNReal.ofReal (Real.exp (-C*t)) • phaseIncrement ν s t) := by
  rw [undamp_measure_balance F _ hs ht h,phaseIncrement_add,smul_add]

end BoltzmannNonuniqueness.WeakTime

end

end

section

/-! # Finite marked histories are iterated physical waiting and collision -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem damped_mediumEventKernel_remaining_le (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ)
    (p : PhysicalFlightState) {T : ℝ} (hT : p.1 ≤ T) :
    ∀ᵐ q ∂dampedMediumEventKernel C b endTime T p, q.1 ≤ p.1 := by
  rw [ae_iff]
  let A : Set PhysicalFlightState := {q | ¬q.1 ≤ p.1}
  have hA : MeasurableSet A := by dsimp [A]; measurability
  change dampedMediumEventKernel C b endTime T p A = 0
  rw [← lintegral_indicator_one hA,
    dampedMediumEventKernel_physical_lintegral C b endTime p hT
      (F := A.indicator (1 : PhysicalFlightState → ℝ≥0∞)) (measurable_const.indicator hA)]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have hsp : p.1-s ≤ p.1 := sub_le_self _ hs.1.le
  have hz : ∀ v : V, A.indicator (1 : PhysicalFlightState → ℝ≥0∞)
      (p.1-s,((mediumPoint endTime p s).2,v)) = 0 := by
    intro v
    exact indicator_of_notMem (by simpa only [A,mem_ofPred_eq,not_not] using hsp) _
  simp only [hz,lintegral_zero,mul_zero,Pi.zero_apply]

theorem damped_mediumEventKernel_pow_eq_comp (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ)
    (n : ℕ) (p : PhysicalFlightState) {T : ℝ} (hT : p.1 ≤ T) :
    ((dampedMediumEventKernel C b endTime T)^n) p =
      ((dampedMediumStateCollision C b endTime ∘ₖ physicalWaitingKernel C)^n) p := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    have hpow (L : Kernel PhysicalFlightState PhysicalFlightState) :
        L^(n+1) = (L^n) ∘ₖ L := by
      simpa only [pow_one] using Kernel.pow_add L n 1
    rw [hpow,hpow,Kernel.comp_apply,Kernel.comp_apply]
    calc
      (dampedMediumEventKernel C b endTime T p).bind ((dampedMediumEventKernel C b endTime T)^n) =
          (dampedMediumEventKernel C b endTime T p).bind
            ((dampedMediumStateCollision C b endTime ∘ₖ physicalWaitingKernel C)^n) := by
        apply Measure.bind_congr_right
        filter_upwards [damped_mediumEventKernel_remaining_le C b endTime p hT] with q hq
        exact ih q (hq.trans hT)
      _ = _ := by rw [dampedMediumEventKernel_eq_comp C b endTime p hT]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Fixed time-window representations of the bounded event histories -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def dampedBoundedPhysicalEvent (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) :
    Kernel PhysicalFlightState PhysicalFlightState :=
  (dampedMediumStateCollision C b endTime ∘ₖ physicalWaitingKernel C).restrict mediumVelocityBox_measurable

instance dampedBoundedPhysicalEvent_sFinite (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) :
    IsSFiniteKernel (dampedBoundedPhysicalEvent C b endTime) := by
  unfold dampedBoundedPhysicalEvent
  infer_instance

theorem damped_boundedMediumEventKernel_eq_physical (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ)
    (p : PhysicalFlightState) {T : ℝ} (hT : p.1 ≤ T) :
    dampedBoundedEventKernel C b endTime T p = dampedBoundedPhysicalEvent C b endTime p := by
  rw [dampedBoundedEventKernel,Kernel.restrict_apply,
    dampedBoundedPhysicalEvent,Kernel.restrict_apply,dampedMediumEventKernel_eq_comp C b endTime p hT]

theorem damped_boundedMediumEventKernel_remaining_le (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ)
    (p : PhysicalFlightState) {T : ℝ} (hT : p.1 ≤ T) :
    ∀ᵐ q ∂dampedBoundedEventKernel C b endTime T p, q.1 ≤ p.1 := by
  rw [dampedBoundedEventKernel,Kernel.restrict_apply]
  exact ae_restrict_of_ae (damped_mediumEventKernel_remaining_le C b endTime p hT)

theorem damped_boundedMediumEventKernel_pow_eq_physical (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ)
    (n : ℕ) (p : PhysicalFlightState) {T : ℝ} (hT : p.1 ≤ T) :
    ((dampedBoundedEventKernel C b endTime T)^n) p = ((dampedBoundedPhysicalEvent C b endTime)^n) p := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    have hpow (L : Kernel PhysicalFlightState PhysicalFlightState) :
        L^(n+1) = (L^n) ∘ₖ L := by
      simpa only [pow_one] using Kernel.pow_add L n 1
    rw [hpow,hpow,Kernel.comp_apply,Kernel.comp_apply]
    calc
      (dampedBoundedEventKernel C b endTime T p).bind ((dampedBoundedEventKernel C b endTime T)^n) =
          (dampedBoundedEventKernel C b endTime T p).bind ((dampedBoundedPhysicalEvent C b endTime)^n) := by
        apply Measure.bind_congr_right
        filter_upwards [damped_boundedMediumEventKernel_remaining_le C b endTime p hT] with q hq
        exact ih q (hq.trans hT)
      _ = _ := by rw [damped_boundedMediumEventKernel_eq_physical C b endTime p hT]


end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Collision-time integrals for the positive Duhamel source -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.WeakTime

def dampedSourceIncrement (a b C s t : ℝ) (μ : Measure (ℝ × Phase)) : Measure Phase :=
  ENNReal.ofReal (Real.exp (-C*t)) • phaseIncrement (timeWeightedSource a b C μ) s t

theorem dampedSourceIncrement_lintegral (μ : Measure (ℝ × Phase))
    {a b C s t : ℝ} (hs : a < s) (ht : t < b) {ψ : Phase → ℝ≥0∞} (hψ : Measurable ψ) :
    (∫⁻ p, ψ p ∂dampedSourceIncrement a b C s t μ) =
      ∫⁻ z in Prod.fst ⁻¹' Ioc s t,
        ENNReal.ofReal (Real.exp (-C*(t-z.1)))*ψ z.2 ∂μ := by
  have hW : Measurable (fun z : ℝ × Phase => ENNReal.ofReal (slabExponential a b C z.1)) := by
    simpa only [Function.comp_def] using
      ((slabExponential_measurable a b C).comp measurable_fst).ennreal_ofReal
  have hp : Measurable (fun z : ℝ × Phase => ψ z.2) := by
    simpa only [Function.comp_def] using hψ.comp measurable_snd
  rw [dampedSourceIncrement,lintegral_smul_measure,phaseIncrement,
    lintegral_map hψ measurable_snd]
  change ENNReal.ofReal (Real.exp (-C*t))*
    (∫⁻ z in Prod.fst ⁻¹' Ioc s t, ψ z.2
      ∂positiveDensityMeasure μ (fun z => slabExponential a b C z.1)) = _
  rw [positiveDensityMeasure,restrict_withDensity (measurable_fst measurableSet_Ioc),
    lintegral_withDensity_eq_lintegral_mul _ hW hp,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (measurable_fst measurableSet_Ioc)] with z hz
  have hab : z.1 ∈ Ioo a b := ⟨hs.trans hz.1,hz.2.trans_lt ht⟩
  change ENNReal.ofReal (Real.exp (-C*t)) *
    (ENNReal.ofReal (slabExponential a b C z.1)*ψ z.2) = _
  rw [slabExponential,indicator_of_mem hab,← mul_assoc,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
  congr 2
  ring_nf

end BoltzmannNonuniqueness.WeakTime

end

end

section

/-! # The damped residence-time kernel along a free characteristic -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.WeakTime

def residenceWeight (C b : ℝ) (q : (ℝ × Phase) × ℝ) : ℝ≥0∞ :=
  {p : (ℝ × Phase) × ℝ | p.1.1 < p.2 ∧ p.2 ≤ b}.indicator
    (fun p => ENNReal.ofReal (Real.exp (C*(p.1.1-p.2)))) q

theorem residenceWeight_measurable (C b : ℝ) : Measurable (residenceWeight C b) := by
  unfold residenceWeight
  have hm : Measurable (fun p : (ℝ × Phase) × ℝ =>
      ENNReal.ofReal (Real.exp (C*(p.1.1-p.2)))) := by fun_prop
  exact hm.indicator ((measurableSet_lt measurable_fst.fst measurable_snd).inter
    (measurableSet_le measurable_snd measurable_const))

def residenceKernel (C b : ℝ) : Kernel (ℝ × Phase) (ℝ × Phase) :=
  (Kernel.withDensity (Kernel.id ×ₖ Kernel.const (ℝ × Phase) (volume : Measure ℝ))
    (fun _ q => residenceWeight C b q)).map (fun q => (q.2,q.1.2))

instance residenceKernel_sFinite (C b : ℝ) : IsSFiniteKernel (residenceKernel C b) := by
  have : IsSFiniteKernel (Kernel.withDensity
      (Kernel.id ×ₖ Kernel.const (ℝ × Phase) (volume : Measure ℝ))
      (fun _ q => residenceWeight C b q)) := by
    apply Kernel.IsSFiniteKernel.withDensity
    intro z q
    by_cases hq : q.1.1 < q.2 ∧ q.2 ≤ b
    · simp [residenceWeight,hq]
    · simp [residenceWeight,hq]
  unfold residenceKernel
  infer_instance

theorem residenceKernel_lintegral (C b : ℝ) (z : ℝ × Phase)
    {f : ℝ × Phase → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ p, f p ∂residenceKernel C b z) =
      ∫⁻ t in Ioc z.1 b, ENNReal.ofReal (Real.exp (C*(z.1-t)))*f (t,z.2) := by
  have hm : Measurable (fun q : (ℝ × Phase) × ℝ => (q.2,q.1.2)) := by fun_prop
  have hc : Measurable (fun q : (ℝ × Phase) × ℝ => f (q.2,q.1.2)) := hf.comp hm
  have hd : Measurable (Function.uncurry (fun (_ : ℝ × Phase) q => residenceWeight C b q)) :=
    (residenceWeight_measurable C b).comp measurable_snd
  rw [residenceKernel,Kernel.lintegral_map _ hm z hf,
    Kernel.lintegral_withDensity _ hd z hc]
  have hi : Measurable (fun q : (ℝ × Phase) × ℝ =>
      residenceWeight C b q*f (q.2,q.1.2)) := (residenceWeight_measurable C b).mul hc
  rw [Kernel.lintegral_id_prod hi]
  change (∫⁻ t, residenceWeight C b (z,t)*f (t,z.2)) = _
  rw [← lintegral_indicator measurableSet_Ioc]
  apply lintegral_congr
  intro t
  by_cases ht : t ∈ Ioc z.1 b
  · simp [residenceWeight,ht,ht.1,ht.2]
  · simp [residenceWeight,ht,show ¬(z.1<t ∧ t≤b) from ht]

end BoltzmannNonuniqueness.WeakTime

end

end

section

/-! # One positive source for the undamped characteristic renewal equation -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.WeakTime

theorem timeWeightedSource_add (a b C : ℝ) (μ ν : Measure (ℝ × Phase)) :
    timeWeightedSource a b C (μ+ν) = timeWeightedSource a b C μ+timeWeightedSource a b C ν := by
  exact withDensity_add_measure _ _ _

theorem timeWeightedSource_density (a b C : ℝ) (μ : Measure (ℝ × Phase))
    {f : ℝ × Phase → ℝ} (hf : AEMeasurable f μ) :
    timeWeightedSource a b C (positiveDensityMeasure μ f) =
      positiveDensityMeasure μ (fun z => slabExponential a b C z.1*f z) := by
  have hw : Measurable (fun z : ℝ × Phase => slabExponential a b C z.1) :=
    (slabExponential_measurable a b C).comp measurable_fst
  unfold timeWeightedSource positiveDensityMeasure
  rw [← withDensity_mul₀ hf.ennreal_ofReal hw.aemeasurable.ennreal_ofReal]
  congr 1
  funext z
  change ENNReal.ofReal (f z)*ENNReal.ofReal (slabExponential a b C z.1) = _
  rw [mul_comm,ENNReal.ofReal_mul (slabExponential_nonneg a b C z.1)]

theorem dampedResidual_source {a b C : ℝ} {F L : ℝ × Phase → ℝ}
    (hF : AEMeasurable F volume) (hL : AEMeasurable L volume) :
    positiveDensityMeasure volume (dampedResidual a b C F L) =
      timeWeightedSource a b C (positiveDensityMeasure volume (fun z => C*F z-L z)) :=
  (timeWeightedSource_density a b C volume ((aemeasurable_const.mul hF).sub hL)).symm

theorem undamp_combined_source_balance {a b C s t : ℝ} {F L : ℝ × Phase → ℝ}
    (μ : Measure (ℝ × Phase)) (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b)
    (hF : AEMeasurable F volume) (hL : AEMeasurable L volume)
    (h : phaseSlice (timeWeightedDensity a b C F) t =
      phaseSlice (timeWeightedDensity a b C F) s+
        phaseIncrement (timeWeightedSource a b C μ+
          positiveDensityMeasure volume (dampedResidual a b C F L)) s t) :
    phaseSlice F t = ENNReal.ofReal (Real.exp (C*(s-t))) • phaseSlice F s+
      dampedSourceIncrement a b C s t
        (μ+positiveDensityMeasure volume (fun z => C*F z-L z)) := by
  rw [dampedResidual_source hF hL,← timeWeightedSource_add] at h
  exact undamp_measure_balance F _ hs ht h

end BoltzmannNonuniqueness.WeakTime

end

end

section

/-! # Initial phase measures and their free-flight occupation -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.WeakTime

def phaseSeed (s : ℝ) (μ : Measure Phase) : Measure (ℝ × Phase) :=
  μ.map (fun p => (s,p))

instance phaseSeed_sFinite (s : ℝ) (μ : Measure Phase) [SFinite μ] : SFinite (phaseSeed s μ) := by
  unfold phaseSeed
  infer_instance

theorem residence_seed_lintegral (C b s : ℝ) (μ : Measure Phase) [SFinite μ]
    {f : ℝ × Phase → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z, f z ∂(residenceKernel C b ∘ₘ phaseSeed s μ)) =
      ∫⁻ t in Ioc s b, ENNReal.ofReal (Real.exp (C*(s-t)))*(∫⁻ p, f (t,p) ∂μ) := by
  rw [Measure.lintegral_bind (Kernel.aemeasurable _) hf.aemeasurable,phaseSeed,
    lintegral_map hf.lintegral_kernel
      (show Measurable (fun p : Phase => (s,p)) from measurable_const.prodMk measurable_id)]
  simp_rw [residenceKernel_lintegral C b _ hf]
  have he : Measurable (fun q : Phase × ℝ => ENNReal.ofReal (Real.exp (C*(s-q.2)))) := by
    fun_prop
  have hm : Measurable (fun q : Phase × ℝ =>
      ENNReal.ofReal (Real.exp (C*(s-q.2)))*f (q.2,q.1)) :=
    he.mul (hf.comp measurable_swap)
  rw [lintegral_lintegral_swap hm.aemeasurable]
  apply setLIntegral_congr_fun measurableSet_Ioc
  intro t ht
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end BoltzmannNonuniqueness.WeakTime

end

end

section

/-! # Terminal phase slices of a positive source history -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.WeakTime

def phaseEndpointKernel (C t : ℝ) : Kernel (ℝ × Phase) Phase :=
  (Kernel.deterministic Prod.snd measurable_snd).withDensity
    (fun z _ => ENNReal.ofReal (Real.exp (C*(z.1-t))))

instance phaseEndpointKernel_sFinite (C t : ℝ) : IsSFiniteKernel (phaseEndpointKernel C t) :=
  Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)

theorem phaseEndpointKernel_lintegral (C t : ℝ) (z : ℝ × Phase)
    {f : Phase → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ p, f p ∂phaseEndpointKernel C t z) =
      ENNReal.ofReal (Real.exp (C*(z.1-t)))*f z.2 := by
  have hm : Measurable (Function.uncurry (fun (z : ℝ × Phase) (_ : Phase) =>
      ENNReal.ofReal (Real.exp (C*(z.1-t))))) := by fun_prop
  rw [phaseEndpointKernel,Kernel.lintegral_withDensity _ hm z hf,
    Kernel.deterministic_apply,lintegral_dirac']
  exact measurable_const.mul hf

theorem endpoint_source_comp (μ : Measure (ℝ × Phase))
    {a B C s t : ℝ} (hs : a < s) (ht : t < B) :
    phaseEndpointKernel C t ∘ₘ μ.restrict (Prod.fst ⁻¹' Ioc s t) =
      dampedSourceIncrement a B C s t μ := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Measure.lintegral_bind (Kernel.aemeasurable _) hf.aemeasurable,
    dampedSourceIncrement_lintegral μ hs ht hf]
  apply setLIntegral_congr_fun (measurable_fst measurableSet_Ioc)
  intro z hz
  dsimp only
  rw [phaseEndpointKernel_lintegral C t z hf,
    show C*(z.1-t) = -C*(t-z.1) by ring]

theorem endpoint_seed_comp (C t s : ℝ) (μ : Measure Phase) :
    phaseEndpointKernel C t ∘ₘ phaseSeed s μ =
      ENNReal.ofReal (Real.exp (C*(s-t))) • μ := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Measure.lintegral_bind (Kernel.aemeasurable _) hf.aemeasurable,phaseSeed,
    lintegral_map hf.lintegral_kernel
      (show Measurable (fun p : Phase => (s,p)) from measurable_const.prodMk measurable_id),
    lintegral_smul_measure,smul_eq_mul]
  simp_rw [phaseEndpointKernel_lintegral C t _ hf]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end BoltzmannNonuniqueness.WeakTime

end

end

section

/-! # Interchanging source time and observation time in the damped flow -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.WeakTime

theorem triangular_time_integral (s b r : ℝ) (g : ℝ → ℝ≥0∞) :
    (∫⁻ t in Ioc s b, (Ioc s t).indicator (fun _ => g t) r) =
      (Ioc s b).indicator (fun r => ∫⁻ t in Ioc r b, g t) r := by
  by_cases hr : r ∈ Ioc s b
  · rw [indicator_of_mem hr,← lintegral_indicator measurableSet_Ioc,
      ← lintegral_indicator measurableSet_Ioc]
    apply lintegral_congr_ae
    filter_upwards [Measure.ae_ne (volume : Measure ℝ) r] with t htr
    by_cases ht : t ∈ Ioc r b
    · have hsb : t ∈ Ioc s b := ⟨hr.1.trans ht.1,ht.2⟩
      have hst : r ∈ Ioc s t := ⟨hr.1,ht.1.le⟩
      simp [ht,hsb,hst]
    · by_cases hsb : t ∈ Ioc s b
      · have hst : r ∉ Ioc s t := by
          intro hst
          apply ht
          exact ⟨lt_of_le_of_ne hst.2 (Ne.symm htr),hsb.2⟩
        simp [ht,hsb,hst]
      · simp [ht,hsb]
  · rw [indicator_of_notMem hr]
    apply setLIntegral_eq_zero measurableSet_Ioc
    intro t ht
    have hst : r ∉ Ioc s t := fun hst => hr ⟨hst.1,hst.2.trans ht.2⟩
    simp [hst]

end BoltzmannNonuniqueness.WeakTime

end

end

section

/-! # Time-integrated Duhamel sources are residence-kernel measures -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.WeakTime

theorem dampedSource_time_integral (μ : Measure (ℝ × Phase)) [SFinite μ]
    {a B C s b : ℝ} (hs : a < s) (hb : b < B)
    {f : ℝ × Phase → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ t in Ioc s b, ∫⁻ p, f (t,p) ∂dampedSourceIncrement a B C s t μ) =
      ∫⁻ p, f p ∂(residenceKernel C b ∘ₘ μ.restrict (Prod.fst ⁻¹' Ioc s b)) := by
  let G : ℝ × (ℝ × Phase) → ℝ≥0∞ := fun q =>
    (Ioc s q.1).indicator
      (fun _ => ENNReal.ofReal (Real.exp (C*(q.2.1-q.1)))*f (q.1,q.2.2)) q.2.1
  have hg : Measurable G := by
    have hset : MeasurableSet {q : ℝ × (ℝ × Phase) | s < q.2.1 ∧ q.2.1 ≤ q.1} :=
      (measurableSet_lt measurable_const measurable_snd.fst).inter
        (measurableSet_le measurable_snd.fst measurable_fst)
    have hexp : Measurable (fun q : ℝ × (ℝ × Phase) =>
        ENNReal.ofReal (Real.exp (C*(q.2.1-q.1)))) := by fun_prop
    have hv : Measurable (fun q : ℝ × (ℝ × Phase) =>
        ENNReal.ofReal (Real.exp (C*(q.2.1-q.1)))*f (q.1,q.2.2)) :=
      hexp.mul (hf.comp (measurable_fst.prodMk measurable_snd.snd))
    have he : G = {q : ℝ × (ℝ × Phase) | s < q.2.1 ∧ q.2.1 ≤ q.1}.indicator
        (fun q => ENNReal.ofReal (Real.exp (C*(q.2.1-q.1)))*f (q.1,q.2.2)) := by
      funext q
      by_cases hq : s < q.2.1 ∧ q.2.1 ≤ q.1 <;> simp [G,hq]
    rw [he]
    exact hv.indicator hset
  calc
    _ = ∫⁻ t in Ioc s b, ∫⁻ z, G (t,z) ∂μ := by
      apply setLIntegral_congr_fun measurableSet_Ioc
      intro t ht
      dsimp only
      rw [dampedSourceIncrement_lintegral μ hs (ht.2.trans_lt hb)
        (ψ := fun p => f (t,p)) (hf.comp (measurable_const.prodMk measurable_id)),
        ← lintegral_indicator (measurable_fst measurableSet_Ioc)]
      apply lintegral_congr
      intro z
      by_cases hz : z.1 ∈ Ioc s t
      · have hz' : z ∈ Prod.fst ⁻¹' Ioc s t := hz
        simp only [G,indicator_of_mem hz,indicator_of_mem hz']
        rw [show -C*(t-z.1) = C*(z.1-t) by ring]
      · have hz' : z ∉ Prod.fst ⁻¹' Ioc s t := hz
        simp only [G,indicator_of_notMem hz,indicator_of_notMem hz']
    _ = ∫⁻ z, ∫⁻ t in Ioc s b, G (t,z) ∂volume ∂μ :=
      lintegral_lintegral_swap hg.aemeasurable
    _ = ∫⁻ z in Prod.fst ⁻¹' Ioc s b,
        ∫⁻ t in Ioc z.1 b, ENNReal.ofReal (Real.exp (C*(z.1-t)))*f (t,z.2) ∂volume ∂μ := by
      rw [← lintegral_indicator (measurable_fst measurableSet_Ioc)]
      apply lintegral_congr
      intro z
      exact triangular_time_integral s b z.1 _
    _ = _ := by
      rw [Measure.lintegral_bind (Kernel.aemeasurable _) hf.aemeasurable]
      apply setLIntegral_congr_fun (measurable_fst measurableSet_Ioc)
      intro z hz
      exact (residenceKernel_lintegral C b z hf).symm

end BoltzmannNonuniqueness.WeakTime

end

end

section

/-! # Integrating a Duhamel trace into a positive occupation equation -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.WeakTime

theorem occupation_eq_residence {F : ℝ × Phase → ℝ} (hF : Measurable F)
    (seed : Measure Phase) [SFinite seed] (source : Measure (ℝ × Phase)) [SFinite source]
    {a B C s b : ℝ} (hs : a < s) (hb : b < B)
    (h : ∀ᵐ t ∂volume, t ∈ Ioc s b →
      phaseSlice F t = ENNReal.ofReal (Real.exp (C*(s-t))) • seed+
        dampedSourceIncrement a B C s t source) :
    (positiveDensityMeasure volume F).restrict (Prod.fst ⁻¹' Ioc s b) =
      residenceKernel C b ∘ₘ (phaseSeed s seed+source.restrict (Prod.fst ⁻¹' Ioc s b)) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [occupation_slice_lintegral hF s b hf,Measure.comp_add,lintegral_add_measure,
    residence_seed_lintegral C b s seed hf,← dampedSource_time_integral source hs hb hf]
  have he : Measurable (fun t : ℝ => ENNReal.ofReal (Real.exp (C*(s-t)))) := by fun_prop
  have hm : Measurable (fun t =>
      ENNReal.ofReal (Real.exp (C*(s-t)))*(∫⁻ p, f (t,p) ∂seed)) :=
    he.mul (hf.lintegral_prod_right' (ν := seed))
  rw [← lintegral_add_left hm]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae h,ae_restrict_mem measurableSet_Ioc] with t ht htb
  rw [ht htb,lintegral_add_measure,lintegral_smul_measure,smul_eq_mul]

end BoltzmannNonuniqueness.WeakTime

end

end

section

/-! # Endpoint domination by every finite positive history sum -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.WeakTime

theorem endpoint_finite_histories (K R : Kernel (ℝ × Phase) (ℝ × Phase))
    (occupation source : Measure (ℝ × Phase)) (seed endpoint : Measure Phase)
    {a B C s t : ℝ} (hs : a < s) (ht : t < B)
    (hoccupation : occupation.restrict (Prod.fst ⁻¹' Ioc s t) =
      R ∘ₘ (phaseSeed s seed+source.restrict (Prod.fst ⁻¹' Ioc s t)))
    (hsource : K ∘ₘ occupation ≤ source)
    (hendpoint : endpoint = ENNReal.ofReal (Real.exp (C*(s-t))) • seed+
      dampedSourceIncrement a B C s t source) (n : ℕ) :
    phaseEndpointKernel C t ∘ₘ
      (∑ j ∈ Finset.range n,
        ((((K.restrict (measurable_fst measurableSet_Ioc :
          MeasurableSet (Prod.fst ⁻¹' Ioc s t))) ∘ₖ R)^j) ∘ₘ phaseSeed s seed)) ≤ endpoint := by
  have hrenew := PositiveMeasureHistories.restricted_source_renewal K R
    (measurable_fst measurableSet_Ioc) hoccupation hsource
  have hh := PositiveMeasureHistories.endpoint_histories_le _ (phaseEndpointKernel C t) hrenew n
  rw [Measure.comp_add,endpoint_seed_comp,endpoint_source_comp source hs ht,← hendpoint] at hh
  exact hh

end BoltzmannNonuniqueness.WeakTime

end

end

end OAI
