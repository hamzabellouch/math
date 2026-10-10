import OAI.MathematicalPhysics.Boltzmann.Branching.BoundedCollisionBlocks
import OAI.MathematicalPhysics.Boltzmann.Branching.MediumStateCollision
import OAI.MathematicalPhysics.Boltzmann.Branching.NormalGainMeasureActions
import OAI.MathematicalPhysics.Boltzmann.Collision.KernelConjugacy
import OAI.MathematicalPhysics.Boltzmann.Compactness.PhysicalGlobalRenormalized
import OAI.MathematicalPhysics.Boltzmann.Jets.BeamNormalOutgoing

namespace OAI

section

/-! # Equal scaled partner measures give equal scaled normal-angle gains -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem normalGainKernel_smul_eq_of_measure_smul_eq
    (K : Kernel X Velocity) (L : Kernel Y Velocity) [IsSFiniteKernel K] [IsSFiniteKernel L]
    (x : X) (y : Y) (v : Velocity) (c d : ℝ≥0∞) (h : c • K x = d • L y) :
    c • normalGainKernel K (x,v) = d • normalGainKernel L (y,v) := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hl := congrArg (fun μ : Measure Velocity => ∫⁻ w, ∫⁻ ω,
    ENNReal.ofReal (collisionKernel w v ω)*f (scatterLeft w v ω) ∂sphereArea ∂μ) h
  have hr := congrArg (fun μ : Measure Velocity => ∫⁻ w, ∫⁻ ω,
    ENNReal.ofReal (collisionKernel w v ω)*f (scatterRight w v ω) ∂sphereArea ∂μ) h
  simp only [lintegral_smul_measure,smul_eq_mul] at hl hr
  rw [lintegral_smul_measure,lintegral_smul_measure,smul_eq_mul,smul_eq_mul,
    normalGainKernel_lintegral K (x,v) hf,normalGainKernel_lintegral L (y,v) hf,
    mul_add,mul_add,hl,hr]

end BoltzmannNonuniqueness

end

end

section

/-! # Positive collision-time integrals under the local density scale -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem scaled_time_lintegral {ρ : ℝ} (hρ : 0 < ρ) (a : ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ s in Ioc 0 a, ENNReal.ofReal ρ*f (ρ*s)) =
      ∫⁻ t in Ioc 0 (ρ*a), f t := by
  have hm : MeasurePreserving (fun s : ℝ => ρ*s)
      (ENNReal.ofReal ρ • (volume : Measure ℝ)) volume := by
    refine ⟨by fun_prop,?_⟩
    rw [Measure.map_smul _ (show Measurable (fun s : ℝ => ρ*s) by fun_prop).aemeasurable]
    simpa only [abs_of_pos hρ] using Real.smul_map_volume_mul_left hρ.ne'
  have hs : (fun s : ℝ => ρ*s) ⁻¹' Ioc 0 (ρ*a) = Ioc 0 a := by
    ext s
    simp only [mem_preimage,mem_Ioc]
    constructor
    · rintro ⟨h₁,h₂⟩
      constructor <;> nlinarith
    · rintro ⟨h₁,h₂⟩
      exact ⟨mul_pos hρ h₁,mul_le_mul_of_nonneg_left h₂ hρ.le⟩
  have H := hm.setLIntegral_comp_preimage (s := Ioc 0 (ρ*a)) measurableSet_Ioc hf
  rw [hs,Measure.restrict_smul,lintegral_smul_measure,smul_eq_mul] at H
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact H

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Exact local density normalization of physical flight states -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def flightScaleEquiv (ρ : ℝ) (hρ : ρ ≠ 0) (x₀ : V) :
    PhysicalFlightState ≃ᵐ PhysicalFlightState where
  toFun p := (ρ*p.1,(ρ • (p.2.1-x₀),p.2.2))
  invFun p := (p.1/ρ,(x₀+ρ⁻¹ • p.2.1,p.2.2))
  left_inv p := by
    apply Prod.ext
    · simp [hρ]
    · apply Prod.ext
      · simp [smul_smul,hρ]
      · rfl
  right_inv p := by
    apply Prod.ext
    · field_simp
    · apply Prod.ext
      · simp [smul_smul,hρ]
      · rfl
  measurable_toFun := by
    change Measurable (fun p : PhysicalFlightState => (ρ*p.1,(ρ • (p.2.1-x₀),p.2.2)))
    fun_prop
  measurable_invFun := by
    change Measurable (fun p : PhysicalFlightState => (p.1/ρ,(x₀+ρ⁻¹ • p.2.1,p.2.2)))
    fun_prop

theorem flightScale_advance (ρ : ℝ) (hρ : ρ ≠ 0) (x₀ : V)
    (p : PhysicalFlightState) (s : ℝ) :
    flightScaleEquiv ρ hρ x₀ (physicalAdvance p s) =
      physicalAdvance (flightScaleEquiv ρ hρ x₀ p) (ρ*s) := by
  apply Prod.ext
  · dsimp [flightScaleEquiv,physicalAdvance]
    ring
  · apply Prod.ext
    · dsimp [flightScaleEquiv,physicalAdvance]
      module
    · rfl

theorem normalized_mediumPoint (ρ : ℝ) (hρ : ρ ≠ 0) (t₀ endTime : ℝ) (x₀ : V)
    (p : PhysicalFlightState) (s : ℝ) :
    normalizedPoint ρ t₀ x₀
      (mediumPoint (ρ*(endTime-t₀)) (flightScaleEquiv ρ hρ x₀ p) (ρ*s)) =
      mediumPoint endTime p s := by
  apply Prod.ext
  · dsimp [normalizedPoint,mediumPoint,flightScaleEquiv]
    field_simp
    ring
  · dsimp [normalizedPoint,mediumPoint,flightScaleEquiv]
    rw [show ρ • (p.2.1-x₀)+(ρ*s) • p.2.2 =
      ρ • (p.2.1-x₀+s • p.2.2) by module,smul_smul,inv_mul_cancel₀ hρ,one_smul]
    abel

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The density-scaled waiting kernel has the reference clock -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem scaled_waiting_lintegral (C : ℝ≥0) {ρ : ℝ} (hρ : 0 < ρ) (x₀ : V)
    (p : PhysicalFlightState) {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) :
    ENNReal.ofReal ρ * (∫⁻ q, F (flightScaleEquiv ρ hρ.ne' x₀ q)
      ∂physicalWaitingKernel (Real.toNNReal ρ*C) p) =
      ∫⁻ q, F q ∂physicalWaitingKernel C (flightScaleEquiv ρ hρ.ne' x₀ p) := by
  let e := flightScaleEquiv ρ hρ.ne' x₀
  have hc : Measurable (fun q => F (e q)) := hF.comp e.measurable
  have hf : Measurable (fun s : ℝ => clockSurvival C s * F (physicalAdvance (e p) s)) :=
    (show Measurable (clockSurvival C) by unfold clockSurvival; fun_prop).mul
      (hF.comp (physicalAdvance_measurable.comp (measurable_const.prodMk measurable_id)))
  rw [physicalWaitingKernel_lintegral _ _ hc,physicalWaitingKernel_lintegral _ _ hF]
  change ENNReal.ofReal ρ * (∫⁻ s in Ioc 0 p.1,
    clockSurvival (Real.toNNReal ρ*C) s * F (e (physicalAdvance p s))) =
      ∫⁻ s in Ioc 0 (ρ*p.1), clockSurvival C s * F (physicalAdvance (e p) s)
  rw [← scaled_time_lintegral hρ p.1 hf,← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro s
  have he := flightScale_advance ρ hρ.ne' x₀ p s
  change e (physicalAdvance p s) = physicalAdvance (e p) (ρ*s) at he
  rw [he]
  congr 2
  unfold clockSurvival
  congr 2
  push_cast
  rw [Real.coe_toNNReal _ hρ.le]
  ring

theorem scaled_waiting_map (C : ℝ≥0) {ρ : ℝ} (hρ : 0 < ρ) (x₀ : V)
    (p : PhysicalFlightState) :
    (ENNReal.ofReal ρ • physicalWaitingKernel (Real.toNNReal ρ*C) p).map
      (flightScaleEquiv ρ hρ.ne' x₀) =
      physicalWaitingKernel C (flightScaleEquiv ρ hρ.ne' x₀ p) := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (flightScaleEquiv ρ hρ.ne' x₀).measurable,
    lintegral_smul_measure,smul_eq_mul]
  exact scaled_waiting_lintegral C hρ x₀ p hF

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The measurable two-beam collision law under local density normalization -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem mediumCollisionKernel_normalized (b : BeamCoefficients) (ρ t₀ : ℝ) (x₀ : V)
    (z : MediumState) :
    mediumCollisionKernel (b.normalized ρ t₀ x₀) z =
      mediumCollisionKernel b (normalizedPoint ρ t₀ x₀ z.1,z.2) := by
  rw [mediumCollisionKernel_projection,mediumCollisionKernel_projection]
  rfl

theorem normalized_flight_location (ρ : ℝ) (hρ : ρ ≠ 0) (t₀ endTime : ℝ) (x₀ : V)
    (p : PhysicalFlightState) :
    normalizedPoint ρ t₀ x₀
      (ρ*(endTime-t₀)-(flightScaleEquiv ρ hρ x₀ p).1,
        (flightScaleEquiv ρ hρ x₀ p).2.1) = (endTime-p.1,p.2.1) := by
  simpa only [mediumPoint,mul_zero,zero_add,add_zero,zero_smul] using
    normalized_mediumPoint ρ hρ t₀ endTime x₀ p 0

theorem mediumStateCollision_scale_map (b : BeamCoefficients) (ρ : ℝ) (hρ : ρ ≠ 0)
    (t₀ endTime : ℝ) (x₀ : V) (p : PhysicalFlightState) :
    (mediumStateCollision b endTime p).map (flightScaleEquiv ρ hρ x₀) =
      mediumStateCollision (b.normalized ρ t₀ x₀) (ρ*(endTime-t₀))
        (flightScaleEquiv ρ hρ x₀ p) := by
  apply Measure.ext_of_lintegral
  intro F hF
  have hc : Measurable (fun q => F (flightScaleEquiv ρ hρ x₀ q)) :=
    hF.comp (flightScaleEquiv ρ hρ x₀).measurable
  rw [lintegral_map hF (flightScaleEquiv ρ hρ x₀).measurable,
    mediumStateCollision_lintegral b endTime p hc,
    mediumStateCollision_lintegral _ _ _ hF,
    mediumCollisionKernel_normalized,normalized_flight_location]
  rfl

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The physical collision intensity and clock normalize by the same density -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def densityScaledCollision (b : BeamCoefficients) (endTime : ℝ) (ρ : ℝ≥0) :
    Kernel PhysicalFlightState PhysicalFlightState :=
  (mediumStateCollision b endTime).withDensity (fun _ _ => ENNReal.ofReal (ρ : ℝ))

instance densityScaledCollision_sFinite (b : BeamCoefficients) (endTime : ℝ) (ρ : ℝ≥0) :
    IsSFiniteKernel (densityScaledCollision b endTime ρ) := by
  apply Kernel.IsSFiniteKernel.withDensity
  intro p q
  exact ENNReal.ofReal_ne_top

theorem densityScaledCollision_lintegral (b : BeamCoefficients) (endTime : ℝ) (ρ : ℝ≥0)
    (p : PhysicalFlightState) {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂densityScaledCollision b endTime ρ p) =
      ENNReal.ofReal (ρ : ℝ) * ∫⁻ q, F q ∂mediumStateCollision b endTime p := by
  rw [densityScaledCollision,Kernel.lintegral_withDensity _ (by fun_prop) p hF,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

def densityScaledEventKernel (b : BeamCoefficients) (endTime : ℝ) (ρ : ℝ≥0) :
    Kernel PhysicalFlightState PhysicalFlightState :=
  densityScaledCollision b endTime ρ ∘ₖ physicalWaitingKernel (ρ*referenceClock)

instance densityScaledEventKernel_sFinite (b : BeamCoefficients) (endTime : ℝ) (ρ : ℝ≥0) :
    IsSFiniteKernel (densityScaledEventKernel b endTime ρ) := by
  unfold densityScaledEventKernel
  infer_instance

theorem densityScaledEvent_scale_map (b : BeamCoefficients) {ρ : ℝ} (hρ : 0 < ρ)
    (t₀ endTime : ℝ) (x₀ : V) (p : PhysicalFlightState) :
    (densityScaledEventKernel b endTime (Real.toNNReal ρ) p).map (flightScaleEquiv ρ hρ.ne' x₀) =
      (mediumStateCollision (b.normalized ρ t₀ x₀) (ρ*(endTime-t₀)) ∘ₖ
        physicalWaitingKernel referenceClock) (flightScaleEquiv ρ hρ.ne' x₀ p) := by
  apply Measure.ext_of_lintegral
  intro F hF
  let e := flightScaleEquiv ρ hρ.ne' x₀
  let L := mediumStateCollision (b.normalized ρ t₀ x₀) (ρ*(endTime-t₀))
  have hc : Measurable (fun q => F (e q)) := hF.comp e.measurable
  have he (q : PhysicalFlightState) :
      (∫⁻ r, F (e r) ∂mediumStateCollision b endTime q) = ∫⁻ r, F r ∂L (e q) := by
    rw [← lintegral_map hF e.measurable,mediumStateCollision_scale_map b ρ hρ.ne' t₀ endTime x₀ q]
  rw [lintegral_map hF e.measurable,densityScaledEventKernel,Kernel.lintegral_comp _ _ _ hc,
    Kernel.lintegral_comp _ _ _ hF]
  simp_rw [densityScaledCollision_lintegral b endTime _ _ hc,he]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [Real.coe_toNNReal _ hρ.le]
  exact scaled_waiting_lintegral referenceClock hρ x₀ p (hF.lintegral_kernel (κ := L))

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Local density normalization preserves the bounded physical event histories -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def boundedDensityScaledEvent (b : BeamCoefficients) (endTime : ℝ) (ρ : ℝ≥0) :
    Kernel PhysicalFlightState PhysicalFlightState :=
  (densityScaledEventKernel b endTime ρ).restrict mediumVelocityBox_measurable

instance boundedDensityScaledEvent_sFinite (b : BeamCoefficients) (endTime : ℝ) (ρ : ℝ≥0) :
    IsSFiniteKernel (boundedDensityScaledEvent b endTime ρ) := by
  unfold boundedDensityScaledEvent
  infer_instance

def boundedPhysicalEvent (b : BeamCoefficients) (endTime : ℝ) :
    Kernel PhysicalFlightState PhysicalFlightState :=
  (mediumStateCollision b endTime ∘ₖ physicalWaitingKernel referenceClock).restrict
    mediumVelocityBox_measurable

instance boundedPhysicalEvent_sFinite (b : BeamCoefficients) (endTime : ℝ) :
    IsSFiniteKernel (boundedPhysicalEvent b endTime) := by
  unfold boundedPhysicalEvent
  infer_instance

theorem boundedDensityScaledEvent_map (b : BeamCoefficients) {ρ : ℝ} (hρ : 0 < ρ)
    (t₀ endTime : ℝ) (x₀ : V) (p : PhysicalFlightState) :
    (boundedDensityScaledEvent b endTime (Real.toNNReal ρ) p).map
      (flightScaleEquiv ρ hρ.ne' x₀) =
      boundedPhysicalEvent (b.normalized ρ t₀ x₀) (ρ*(endTime-t₀))
        (flightScaleEquiv ρ hρ.ne' x₀ p) := by
  have hs : (flightScaleEquiv ρ hρ.ne' x₀) ⁻¹' mediumVelocityBox = mediumVelocityBox := rfl
  rw [boundedDensityScaledEvent,Kernel.restrict_apply,← hs,
    ← Measure.restrict_map (flightScaleEquiv ρ hρ.ne' x₀).measurable mediumVelocityBox_measurable,
    densityScaledEvent_scale_map b hρ t₀ endTime x₀ p]
  rfl

theorem boundedDensityScaledEvent_pow_map (b : BeamCoefficients) {ρ : ℝ} (hρ : 0 < ρ)
    (t₀ endTime : ℝ) (x₀ : V) (n : ℕ) (p : PhysicalFlightState) :
    (((boundedDensityScaledEvent b endTime (Real.toNNReal ρ))^n) p).map
      (flightScaleEquiv ρ hρ.ne' x₀) =
      ((boundedPhysicalEvent (b.normalized ρ t₀ x₀) (ρ*(endTime-t₀)))^n)
        (flightScaleEquiv ρ hρ.ne' x₀ p) :=
  kernel_pow_map (flightScaleEquiv ρ hρ.ne' x₀) _ _
    (boundedDensityScaledEvent_map b hρ t₀ endTime x₀) n p

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
