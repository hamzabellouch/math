import OAI.MathematicalPhysics.Boltzmann.Approximation.RegularizedEntropyIntegrability
import OAI.MathematicalPhysics.Boltzmann.Branching.MediumStateCollision
import OAI.MathematicalPhysics.Boltzmann.Branching.PerturbedFiniteBlock
import OAI.MathematicalPhysics.Boltzmann.Collision.ScalarEntropyConvex
import OAI.MathematicalPhysics.Boltzmann.Compactness.PhysicalEntropyProduction
import OAI.MathematicalPhysics.Boltzmann.Jets.TorusTransport
import OAI.MathematicalPhysics.Boltzmann.Model
import Mathlib.Analysis.Normed.Lp.lpSpace

namespace OAI

section

/-! # Integrability of the finite cutoff source in Eulerian and characteristic coordinates -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

namespace CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem bounded_cutoff_source_integrable (hcarleman : Published.GPV2009CarlemanInput)
    {μ : Measure X} [IsFiniteMeasure μ] {q A b : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hA : 0 ≤ A) (hb : 0 ≤ b)
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hfn : ∀ z, 0 ≤ f z)
    (hfb : ∀ z, f z ≤ A*H q z.2) : Integrable (collisionSource b f) (μ.prod volume) := by
  have hgain : Integrable (KineticCollisionNullSets.gain b f) (μ.prod (volume : Measure Velocity)) := by
    apply (((integrable_H hq₂).const_mul (A^2*HotApplication.realBound q)).comp_snd μ).mono'
      (KineticCollisionNullSets.measurable_gain hfm b).aestronglyMeasurable
    filter_upwards [bounded_cutoff_gain hcarleman hq₁ hq₂ hA hfm hfn hfb b] with z hz
    rw [Real.norm_of_nonneg (cutoffGainDensity_nonneg hfn b z)]
    exact hz
  have hloss : Integrable (cutoffLossDensity b f) (μ.prod (volume : Measure Velocity)) := by
    apply (((integrable_H hq₂).const_mul (A^2*CutoffLipschitz.frequencyConstant q b)).comp_snd μ).mono'
      (cutoffLossDensity_measurable hfm b).aestronglyMeasurable
    filter_upwards [bounded_cutoff_loss hq₂ hA hb hfm hfn hfb] with z hz
    rw [Real.norm_of_nonneg (cutoffLossDensity_nonneg hfn b z)]
    exact hz
  have hpair := bounded_pair_integrable (μ := μ) hq₂ hA hfm hfn hfb
  apply (hgain.sub hloss).congr
  filter_upwards [cutoff_loss_ae_eq_frequency hfm hfn hpair b] with z hz
  change KineticCollisionNullSets.gain b f z-cutoffLossDensity b f z = _
  rw [hz]
  rfl

end CollisionCompactness

theorem cutoffPhysicalSource_eq (b : ℝ) (F : Evolution) :
    cutoffPhysicalSource b F = fun z : ℝ × Phase =>
      CollisionCompactness.collisionSource b (kineticDensity F) ((z.1,z.2.1),z.2.2) := rfl

theorem cutoffPhysicalSource_measurable {F : Evolution}
    (hFm : Measurable (fun z : ℝ × Phase => F z.1 z.2)) (b : ℝ) :
    Measurable (cutoffPhysicalSource b F) := by
  rw [cutoffPhysicalSource_eq]
  have hkin : Measurable (kineticDensity F) := hFm.comp MeasurableEquiv.prodAssoc.measurable
  have hs : Measurable (CollisionCompactness.collisionSource b (kineticDensity F)) :=
    CollisionCompactness.collisionSource_measurable hkin b
  exact hs.comp ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd)

theorem cutoffPhysicalSource_integrable (hcarleman : Published.GPV2009CarlemanInput)
    {T q A b : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hA : 0 ≤ A) (hb : 0 ≤ b)
    {F : Evolution} (hFm : Measurable (fun z : ℝ × Phase => F z.1 z.2))
    (hFn : ∀ t p, 0 ≤ F t p) (hFb : ∀ t p, F t p ≤ A*H q p.2) :
    Integrable (cutoffPhysicalSource b F) ((volume.restrict (Icc 0 T)).prod volume) := by
  have h := CollisionCompactness.bounded_cutoff_source_integrable
    (μ := AnnularEnvelope.timePositionVolume T) (f := kineticDensity F) hcarleman hq₁ hq₂ hA hb
    (hFm.comp MeasurableEquiv.prodAssoc.measurable) (fun z => hFn _ _) (fun z => hFb _ _)
  exact (kineticGrouping_measurePreserving (volume.restrict (Icc 0 T))).symm.integrable_comp_of_integrable h

theorem cutoffCharacteristicSource_integrable (hcarleman : Published.GPV2009CarlemanInput)
    {T q A b : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hA : 0 ≤ A) (hb : 0 ≤ b)
    {F : Evolution} (hFm : Measurable (fun z : ℝ × Phase => F z.1 z.2))
    (hFn : ∀ t p, 0 ≤ F t p) (hFb : ∀ t p, F t p ≤ A*H q p.2) :
    Integrable (TorusFlight.along (cutoffPhysicalSource b F))
      ((volume.restrict (Icc 0 T)).prod volume) :=
  (TorusFlight.along_measurePreserving _).integrable_comp_of_integrable
    (cutoffPhysicalSource_integrable hcarleman hq₁ hq₂ hA hb hFm hFn hFb)

end BoltzmannNonuniqueness

end

end

section

/-! # Complete sup-norm space of bounded measurable representatives

This space is used for the fixed-cutoff positive iteration. It retains
pointwise representatives, so every iterated collision integral is defined.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace BoltzmannNonuniqueness.BoundedMeasurable

variable (X : Type*) [MeasurableSpace X]

abbrev SupSpace := lp (fun _ : X => ℝ) ⊤

def measurableSet : Set (SupSpace X) := {f | Measurable (fun x => f x)}

theorem measurableSet_closed : IsClosed (measurableSet X) := by
  apply isSeqClosed_iff_isClosed.mp
  intro u f hu hf
  apply measurable_of_tendsto_metrizable (fun n => hu n)
  exact (lp.uniformContinuous_coe (p := ⊤)).continuous.tendsto f |>.comp hf

abbrev Space := {f : SupSpace X // f ∈ measurableSet X}

instance : CompleteSpace (Space X) := (measurableSet_closed X).isComplete.completeSpace_coe

instance : CoeFun (Space X) (fun _ => X → ℝ) := ⟨fun f => f.val⟩

theorem measurable (f : Space X) : Measurable (fun x => f x) := f.property

def ofBounded (f : X → ℝ) (hm : Measurable f) (C : ℝ) (hC : ∀ x, |f x| ≤ C) :
    Space X := ⟨⟨f, memℓp_infty ⟨C, by rintro _ ⟨x, rfl⟩; simpa only [Real.norm_eq_abs] using hC x⟩⟩, hm⟩

@[simp] theorem ofBounded_apply (f : X → ℝ) (hm : Measurable f) (C : ℝ)
    (hC : ∀ x, |f x| ≤ C) (x : X) : ofBounded X f hm C hC x = f x := rfl

theorem dist_apply_le (f g : Space X) (x : X) : |f x - g x| ≤ dist f g := by
  simpa only [Real.dist_eq, Subtype.dist_eq, NNReal.coe_one, one_mul] using
    (lp.lipschitzWith_one_eval (E := fun _ : X => ℝ) ⊤ x).dist_le_mul f.val g.val

theorem dist_le {f g : Space X} {C : ℝ} (hC : 0 ≤ C) (h : ∀ x, |f x - g x| ≤ C) :
    dist f g ≤ C := by
  change dist f.val g.val ≤ C
  rw [dist_eq_norm]
  apply lp.norm_le_of_forall_le hC
  intro x
  exact (Real.norm_eq_abs _).symm ▸ h x

def positiveBall (R : ℝ) : Set (Space X) := {f | ∀ x, 0 ≤ f x ∧ f x ≤ R}

theorem positiveBall_closed (R : ℝ) : IsClosed (positiveBall X R) := by
  have he (x : X) : Continuous (fun f : Space X => f x) :=
    (lp.lipschitzWith_one_eval (E := fun _ : X => ℝ) ⊤ x).continuous.comp continuous_subtype_val
  convert isClosed_iInter (fun x => (isClosed_le (f := fun _ => (0 : ℝ)) continuous_const (he x)).inter
    (isClosed_le (he x) (g := fun _ => R) continuous_const)) using 1
  ext f
  simp only [positiveBall, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_inter_iff]

abbrev PositiveBall (R : ℝ) := {f : Space X // f ∈ positiveBall X R}

instance (R : ℝ) : CompleteSpace (PositiveBall X R) :=
  (positiveBall_closed X R).isComplete.completeSpace_coe

end BoltzmannNonuniqueness.BoundedMeasurable

end

end

section

/-! # Finite medium words whose collision velocities stay in the physical box -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

def boundedMediumWordDensity (b : BeamCoefficients) (endTime : ℝ) :
    (n : ℕ) → PhysicalFlightState → ParameterWord n → ℝ≥0∞
  | 0,_,_ => 1
  | n+1,p,a =>
      let q := mediumParameterState b endTime p a.1
      mediumParameterDensity b endTime p a.1 *
        ({q : PhysicalFlightState | ‖q.2.2‖ ≤ 6}.indicator 1 q *
          boundedMediumWordDensity b endTime n q a.2)

theorem boundedMediumWordDensity_measurable (b : BeamCoefficients) (endTime : ℝ) (n : ℕ) :
    Measurable (fun q : PhysicalFlightState × ParameterWord n =>
      boundedMediumWordDensity b endTime n q.1 q.2) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hh : Measurable (fun q : PhysicalFlightState × ParameterWord (n+1) => (q.1,q.2.1)) := by
      fun_prop
    have hs : Measurable (fun q : PhysicalFlightState × ParameterWord (n+1) =>
        mediumParameterState b endTime q.1 q.2.1) :=
      (mediumParameterState_measurable b endTime).comp hh
    have ht : Measurable (fun q : PhysicalFlightState × ParameterWord (n+1) => q.2.2) := by
      fun_prop
    have hbox : Measurable ({q : PhysicalFlightState | ‖q.2.2‖ ≤ 6}.indicator
        (1 : PhysicalFlightState → ℝ≥0∞)) :=
      measurable_const.indicator (measurableSet_le (by fun_prop) measurable_const)
    exact ((mediumParameterDensity_measurable b endTime).comp hh).mul
      ((hbox.comp hs).mul (ih.comp (hs.prodMk ht)))

theorem boundedMediumWordDensity_eq (b : BeamCoefficients) (endTime : ℝ)
    (n : ℕ) {p : TimeFlightState} {q : PhysicalFlightState} (a : ParameterWord n)
    {δ ε : ℝ} (hbudget : δ+(n:ℝ)*ε ≤ 1)
    (hv : ‖q.2.2-p.2.2.1‖ ≤ δ)
    (ha : GoodReferenceWord n p a) (hb : WordNearby b endTime ε n q a) :
    boundedMediumWordDensity b endTime n q a = mediumWordDensity b endTime n q a := by
  induction n generalizing p q δ with
  | zero => rfl
  | succ n ih =>
    have hv' := medium_parameter_velocity_error b endTime ha.2.1 hv hb.1 hb.2.1
    have hbud' : (δ+ε)+(n:ℝ)*ε ≤ 1 := by
      push_cast at hbudget
      linarith
    have hε : 0 ≤ ε := (norm_nonneg _).trans hb.1
    have hδε : δ+ε ≤ 1 := by nlinarith
    have hnorm : ‖(mediumParameterState b endTime q a.1).2.2‖ ≤ 6 := by
      have hh := norm_add_le
        ((mediumParameterState b endTime q a.1).2.2-(markedParameterState p a.1).2.2.1)
        (markedParameterState p a.1).2.2.1
      rw [sub_add_cancel] at hh
      linarith [retainedState_norm (markedParameterState p a.1).2.2]
    change mediumParameterDensity b endTime q a.1 *
        ({q : PhysicalFlightState | ‖q.2.2‖ ≤ 6}.indicator 1
          (mediumParameterState b endTime q a.1) *
            boundedMediumWordDensity b endTime n (mediumParameterState b endTime q a.1) a.2) = _
    have hmem : mediumParameterState b endTime q a.1 ∈
        {q : PhysicalFlightState | ‖q.2.2‖ ≤ 6} := hnorm
    rw [indicator_of_mem hmem,Pi.one_apply,one_mul,
      ih a.2 hbud' hv' ha.2.2 hb.2.2.2.2]
    rfl

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The event kernel with all intermediate velocities in the physical box -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def mediumVelocityBox : Set PhysicalFlightState := {q | ‖q.2.2‖ ≤ 6}

theorem mediumVelocityBox_measurable : MeasurableSet mediumVelocityBox := by
  unfold mediumVelocityBox
  exact measurableSet_le (by fun_prop) measurable_const

def boundedMediumEventKernel (b : BeamCoefficients) (endTime T : ℝ) :
    Kernel PhysicalFlightState PhysicalFlightState :=
  (mediumEventKernel b endTime T).restrict mediumVelocityBox_measurable

instance boundedMediumEventKernel_sFinite (b : BeamCoefficients) (endTime T : ℝ) :
    IsSFiniteKernel (boundedMediumEventKernel b endTime T) := by
  unfold boundedMediumEventKernel
  infer_instance

theorem boundedMediumEventKernel_lintegral (b : BeamCoefficients) (endTime T : ℝ)
    (p : PhysicalFlightState) {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂boundedMediumEventKernel b endTime T p) =
      ∫⁻ a, mediumParameterDensity b endTime p a *
        (mediumVelocityBox.indicator 1 (mediumParameterState b endTime p a) *
          F (mediumParameterState b endTime p a)) ∂markedEventMeasure T := by
  rw [boundedMediumEventKernel,Kernel.lintegral_restrict,
    ← lintegral_indicator mediumVelocityBox_measurable,
    mediumEventKernel_lintegral b endTime T p (hF.indicator mediumVelocityBox_measurable)]
  apply lintegral_congr
  intro a
  by_cases ha : mediumParameterState b endTime p a ∈ mediumVelocityBox
  · simp [ha]
  · simp [ha]

instance boundedMediumEventKernel_pow_sFinite (b : BeamCoefficients) (endTime T : ℝ) (n : ℕ) :
    IsSFiniteKernel ((boundedMediumEventKernel b endTime T)^n) := by
  induction n with
  | zero => change IsSFiniteKernel Kernel.id; infer_instance
  | succ n ih =>
    rw [show (boundedMediumEventKernel b endTime T)^(n+1) =
        ((boundedMediumEventKernel b endTime T)^n) ∘ₖ boundedMediumEventKernel b endTime T by
      simpa only [pow_one] using Kernel.pow_add (boundedMediumEventKernel b endTime T) n 1]
    let _ := ih
    infer_instance

theorem boundedMediumWord_integral (b : BeamCoefficients) (endTime T : ℝ)
    {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) (n : ℕ) (p : PhysicalFlightState) :
    (∫⁻ a, boundedMediumWordDensity b endTime n p a * F (mediumWordState b endTime n p a)
      ∂parameterWordMeasure T n) = ∫⁻ q, F q ∂((boundedMediumEventKernel b endTime T)^n) p := by
  induction n generalizing p with
  | zero =>
    change (∫⁻ _a : PUnit, 1*F p ∂Measure.dirac PUnit.unit) = ∫⁻ q, F q ∂Kernel.id p
    simp [Kernel.id_apply,lintegral_dirac' _ hF]
  | succ n ih =>
    have hmap : Measurable (fun a : ParameterWord (n+1) => (p,a)) :=
      measurable_const.prodMk measurable_id
    have hd : Measurable (fun a : ParameterWord (n+1) => boundedMediumWordDensity b endTime (n+1) p a) :=
      (boundedMediumWordDensity_measurable b endTime (n+1)).comp hmap
    have hs : Measurable (fun a : ParameterWord (n+1) => mediumWordState b endTime (n+1) p a) :=
      (mediumWordState_measurable b endTime (n+1)).comp hmap
    have hm : Measurable (fun a : ParameterWord (n+1) =>
        boundedMediumWordDensity b endTime (n+1) p a * F (mediumWordState b endTime (n+1) p a)) :=
      hd.mul (hF.comp hs)
    rw [parameterWordMeasure,lintegral_prod _ hm.aemeasurable]
    rw [show (boundedMediumEventKernel b endTime T)^(n+1) =
        ((boundedMediumEventKernel b endTime T)^n) ∘ₖ boundedMediumEventKernel b endTime T by
      simpa only [pow_one] using Kernel.pow_add (boundedMediumEventKernel b endTime T) n 1,
      Kernel.lintegral_comp _ _ _ hF,
      boundedMediumEventKernel_lintegral b endTime T p
        (hF.lintegral_kernel (κ := (boundedMediumEventKernel b endTime T)^n))]
    apply lintegral_congr
    intro a
    change (∫⁻ w, (mediumParameterDensity b endTime p a *
        (mediumVelocityBox.indicator 1 (mediumParameterState b endTime p a) *
          boundedMediumWordDensity b endTime n (mediumParameterState b endTime p a) w)) *
        F (mediumWordState b endTime n (mediumParameterState b endTime p a) w)
          ∂parameterWordMeasure T n) = _
    have hb : mediumVelocityBox.indicator (1 : PhysicalFlightState → ℝ≥0∞)
        (mediumParameterState b endTime p a) ≠ ⊤ := by
      by_cases ha : mediumParameterState b endTime p a ∈ mediumVelocityBox <;> simp [ha]
    simp_rw [mul_assoc]
    rw [lintegral_const_mul' _ _ (mediumParameterDensity_ne_top b endTime p a),
      lintegral_const_mul' _ _ hb,ih]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Lower transfer of reference blocks with every velocity kept bounded -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

def boundedMediumBlockIntegrand (b : BeamCoefficients) (endTime : ℝ) (p : TimeFlightState)
    (κ d : ℝ) (n : ℕ) (a : ParameterWord n) : ℝ≥0∞ :=
  let q := mediumWordState b endTime n (embedFlightState p) a
  boundedMediumWordDensity b endTime n (embedFlightState p) a *
    (clockSurvival referenceClock q.1 *
      (physicalBlockTarget p.2.1 p.1 κ d).indicator 1 (finishMediumFlight q))

def boundedMediumBlockMass (b : BeamCoefficients) (endTime T : ℝ) (p : TimeFlightState)
    (κ d : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ∑ n ∈ Finset.range N,
    ∫⁻ a, boundedMediumBlockIntegrand b endTime p κ d n a ∂parameterWordMeasure T n

theorem bounded_medium_word_integrand_bound (b : BeamCoefficients) (endTime : ℝ)
    (n : ℕ) (p : TimeFlightState) (a : ParameterWord n) {ε κ d : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1/4) (hp : 0 ≤ p.1) (hv : (n:ℝ)*ε ≤ 1)
    (hx : 2*p.1*((n:ℝ)*ε) ≤ d*κ*p.1/4)
    (hnear : GoodReferenceWord n p a → WordNearby b endTime ε n (embedFlightState p) a) :
    parameterWordDensity n p a * flightSeed referenceClock
        ((blockTarget p.2.1 p.1 κ d).indicator 1) (parameterWordState n p a) ≤
      boundedMediumBlockIntegrand b endTime p κ d n a+historyPerturbationError n ε := by
  by_cases hr : parameterWordDensity n p a = 0
  · rw [hr,zero_mul]
    exact bot_le
  have ha := goodReferenceWord_of_density_ne_zero n p a hr
  have he := boundedMediumWordDensity_eq b endTime n a (δ := 0)
    (by simpa using hv) (by simp [embedFlightState]) ha (hnear ha)
  unfold boundedMediumBlockIntegrand
  rw [he]
  exact medium_word_integrand_bound b endTime n p a hε hε1 hp hv hx hnear

theorem bounded_medium_word_integral_lower (b : BeamCoefficients) (endTime : ℝ)
    (n : ℕ) (p : TimeFlightState) (T : ℝ) {ε κ d : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1/4) (hp : 0 ≤ p.1) (hpT : p.1 ≤ T)
    (hv : (n:ℝ)*ε ≤ 1) (hx : 2*p.1*((n:ℝ)*ε) ≤ d*κ*p.1/4)
    (hnear : ∀ a, GoodReferenceWord n p a → WordNearby b endTime ε n (embedFlightState p) a) :
    eventHistory referenceClock branchingKernel
        (flightSeed referenceClock ((blockTarget p.2.1 p.1 κ d).indicator 1)) n p ≤
      (∫⁻ a, boundedMediumBlockIntegrand b endTime p κ d n a ∂parameterWordMeasure T n)+
        historyPerturbationError n ε*(3*ENNReal.ofReal T)^n := by
  have hf : Measurable ((blockTarget p.2.1 p.1 κ d).indicator (1 : FlightState → ℝ≥0∞)) :=
    measurable_const.indicator (blockTarget_measurable _ _ _ _)
  rw [← parameterWord_integral (flightSeed_measurable referenceClock hf) T n p ⟨hp,hpT⟩]
  calc
    _ ≤ ∫⁻ a, boundedMediumBlockIntegrand b endTime p κ d n a+historyPerturbationError n ε
        ∂parameterWordMeasure T n :=
      lintegral_mono (fun a => bounded_medium_word_integrand_bound b endTime n p a
        hε hε1 hp hv hx (hnear a))
    _ = _ := by rw [lintegral_add_right _ measurable_const,lintegral_const,parameterWordMeasure_mass]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Endpoint measures for the bounded physical collision histories -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def boundedMediumEndpointKernel (b : BeamCoefficients) (endTime T : ℝ) (n : ℕ) :
    Kernel PhysicalFlightState (V × V) :=
  (Kernel.withDensity ((boundedMediumEventKernel b endTime T)^n)
    (fun _ p => clockSurvival referenceClock p.1)).map finishMediumFlight

instance boundedMediumEndpointKernel_isSFinite (b : BeamCoefficients) (endTime T : ℝ) (n : ℕ) :
    IsSFiniteKernel (boundedMediumEndpointKernel b endTime T n) := by
  have hs : IsSFiniteKernel (Kernel.withDensity ((boundedMediumEventKernel b endTime T)^n)
      (fun _ p => clockSurvival referenceClock p.1)) := by
    apply Kernel.IsSFiniteKernel.withDensity
    intro p q
    exact ENNReal.ofReal_ne_top
  unfold boundedMediumEndpointKernel
  infer_instance

theorem boundedMediumEndpointKernel_lintegral (b : BeamCoefficients) (endTime T : ℝ) (n : ℕ)
    (p : PhysicalFlightState) {F : V × V → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ y, F y ∂boundedMediumEndpointKernel b endTime T n p) =
      ∫⁻ q, mediumFlightSeed F q ∂((boundedMediumEventKernel b endTime T)^n) p := by
  have hc : Measurable (Function.uncurry (fun (_ : PhysicalFlightState) (q : PhysicalFlightState) =>
      clockSurvival referenceClock q.1)) := by unfold clockSurvival; fun_prop
  have hf : Measurable (fun q : PhysicalFlightState => F (finishMediumFlight q)) := by
    simpa only [Function.comp_def] using hF.comp finishMediumFlight_measurable
  rw [boundedMediumEndpointKernel,Kernel.lintegral_map _ finishMediumFlight_measurable p hF,
    Kernel.lintegral_withDensity _ hc p hf]
  rfl

theorem boundedMediumEndpointKernel_apply (b : BeamCoefficients) (endTime T : ℝ) (n : ℕ)
    (p : PhysicalFlightState) {A : Set (V × V)} (hA : MeasurableSet A) :
    boundedMediumEndpointKernel b endTime T n p A =
      ∫⁻ q, mediumFlightSeed (A.indicator 1) q ∂((boundedMediumEventKernel b endTime T)^n) p := by
  have H := boundedMediumEndpointKernel_lintegral b endTime T n p
    (measurable_const.indicator hA : Measurable (A.indicator (1 : V × V → ℝ≥0∞)))
  change (∫⁻ y, A.indicator (1 : V × V → ℝ≥0∞) y ∂boundedMediumEndpointKernel b endTime T n p) = _ at H
  rw [lintegral_indicator_one hA] at H
  exact H

theorem boundedMediumBlockMass_endpoints (b : BeamCoefficients) (endTime T : ℝ)
    (p : TimeFlightState) (κ d : ℝ) (N : ℕ) :
    boundedMediumBlockMass b endTime T p κ d N =
      ∑ n ∈ Finset.range N, boundedMediumEndpointKernel b endTime T n (embedFlightState p)
        (physicalBlockTarget p.2.1 p.1 κ d) := by
  unfold boundedMediumBlockMass
  apply Finset.sum_congr rfl
  intro n _hn
  rw [boundedMediumEndpointKernel_apply b endTime T n (embedFlightState p)
    (physicalBlockTarget_measurable _ _ _ _)]
  exact boundedMediumWord_integral b endTime T
    (mediumFlightSeed_measurable (measurable_const.indicator
      (physicalBlockTarget_measurable _ _ _ _))) n (embedFlightState p)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The regularized entropy balance for a bounded mild cutoff solution -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

def regularizedRelativeEntropyDensity (δ : ℝ) (f : Density) (p : Phase) : ℝ :=
  scalarRelativeEntropy (maxwellian p.2) (f p+δ*Real.exp (-2*‖p.2‖^2))

theorem regularizedRelativeEntropyDensity_integrable {q A δ : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hA : 0 ≤ A) (hδ : 0 < δ) (hδone : δ ≤ 1)
    {f : Density} (hfm : Measurable f) (hfn : ∀ p, 0 ≤ f p) (hfb : ∀ p, f p ≤ A*H q p.2) :
    Integrable (regularizedRelativeEntropyDensity δ f) := by
  rw [Measure.volume_eq_prod]
  exact regularized_relative_entropy_integrable hq₁ hq₂ hA hδ hδone hfm hfn hfb

theorem bounded_mild_entropy_balance (hcarleman : Published.GPV2009CarlemanInput)
    {T q A δ b : ℝ} (hT : 0 < T) (hq₁ : 1 < q) (hq₂ : q < 2) (hA : 0 ≤ A)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hb : 0 ≤ b)
    {F : Evolution} {a : Density}
    (hFm : Measurable (fun z : ℝ × Phase => F z.1 z.2))
    (hFn : ∀ t p, 0 ≤ F t p) (hFb : ∀ t p, F t p ≤ A*H q p.2)
    (ham : Measurable a) (han : ∀ p, 0 ≤ a p) (hab : ∀ p, a p ≤ A*H q p.2)
    (hchar : (fun z : ℝ × Phase => F z.1 (TorusFlight.flight z.1 z.2)) =ᵐ[
      (volume.restrict (Icc 0 T)).prod volume]
        (fun z => entropyPath a (TorusFlight.along (cutoffPhysicalSource b F)) z.1 z.2))
    (hcharT : (fun p => F T (TorusFlight.flight T p)) =ᵐ[volume]
      entropyPath a (TorusFlight.along (cutoffPhysicalSource b F)) T) :
    (∫ p, regularizedRelativeEntropyDensity δ (F T) p)-
      (∫ p, regularizedRelativeEntropyDensity δ a p) =
      ∫ z : ℝ × Phase, Real.log ((F z.1 z.2+δ*Real.exp (-2*‖z.2.2‖^2))/maxwellian z.2.2)*
        cutoffPhysicalSource b F z ∂(volume.restrict (Icc 0 T)).prod volume := by
  let μ : Measure ℝ := volume.restrict (Icc 0 T)
  let r := TorusFlight.along (cutoffPhysicalSource b F)
  let m : Phase → ℝ := fun p => maxwellian p.2
  let e : Phase → ℝ := fun p => Real.exp (-2*‖p.2‖^2)
  let R : Phase → ℝ := fun p => A*H q p.2
  have hri : Integrable r (μ.prod volume) :=
    cutoffCharacteristicSource_integrable hcarleman hq₁ hq₂ hA hb hFm hFn hFb
  have hbounds : ∀ᵐ p : Phase, ∀ᵐ t ∂μ, entropyPath a r t p ∈ Icc 0 (R p) := by
    have hs := (Measure.measurePreserving_swap (μ := (volume : Measure Phase)) (ν := μ)).quasiMeasurePreserving.ae hchar
    filter_upwards [Measure.ae_ae_of_ae_prod hs] with p hp
    filter_upwards [hp] with t ht
    change F t (TorusFlight.flight t p) = entropyPath a r t p at ht
    rw [← ht]
    exact ⟨hFn _ _,hFb _ _⟩
  have hET' := regularizedRelativeEntropyDensity_integrable hq₁ hq₂ hA hδ hδone
    (hFm.comp (measurable_const.prodMk measurable_id)) (hFn T) (hFb T)
  have hET : Integrable (fun p => scalarRelativeEntropy (m p) (entropyPath a r T p+δ*e p)) := by
    have h := (TorusFlight.flight_measurePreserving T).integrable_comp_of_integrable hET'
    apply h.congr
    filter_upwards [hcharT] with p hp
    change scalarRelativeEntropy (maxwellian p.2) (F T (TorusFlight.flight T p)+δ*e p) = _
    rw [hp]
  have hE0 : Integrable (fun p => scalarRelativeEntropy (m p) (a p+δ*e p)) :=
    regularizedRelativeEntropyDensity_integrable hq₁ hq₂ hA hδ hδone ham han hab
  have hbase : Integrable (fun p => scalarRelativeEntropy (m p) (δ*e p)) := by
    have h := regularizedRelativeEntropyDensity_integrable hq₁ hq₂ (le_refl (0:ℝ)) hδ hδone
      (f := fun _ => 0) measurable_const (fun _ => le_refl _) (fun p => by simp)
    convert h using 1
    funext p
    simp only [regularizedRelativeEntropyDensity,m,e,zero_add]
  let L : ℝ × Phase → ℝ := fun z =>
    Real.log ((F z.1 z.2+δ*Real.exp (-2*‖z.2.2‖^2))/maxwellian z.2.2)*cutoffPhysicalSource b F z
  have hL : Integrable L (μ.prod volume) :=
    physical_regularized_entropy_integrable hcarleman hq₁ hq₂ hA hδ hδone hb hFm hFn hFb
  have hLi : Integrable (fun z : ℝ × Phase =>
      Real.log ((entropyPath a r z.1 z.2+δ*e z.2)/m z.2)*r z) (μ.prod volume) := by
    have h := (TorusFlight.along_measurePreserving μ).integrable_comp_of_integrable hL
    apply h.congr
    filter_upwards [hchar] with z hz
    change Real.log ((F z.1 (TorusFlight.flight z.1 z.2)+δ*e z.2)/m z.2)*r z = _
    rw [hz]
  have hbal := scalar_entropy_integral_balance hT hδ a m e R r
    (fun p => maxwellian_pos p.2) (fun p => Real.exp_pos _) (fun p => mul_nonneg hA (H_nonneg q p.2))
    hri hbounds hET hE0 hbase integrable_maxwellian_phase hLi
  have hend : (∫ p, scalarRelativeEntropy (m p) (entropyPath a r T p+δ*e p)) =
      ∫ p, regularizedRelativeEntropyDensity δ (F T) p := by
    calc
      _ = ∫ p, regularizedRelativeEntropyDensity δ (F T) (TorusFlight.flight T p) := by
        apply integral_congr_ae
        filter_upwards [hcharT] with p hp
        change scalarRelativeEntropy (m p) (entropyPath a r T p+δ*e p) =
          scalarRelativeEntropy (m p) (F T (TorusFlight.flight T p)+δ*e p)
        rw [hp]
      _ = _ := TorusFlight.integral_flight _ T
  have hrhs : (∫ z : ℝ × Phase, Real.log ((entropyPath a r z.1 z.2+δ*e z.2)/m z.2)*r z ∂μ.prod volume) =
      ∫ z, L z ∂μ.prod volume := by
    calc
      _ = ∫ z, TorusFlight.along L z ∂μ.prod volume := by
        apply integral_congr_ae
        filter_upwards [hchar] with z hz
        change Real.log ((entropyPath a r z.1 z.2+δ*e z.2)/m z.2)*r z =
          Real.log ((F z.1 (TorusFlight.flight z.1 z.2)+δ*e z.2)/m z.2)*r z
        rw [hz]
      _ = _ := by
        have hAlong : Integrable (TorusFlight.along L) (μ.prod volume) :=
          (TorusFlight.along_measurePreserving μ).integrable_comp_of_integrable hL
        rw [integral_prod _ hAlong,integral_prod _ hL]
        apply integral_congr_ae
        filter_upwards [] with t
        exact TorusFlight.integral_flight (fun p => L (t,p)) t
  rw [hend,hrhs] at hbal
  exact hbal

end BoltzmannNonuniqueness

end

end

section

/-! # Uniform finite branching growth with bounded collision velocities -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem bounded_finite_history_block_transfer (N : ℕ) (T : ℝ) {κ d : ℝ}
    (hκ : 0 < κ) (hd : 0 < d) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Icc 0 ε₀, ∀ A ∈ Icc 0 T, ∀ z : FlightState,
      (7 : ℝ≥0∞) < (∑ n ∈ Finset.range N, eventHistory referenceClock branchingKernel
        (flightSeed referenceClock ((blockTarget z.1 A κ d).indicator 1)) n (A,z)) →
      ∀ (b : BeamCoefficients) (endTime : ℝ),
      (∀ n < N, ∀ a : ParameterWord n, GoodReferenceWord n (A,z) a →
        WordNearby b endTime ε n (embedFlightState (A,z)) a) →
      (6 : ℝ≥0∞) < boundedMediumBlockMass b endTime T (A,z) κ d N := by
  obtain ⟨r,hr,hrsmall⟩ := finiteHistoryError_small N T
  let L : ℝ := (N:ℝ)+1
  have hL : 0 < L := by dsimp [L]; positivity
  let ε₀ := min (1/4:ℝ) (min (1/L) (min ((d*κ/8)/L) r))
  have hε₀ : 0 < ε₀ := by
    dsimp [ε₀]
    simp only [lt_min_iff]
    exact ⟨by norm_num,one_div_pos.mpr hL,by positivity,hr⟩
  refine ⟨ε₀,hε₀,?_⟩
  intro ε hε A hA z href b endTime hnear
  have hcut : ε ≤ min (1/4:ℝ) (min (1/L) (min ((d*κ/8)/L) r)) := hε.2
  have hquarter := hcut.trans (min_le_left _ _)
  have htail := hcut.trans (min_le_right _ _)
  have hεL := htail.trans (min_le_left _ _)
  have htail' := htail.trans (min_le_right _ _)
  have hεd := htail'.trans (min_le_left _ _)
  have hεr := htail'.trans (min_le_right _ _)
  have hmass := hrsmall ε ⟨hε.1,hεr⟩
  have hsum : (∑ n ∈ Finset.range N, eventHistory referenceClock branchingKernel
      (flightSeed referenceClock ((blockTarget z.1 A κ d).indicator 1)) n (A,z)) ≤
      boundedMediumBlockMass b endTime T (A,z) κ d N+finiteHistoryError N T ε := by
    calc
      _ ≤ ∑ n ∈ Finset.range N,
          ((∫⁻ a, boundedMediumBlockIntegrand b endTime (A,z) κ d n a ∂parameterWordMeasure T n)+
            historyPerturbationError n ε*(3*ENNReal.ofReal T)^n) := by
        apply Finset.sum_le_sum
        intro n hn
        have hnN := (Finset.mem_range.mp hn).le
        have hnL : (n:ℝ) ≤ L :=
          (Nat.cast_le.mpr hnN).trans (le_add_of_nonneg_right (by norm_num))
        have hv : (n:ℝ)*ε ≤ 1 :=
          (mul_le_mul_of_nonneg_right hnL hε.1).trans
            (by simpa only [mul_comm] using (le_div_iff₀ hL).mp hεL)
        have hx' : (n:ℝ)*ε ≤ d*κ/8 :=
          (mul_le_mul_of_nonneg_right hnL hε.1).trans
            (by simpa only [mul_comm] using (le_div_iff₀ hL).mp hεd)
        have hx : 2*A*((n:ℝ)*ε) ≤ d*κ*A/4 := by
          convert mul_le_mul_of_nonneg_left hx' (show 0 ≤ (2:ℝ)*A from mul_nonneg (by norm_num) hA.1) using 1
          ring
        exact bounded_medium_word_integral_lower b endTime n (A,z) T hε.1 hquarter hA.1 hA.2
          hv hx (hnear n (Finset.mem_range.mp hn))
      _ = _ := by rw [Finset.sum_add_distrib]; rfl
  by_contra hbad
  have hupper := hsum.trans (add_le_add (le_of_not_gt hbad) hmass.le)
  norm_num at hupper
  exact (not_lt_of_ge hupper) href

theorem uniform_bounded_perturbed_block_growth {d κ : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hκ : 0 < κ) (hκ1 : κ < 1)
    (hg : (referenceClock : ℝ)*κ < referenceGrowth) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ T : ℝ, A₀ ≤ T → ∃ N : ℕ, ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε ∈ Icc 0 ε₀, ∀ A ∈ Icc A₀ T, ∀ z : FlightState,
      ∀ (b : BeamCoefficients) (endTime : ℝ),
      (∀ n < N, ∀ a : ParameterWord n, GoodReferenceWord n (A,z) a →
        WordNearby b endTime ε n (embedFlightState (A,z)) a) →
      (6 : ℝ≥0∞) < boundedMediumBlockMass b endTime T (A,z) κ d N := by
  obtain ⟨A₀,hA₀,hdepth⟩ := uniform_finite_branching_block_growth hd hd1 hκ hκ1 hg
  refine ⟨A₀,hA₀,?_⟩
  intro T hT
  obtain ⟨N,hN⟩ := hdepth T hT
  obtain ⟨ε₀,hε₀,htransfer⟩ := bounded_finite_history_block_transfer N T hκ hd
  refine ⟨N,ε₀,hε₀,?_⟩
  intro ε hε A hA z b endTime hnear
  exact htransfer ε hε A ⟨hA₀.le.trans hA.1,hA.2⟩ z (hN A hA z) b endTime hnear

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
