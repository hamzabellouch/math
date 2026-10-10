import OAI.MathematicalPhysics.Boltzmann.Branching.PerturbedFiniteBlock
import OAI.MathematicalPhysics.Boltzmann.Branching.ReferenceHistoryMoments
import OAI.MathematicalPhysics.Boltzmann.Jets.GeometricPositiveCompact

namespace OAI

section

/-! # The positive marked collision kernel of a measurable two-beam medium -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

abbrev MediumState := (ℝ × V) × V

def markedChildKernel (b : BeamCoefficients) (m : HistoryMark) : Kernel MediumState V :=
  if m = 0 then Kernel.deterministic Prod.snd measurable_snd
  else outgoing.comap (fun z => (z.2,if m = 1 then b.plusPartner z.1 else b.minusPartner z.1))
    (measurable_snd.prodMk (by
      split
      · exact b.plusPartner_measurable.comp measurable_fst
      · exact b.minusPartner_measurable.comp measurable_fst))

instance markedChildKernel_isMarkov (b : BeamCoefficients) (m : HistoryMark) :
    IsMarkovKernel (markedChildKernel b m) := by
  unfold markedChildKernel
  split <;> infer_instance

def mediumMarkedRate (b : BeamCoefficients) (m : HistoryMark) (z : MediumState) : ℝ≥0∞ :=
  ENNReal.ofReal (markedRate m z.2 (b.plusPartner z.1) (b.minusPartner z.1)
    (b.plusDensity z.1) (b.minusDensity z.1))

theorem mediumMarkedRate_measurable (b : BeamCoefficients) (m : HistoryMark) :
    Measurable (mediumMarkedRate b m) := by
  have hp := b.plusPartner_measurable.comp (measurable_fst : Measurable (Prod.fst : MediumState → ℝ × V))
  have hm := b.minusPartner_measurable.comp (measurable_fst : Measurable (Prod.fst : MediumState → ℝ × V))
  have hbp := b.plusDensity_measurable.comp (measurable_fst : Measurable (Prod.fst : MediumState → ℝ × V))
  have hbm := b.minusDensity_measurable.comp (measurable_fst : Measurable (Prod.fst : MediumState → ℝ × V))
  unfold mediumMarkedRate
  apply Measurable.ennreal_ofReal
  unfold markedRate
  split
  · exact measurable_const.sub (measurable_const.mul
      ((hbp.mul (measurable_snd.sub hp).norm).add (hbm.mul (measurable_snd.sub hm).norm)))
  · split
    · exact (measurable_const.mul hbp).mul (measurable_snd.sub hp).norm
    · exact (measurable_const.mul hbm).mul (measurable_snd.sub hm).norm

def mediumMarkedKernel (b : BeamCoefficients) (m : HistoryMark) : Kernel MediumState V :=
  Kernel.withDensity (markedChildKernel b m) (fun z _ => mediumMarkedRate b m z)

instance mediumMarkedKernel_isSFinite (b : BeamCoefficients) (m : HistoryMark) :
    IsSFiniteKernel (mediumMarkedKernel b m) := by
  apply Kernel.IsSFiniteKernel.withDensity
  intro z v
  exact ENNReal.ofReal_ne_top

theorem mediumMarkedKernel_apply (b : BeamCoefficients) (m : HistoryMark) (z : MediumState) :
    mediumMarkedKernel b m z = mediumMarkedRate b m z • markedChildKernel b m z := by
  rw [mediumMarkedKernel,Kernel.withDensity_apply]
  · exact withDensity_const _
  · exact (mediumMarkedRate_measurable b m).comp measurable_fst

def mediumCollisionKernel (b : BeamCoefficients) : Kernel MediumState V :=
  mediumMarkedKernel b 0+mediumMarkedKernel b 1+mediumMarkedKernel b 2

instance mediumCollisionKernel_isSFinite (b : BeamCoefficients) :
    IsSFiniteKernel (mediumCollisionKernel b) := by
  unfold mediumCollisionKernel
  infer_instance

theorem mediumMarkedKernel_lintegral (b : BeamCoefficients) (m : HistoryMark)
    (z : MediumState) {F : V → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ v, F v ∂mediumMarkedKernel b m z) = mediumMarkedRate b m z *
      ∫⁻ n : Sphere, F (markedChild m z.2 (b.plusPartner z.1) (b.minusPartner z.1) n.1)
        ∂sphereProbability := by
  rw [mediumMarkedKernel_apply,lintegral_smul_measure,smul_eq_mul]
  by_cases h0 : m = 0
  · simp [markedChildKernel,h0,markedChild,Kernel.deterministic_apply,lintegral_dirac]
  · rw [markedChildKernel,ite_eq_right h0,Kernel.comap_apply,outgoing_apply,
      lintegral_map hF (by unfold child; fun_prop)]
    congr 1
    apply lintegral_congr
    intro n
    simp [markedChild,h0]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The damped one-event kernel for finite marked histories in a measurable medium -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem mediumParameterDensity_ne_top (b : BeamCoefficients) (endTime : ℝ)
    (p : PhysicalFlightState) (a : MarkedEventParameter) :
    mediumParameterDensity b endTime p a ≠ ⊤ := by
  unfold mediumParameterDensity
  by_cases ht : a.2.1 ∈ Ioc 0 p.1
  · rw [indicator_of_mem ht,Pi.one_apply,one_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  · simp [ht]

def mediumEventDensity (b : BeamCoefficients) (endTime : ℝ)
    (_ : PhysicalFlightState) (p : PhysicalFlightState × MarkedEventParameter) : ℝ≥0∞ :=
  mediumParameterDensity b endTime p.1 p.2

theorem mediumEventDensity_measurable (b : BeamCoefficients) (endTime : ℝ) :
    Measurable (Function.uncurry (mediumEventDensity b endTime)) :=
  (mediumParameterDensity_measurable b endTime).comp measurable_snd

def mediumEventKernel (b : BeamCoefficients) (endTime T : ℝ) :
    Kernel PhysicalFlightState PhysicalFlightState :=
  (Kernel.withDensity (Kernel.id ×ₖ Kernel.const PhysicalFlightState (markedEventMeasure T))
    (mediumEventDensity b endTime)).map (fun p => mediumParameterState b endTime p.1 p.2)

instance mediumEventKernel_isSFinite (b : BeamCoefficients) (endTime T : ℝ) :
    IsSFiniteKernel (mediumEventKernel b endTime T) := by
  have hd : IsSFiniteKernel (Kernel.withDensity
      (Kernel.id ×ₖ Kernel.const PhysicalFlightState (markedEventMeasure T))
      (mediumEventDensity b endTime)) := by
    apply Kernel.IsSFiniteKernel.withDensity
    intro p a
    exact mediumParameterDensity_ne_top b endTime a.1 a.2
  unfold mediumEventKernel
  infer_instance

theorem mediumEventKernel_lintegral (b : BeamCoefficients) (endTime T : ℝ)
    (p : PhysicalFlightState) {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂mediumEventKernel b endTime T p) =
      ∫⁻ a, mediumParameterDensity b endTime p a * F (mediumParameterState b endTime p a)
        ∂markedEventMeasure T := by
  have hcomp : Measurable (fun q : PhysicalFlightState × MarkedEventParameter =>
      F (mediumParameterState b endTime q.1 q.2)) := by
    simpa only [Function.comp_def] using hF.comp (mediumParameterState_measurable b endTime)
  have hm : Measurable (fun q : PhysicalFlightState × MarkedEventParameter =>
      mediumParameterDensity b endTime q.1 q.2 * F (mediumParameterState b endTime q.1 q.2)) :=
    (mediumParameterDensity_measurable b endTime).mul hcomp
  rw [mediumEventKernel,Kernel.lintegral_map _ (mediumParameterState_measurable b endTime) p hF,
    Kernel.lintegral_withDensity _ (mediumEventDensity_measurable b endTime) p hcomp]
  simpa only [mediumEventDensity,Function.comp_def,Kernel.const_apply] using!
    Kernel.lintegral_id_prod hm (Kernel.const PhysicalFlightState (markedEventMeasure T)) p

instance mediumEventKernel_pow_isSFinite (b : BeamCoefficients) (endTime T : ℝ) (n : ℕ) :
    IsSFiniteKernel ((mediumEventKernel b endTime T)^n) := by
  induction n with
  | zero => change IsSFiniteKernel Kernel.id; infer_instance
  | succ n ih =>
    rw [show (mediumEventKernel b endTime T)^(n+1) =
        ((mediumEventKernel b endTime T)^n) ∘ₖ mediumEventKernel b endTime T by
      simpa only [pow_one] using Kernel.pow_add (mediumEventKernel b endTime T) n 1]
    let _ := ih
    infer_instance

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Physical projection and local bounds of the positive two-beam kernel -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem mediumCollisionKernel_lintegral (b : BeamCoefficients) (z : MediumState)
    {F : V → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ v, F v ∂mediumCollisionKernel b z) =
      ∑ m : HistoryMark, mediumMarkedRate b m z *
        ∫⁻ n : Sphere, F (markedChild m z.2 (b.plusPartner z.1) (b.minusPartner z.1) n.1)
          ∂sphereProbability := by
  simp only [mediumCollisionKernel,add_apply,lintegral_add_measure,
    mediumMarkedKernel_lintegral b _ z hF,Fin.sum_univ_three]

theorem mediumCollisionKernel_mass (b : BeamCoefficients) (z : MediumState) :
    mediumCollisionKernel b z univ = ∑ m : HistoryMark, mediumMarkedRate b m z := by
  have H := mediumCollisionKernel_lintegral b z (F := fun _ => 1) measurable_const
  simpa only [lintegral_const,measure_univ,one_mul,mul_one] using H

theorem mediumCollisionKernel_projection (b : BeamCoefficients) (z : MediumState) :
    mediumCollisionKernel b z =
      ENNReal.ofReal (4*Real.pi*b.plusDensity z.1*‖z.2-b.plusPartner z.1‖) •
        outgoing (z.2,b.plusPartner z.1)+
      ENNReal.ofReal (4*Real.pi*b.minusDensity z.1*‖z.2-b.minusPartner z.1‖) •
        outgoing (z.2,b.minusPartner z.1)+
      ENNReal.ofReal (48*Real.pi-mediumFrequency z.2 (b.plusPartner z.1) (b.minusPartner z.1)
        (b.plusDensity z.1) (b.minusDensity z.1)) • Measure.dirac z.2 := by
  simp only [mediumCollisionKernel,add_apply,mediumMarkedKernel_apply,
    mediumMarkedRate,markedChildKernel,markedRate,Fin.isValue,one_ne_zero,
    show (2 : HistoryMark) ≠ 0 by decide,show (2 : HistoryMark) ≠ 1 by decide,
    ↓reduceIte,Kernel.deterministic_apply,Kernel.comap_apply]
  ac_rfl

theorem mediumCollisionKernel_mass_exact (b : BeamCoefficients) (z : MediumState)
    (hp : 0 ≤ b.plusDensity z.1) (hm : 0 ≤ b.minusDensity z.1)
    (hf : mediumFrequency z.2 (b.plusPartner z.1) (b.minusPartner z.1)
      (b.plusDensity z.1) (b.minusDensity z.1) ≤ 48*Real.pi) :
    mediumCollisionKernel b z univ = ENNReal.ofReal (48*Real.pi+
      mediumFrequency z.2 (b.plusPartner z.1) (b.minusPartner z.1)
        (b.plusDensity z.1) (b.minusDensity z.1)) := by
  rw [mediumCollisionKernel_mass,Fin.sum_univ_three]
  simp only [mediumMarkedRate,markedRate,Fin.isValue,one_ne_zero,
    show (2 : HistoryMark) ≠ 0 by decide,show (2 : HistoryMark) ≠ 1 by decide,↓reduceIte]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr hf) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  unfold mediumFrequency
  ring

theorem mediumCollisionKernel_mass_bound (b : BeamCoefficients) (z : MediumState)
    (hv : ‖z.2‖ ≤ 6) (hwp : ‖b.plusPartner z.1‖ ≤ 2) (hwm : ‖b.minusPartner z.1‖ ≤ 2)
    (hp : 0 ≤ b.plusDensity z.1) (hm : 0 ≤ b.minusDensity z.1)
    (hp1 : b.plusDensity z.1 ≤ 5/4) (hm1 : b.minusDensity z.1 ≤ 5/4) :
    mediumCollisionKernel b z univ ≤ ENNReal.ofReal (88*Real.pi) := by
  have hf := medium_frequency_bounds hv hwp hwm hp hm hp1 hm1
  rw [mediumCollisionKernel_mass_exact b z hp hm (by linarith [Real.pi_pos])]
  apply ENNReal.ofReal_le_ofReal
  linarith

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Physical collision-time formula for the marked medium event kernel -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem medium_parameter_integral (b : BeamCoefficients) (endTime : ℝ)
    (p : PhysicalFlightState) (m : HistoryMark) {T : ℝ} (hT : p.1 ≤ T)
    {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ a, mediumParameterDensity b endTime p (m,a) *
      F (mediumParameterState b endTime p (m,a)) ∂eventParameterMeasure T) =
    ∫⁻ s in Ioc 0 p.1, clockSurvival referenceClock s *
      (mediumMarkedRate b m (mediumPoint endTime p s,p.2.2) *
        ∫⁻ n : Sphere, F (mediumParameterState b endTime p (m,(s,n)))
          ∂sphereProbability) := by
  have hpair : Measurable (fun a : EventParameter => (p,(m,a))) := by fun_prop
  have hm : Measurable (fun a : EventParameter =>
      mediumParameterDensity b endTime p (m,a) *
        F (mediumParameterState b endTime p (m,a))) :=
    ((mediumParameterDensity_measurable b endTime).comp hpair).mul
      (hF.comp ((mediumParameterState_measurable b endTime).comp hpair))
  rw [eventParameterMeasure,lintegral_prod _ hm.aemeasurable]
  have he (s : ℝ) : (∫⁻ n : Sphere, mediumParameterDensity b endTime p (m,(s,n)) *
      F (mediumParameterState b endTime p (m,(s,n))) ∂sphereProbability) =
      (Ioc 0 p.1).indicator (fun s => clockSurvival referenceClock s *
        (mediumMarkedRate b m (mediumPoint endTime p s,p.2.2) *
          ∫⁻ n : Sphere, F (mediumParameterState b endTime p (m,(s,n)))
            ∂sphereProbability)) s := by
    by_cases hs : s ∈ Ioc 0 p.1
    · simp only [mediumParameterDensity,indicator_of_mem hs,Pi.one_apply,one_mul,
        mediumMarkedRate,mul_assoc]
      unfold clockSurvival
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    · simp [mediumParameterDensity,hs]
  simp_rw [he]
  rw [lintegral_indicator measurableSet_Ioc,Measure.restrict_restrict_of_subset]
  exact Ioc_subset_Ioc_right hT

theorem mediumEventKernel_physical_lintegral (b : BeamCoefficients) (endTime : ℝ)
    (p : PhysicalFlightState) {T : ℝ} (hT : p.1 ≤ T)
    {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂mediumEventKernel b endTime T p) =
    ∫⁻ s in Ioc 0 p.1, clockSurvival referenceClock s *
      ∫⁻ v, F (p.1-s,((mediumPoint endTime p s).2,v))
        ∂mediumCollisionKernel b (mediumPoint endTime p s,p.2.2) := by
  rw [mediumEventKernel_lintegral b endTime T p hF]
  have hpair : Measurable (fun a : MarkedEventParameter => (p,a)) := by fun_prop
  have hm : Measurable (fun a : MarkedEventParameter =>
      mediumParameterDensity b endTime p a * F (mediumParameterState b endTime p a)) :=
    ((mediumParameterDensity_measurable b endTime).comp hpair).mul
      (hF.comp ((mediumParameterState_measurable b endTime).comp hpair))
  rw [markedEventMeasure,lintegral_prod _ hm.aemeasurable,lintegral_fintype]
  simp only [Measure.count_singleton,mul_one]
  simp_rw [medium_parameter_integral b endTime p _ hT hF]
  rw [← lintegral_finsetSum]
  · apply lintegral_congr
    intro s
    rw [← Finset.mul_sum,mediumCollisionKernel_lintegral b _
      (F := fun v => F (p.1-s,((mediumPoint endTime p s).2,v)))
      (hF.comp (by fun_prop))]
    rfl
  · intro m _
    have hrate : Measurable (fun s : ℝ =>
        mediumMarkedRate b m (mediumPoint endTime p s,p.2.2)) :=
      (mediumMarkedRate_measurable b m).comp (by unfold mediumPoint; fun_prop)
    have hi : Measurable (fun a : EventParameter =>
        F (mediumParameterState b endTime p (m,a))) :=
      hF.comp ((mediumParameterState_measurable b endTime).comp
        (show Measurable (fun a : EventParameter => (p,(m,a))) by fun_prop))
    exact (show Measurable (clockSurvival referenceClock) by
      unfold clockSurvival; fun_prop).mul (hrate.mul hi.lintegral_prod_right')

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Finite medium histories equal powers of the actual marked event kernel -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem mediumWord_integral (b : BeamCoefficients) (endTime T : ℝ)
    {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) (n : ℕ) (p : PhysicalFlightState) :
    (∫⁻ a, mediumWordDensity b endTime n p a * F (mediumWordState b endTime n p a)
      ∂parameterWordMeasure T n) = ∫⁻ q, F q ∂((mediumEventKernel b endTime T)^n) p := by
  induction n generalizing p with
  | zero =>
    have hi : (1 : Kernel PhysicalFlightState PhysicalFlightState) = Kernel.id := rfl
    rw [pow_zero,hi,Kernel.id_apply,lintegral_dirac]
    change (∫⁻ _a : PUnit, 1*F p ∂Measure.dirac PUnit.unit) = F p
    rw [lintegral_const,Measure.dirac_apply_of_mem (mem_univ _),mul_one,one_mul]
  | succ n ih =>
    have hmap : Measurable (fun a : ParameterWord (n+1) => (p,a)) :=
      measurable_const.prodMk measurable_id
    have hd : Measurable (fun a : ParameterWord (n+1) => mediumWordDensity b endTime (n+1) p a) := by
      simpa only [Function.comp_def] using (mediumWordDensity_measurable b endTime (n+1)).comp hmap
    have hs : Measurable (fun a : ParameterWord (n+1) => mediumWordState b endTime (n+1) p a) := by
      simpa only [Function.comp_def] using (mediumWordState_measurable b endTime (n+1)).comp hmap
    have hm : Measurable (fun a : ParameterWord (n+1) =>
        mediumWordDensity b endTime (n+1) p a * F (mediumWordState b endTime (n+1) p a)) :=
      hd.mul (hF.comp hs)
    rw [parameterWordMeasure,lintegral_prod _ hm.aemeasurable]
    rw [show (mediumEventKernel b endTime T)^(n+1) =
        ((mediumEventKernel b endTime T)^n) ∘ₖ mediumEventKernel b endTime T by
      simpa only [pow_one] using Kernel.pow_add (mediumEventKernel b endTime T) n 1,
      Kernel.lintegral_comp _ _ _ hF,
      mediumEventKernel_lintegral b endTime T p (hF.lintegral_kernel (κ := (mediumEventKernel b endTime T)^n))]
    apply lintegral_congr
    intro a
    change (∫⁻ w, (mediumParameterDensity b endTime p a *
      mediumWordDensity b endTime n (mediumParameterState b endTime p a) w) *
      F (mediumWordState b endTime n (mediumParameterState b endTime p a) w)
        ∂parameterWordMeasure T n) = _
    simp_rw [mul_assoc]
    rw [lintegral_const_mul' _ _ (mediumParameterDensity_ne_top b endTime p a),ih]

def mediumFlightSeed (f : V × V → ℝ≥0∞) (p : PhysicalFlightState) : ℝ≥0∞ :=
  clockSurvival referenceClock p.1*f (finishMediumFlight p)

theorem finishMediumFlight_measurable : Measurable finishMediumFlight := by
  unfold finishMediumFlight
  fun_prop

theorem mediumFlightSeed_measurable {f : V × V → ℝ≥0∞} (hf : Measurable f) :
    Measurable (mediumFlightSeed f) := by
  exact (show Measurable (fun p : PhysicalFlightState => clockSurvival referenceClock p.1) by
    unfold clockSurvival; fun_prop).mul (hf.comp finishMediumFlight_measurable)

theorem physicalBlockTarget_measurable (x : V) (A κ d : ℝ) :
    MeasurableSet (physicalBlockTarget x A κ d) := by
  unfold physicalBlockTarget
  measurability

theorem mediumBlockMass_kernel (b : BeamCoefficients) (endTime T : ℝ)
    (p : TimeFlightState) (κ d : ℝ) (N : ℕ) :
    mediumBlockMass b endTime T p κ d N =
      ∑ n ∈ Finset.range N, ∫⁻ q,
        mediumFlightSeed ((physicalBlockTarget p.2.1 p.1 κ d).indicator 1) q
          ∂((mediumEventKernel b endTime T)^n) (embedFlightState p) := by
  unfold mediumBlockMass
  apply Finset.sum_congr rfl
  intro n _hn
  exact mediumWord_integral b endTime T
    (mediumFlightSeed_measurable (measurable_const.indicator (physicalBlockTarget_measurable _ _ _ _)))
      n (embedFlightState p)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Endpoint measures generated by the finite physical collision histories -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def mediumEndpointKernel (b : BeamCoefficients) (endTime T : ℝ) (n : ℕ) :
    Kernel PhysicalFlightState (V × V) :=
  (Kernel.withDensity ((mediumEventKernel b endTime T)^n)
    (fun _ p => clockSurvival referenceClock p.1)).map finishMediumFlight

instance mediumEndpointKernel_isSFinite (b : BeamCoefficients) (endTime T : ℝ) (n : ℕ) :
    IsSFiniteKernel (mediumEndpointKernel b endTime T n) := by
  have hs : IsSFiniteKernel (Kernel.withDensity ((mediumEventKernel b endTime T)^n)
      (fun _ p => clockSurvival referenceClock p.1)) := by
    apply Kernel.IsSFiniteKernel.withDensity
    intro p q
    exact ENNReal.ofReal_ne_top
  unfold mediumEndpointKernel
  infer_instance

theorem mediumEndpointKernel_lintegral (b : BeamCoefficients) (endTime T : ℝ) (n : ℕ)
    (p : PhysicalFlightState) {F : V × V → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ y, F y ∂mediumEndpointKernel b endTime T n p) =
      ∫⁻ q, mediumFlightSeed F q ∂((mediumEventKernel b endTime T)^n) p := by
  have hc : Measurable (Function.uncurry (fun (_ : PhysicalFlightState) (q : PhysicalFlightState) =>
      clockSurvival referenceClock q.1)) := by unfold clockSurvival; fun_prop
  have hf : Measurable (fun q : PhysicalFlightState => F (finishMediumFlight q)) := by
    simpa only [Function.comp_def] using hF.comp finishMediumFlight_measurable
  rw [mediumEndpointKernel,Kernel.lintegral_map _ finishMediumFlight_measurable p hF,
    Kernel.lintegral_withDensity _ hc p hf]
  rfl

theorem mediumEndpointKernel_apply (b : BeamCoefficients) (endTime T : ℝ) (n : ℕ)
    (p : PhysicalFlightState) {A : Set (V × V)} (hA : MeasurableSet A) :
    mediumEndpointKernel b endTime T n p A =
      ∫⁻ q, mediumFlightSeed (A.indicator 1) q ∂((mediumEventKernel b endTime T)^n) p := by
  have H := mediumEndpointKernel_lintegral b endTime T n p
    (measurable_const.indicator hA : Measurable (A.indicator (1 : V × V → ℝ≥0∞)))
  change (∫⁻ y, A.indicator (1 : V × V → ℝ≥0∞) y ∂mediumEndpointKernel b endTime T n p) = _ at H
  rw [lintegral_indicator_one hA] at H
  exact H

theorem mediumBlockMass_endpoints (b : BeamCoefficients) (endTime T : ℝ)
    (p : TimeFlightState) (κ d : ℝ) (N : ℕ) :
    mediumBlockMass b endTime T p κ d N =
      ∑ n ∈ Finset.range N, mediumEndpointKernel b endTime T n (embedFlightState p)
        (physicalBlockTarget p.2.1 p.1 κ d) := by
  rw [mediumBlockMass_kernel]
  apply Finset.sum_congr rfl
  intro n _hn
  exact (mediumEndpointKernel_apply b endTime T n (embedFlightState p)
    (physicalBlockTarget_measurable _ _ _ _)).symm

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The physical collision kernel retaining time and position -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def mediumStateCollision (b : BeamCoefficients) (endTime : ℝ) :
    Kernel PhysicalFlightState PhysicalFlightState :=
  (Kernel.id ×ₖ (mediumCollisionKernel b).comap
    (fun p => ((endTime-p.1,p.2.1),p.2.2)) (by fun_prop)).map
      (fun q => (q.1.1,(q.1.2.1,q.2)))

instance mediumStateCollision_sFinite (b : BeamCoefficients) (endTime : ℝ) :
    IsSFiniteKernel (mediumStateCollision b endTime) := by
  unfold mediumStateCollision
  infer_instance

theorem mediumStateCollision_lintegral (b : BeamCoefficients) (endTime : ℝ)
    (p : PhysicalFlightState) {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂mediumStateCollision b endTime p) =
      ∫⁻ v, F (p.1,(p.2.1,v))
        ∂mediumCollisionKernel b ((endTime-p.1,p.2.1),p.2.2) := by
  have hm : Measurable (fun q : PhysicalFlightState × V => (q.1.1,(q.1.2.1,q.2))) := by
    fun_prop
  rw [mediumStateCollision,Kernel.lintegral_map _ hm p hF]
  have hc : Measurable (fun q : PhysicalFlightState × V => F (q.1.1,(q.1.2.1,q.2))) :=
    hF.comp hm
  exact Kernel.lintegral_id_prod hc _ p

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
