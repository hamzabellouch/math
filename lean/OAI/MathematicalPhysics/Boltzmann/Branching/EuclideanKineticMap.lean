import OAI.MathematicalPhysics.Boltzmann.Branching.PublishedInputs
import OAI.MathematicalPhysics.Boltzmann.Branching.TransportCutoff
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedNetLoss
import OAI.MathematicalPhysics.Boltzmann.Compactness.PhysicalCharacteristic
import OAI.MathematicalPhysics.Boltzmann.Jets.JetPeriodicDatum

namespace OAI

section

/-! # Euclidean coordinates for the physical characteristic equation -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.EuclideanFlight

/-- Euclidean free transport, with the same velocity convention as GLPS. -/
def flight (t : ℝ) (p : Velocity × Velocity) : Velocity × Velocity :=
  (p.1+t • p.2,p.2)

def spaceEquiv : Velocity ≃ᵐ JetPrototype.Space :=
  split.trans MeasurableEquiv.prodComm

def phaseEquiv : (Velocity × Velocity) ≃ᵐ JetPrototype.Phase :=
  MeasurableEquiv.prodCongr spaceEquiv (MeasurableEquiv.refl Velocity)

theorem spaceEquiv_apply (x : Velocity) : spaceEquiv x = JetPeriodicDatum.spatialMap x := by
  change (split x).swap = _
  rw [split_apply]
  rfl

theorem phaseEquiv_apply (p : Velocity × Velocity) : phaseEquiv p = JetPeriodicDatum.phaseMap p := by
  change (spaceEquiv p.1,p.2) = _
  rw [spaceEquiv_apply]
  rfl

theorem phaseEquiv_measurePreserving :
    MeasurePreserving phaseEquiv (volume : Measure (Velocity × Velocity)) FlightMeasure.phaseVolume := by
  convert JetPeriodicDatum.phaseMap_measurePreserving using 1
  funext p
  exact phaseEquiv_apply p

theorem phaseEquiv_flight (t : ℝ) (p : Velocity × Velocity) :
    phaseEquiv (flight t p) = JetBarrier.flight t (phaseEquiv p) := by
  simp only [phaseEquiv_apply,JetPeriodicDatum.phaseMap,JetPeriodicDatum.spatialMap,
    flight,JetBarrier.flight]
  congr 2

/-- The physical density lifted to the Euclidean kinetic domain of GLPS. -/
def density (q : ℝ) (F : ℝ × JetPrototype.Phase → ℝ)
    (z : Published.KineticPhase) : ℝ :=
  PhysicalLocalization.density q F (z.1.1,phaseEquiv (z.1.2,z.2))

def source (b q : ℝ) (F : ℝ × JetPrototype.Phase → ℝ)
    (z : Published.KineticPhase) : ℝ :=
  PhysicalLocalization.source b q F (z.1.1,phaseEquiv (z.1.2,z.2))

theorem density_measurable {F : ℝ × JetPrototype.Phase → ℝ} (hF : Measurable F) (q : ℝ) :
    Measurable (density q F) := by
  have hphase : Measurable (fun z : Published.KineticPhase => phaseEquiv (z.1.2,z.2)) :=
    phaseEquiv.measurable.comp (measurable_fst.snd.prodMk measurable_snd)
  exact ((ChartKernel.measurable_H q).comp measurable_snd).mul
    (hF.comp (measurable_fst.fst.prodMk hphase))

theorem source_eq_collision (b q : ℝ) (F : ℝ × JetPrototype.Phase → ℝ) :
    source b q F = CollisionCompactness.collisionSource b (density q F) := by
  funext z
  rfl

end BoltzmannNonuniqueness.EuclideanFlight

end

end

section

/-! # Inverse free flight and Lebesgue preservation in Euclidean coordinates -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.EuclideanFlight

theorem flight_measurePreserving (t : ℝ) :
    MeasurePreserving (flight t) (volume : Measure (Velocity × Velocity)) volume := by
  have h := (MeasurePreserving.symm phaseEquiv phaseEquiv_measurePreserving).comp
    ((FlightMeasure.flight_measurePreserving t).comp phaseEquiv_measurePreserving)
  have he : (fun p => phaseEquiv.symm (JetBarrier.flight t (phaseEquiv p))) = flight t := by
    funext p
    apply phaseEquiv.injective
    simp only [phaseEquiv.apply_symm_apply,phaseEquiv_flight]
  exact he ▸ h

theorem characteristic_back (p : Velocity × Velocity) (t s : ℝ) :
    TransportCutoff.characteristic (flight (-t) p) s =
      ((s,p.1-(t-s) • p.2),p.2) := by
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · dsimp [TransportCutoff.characteristic,flight]
      module
  · rfl

@[simp] theorem characteristic_endpoint (p : Velocity × Velocity) (t : ℝ) :
    TransportCutoff.characteristic (flight (-t) p) t = ((t,p.1),p.2) := by
  rw [characteristic_back]
  simp only [sub_self,zero_smul,sub_zero]

end BoltzmannNonuniqueness.EuclideanFlight

end

end

section

/-! # Localized physical mild equation in the Euclidean GLPS coordinates -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.EuclideanFlight

@[simp] theorem phaseEquiv_snd (p : Velocity × Velocity) : (phaseEquiv p).2 = p.2 := rfl

theorem density_along (q : ℝ) (F : ℝ × JetPrototype.Phase → ℝ)
    (p : Velocity × Velocity) (t : ℝ) :
    density q F ((t,(flight t p).1),(flight t p).2) =
      PhysicalLocalization.density q F (t,JetBarrier.flight t (phaseEquiv p)) := by
  change PhysicalLocalization.density q F (t,phaseEquiv (flight t p)) = _
  rw [phaseEquiv_flight]

theorem source_along (b q : ℝ) (F : ℝ × JetPrototype.Phase → ℝ)
    (p : Velocity × Velocity) (t : ℝ) :
    source b q F ((t,(flight t p).1),(flight t p).2) =
      PhysicalLocalization.source b q F (t,JetBarrier.flight t (phaseEquiv p)) := by
  change PhysicalLocalization.source b q F (t,phaseEquiv (flight t p)) = _
  rw [phaseEquiv_flight]

theorem localized (hcarleman : Published.GPV2009CarlemanInput)
    {q b L T U R : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    (F : WeightedLocalControl.PeriodicMildState q b L U R f₀)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hb : 0 ≤ b) (hR : 0 ≤ R) (hT : 0 ≤ T) (hTU : T ≤ U)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L) (hf₀ : Measurable f₀)
    (χ χ' : (Velocity × Velocity) → ℝ → ℝ)
    (hχ : ∀ p, ContinuousOn (χ p) (Icc 0 T))
    (hχ' : ∀ p, ContinuousOn (χ' p) (Icc 0 T))
    (hdχ : ∀ p t, t ∈ Icc 0 T → HasDerivAt (χ p) (χ' p t) t) :
    ∀ᵐ p ∂(volume : Measure (Velocity × Velocity)),
      χ p T*density q F.value ((T,(flight T p).1),(flight T p).2) =
        Real.exp (-T)*χ p 0*(H q p.2*f₀ (phaseEquiv p)) +
        ∫ t in 0..T, Real.exp (-(T-t)) *
          (χ p t*source b q F.value ((t,(flight t p).1),(flight t p).2) +
            (χ' p t+χ p t)*density q F.value ((t,(flight t p).1),(flight t p).2)) := by
  have h := PhysicalLocalization.localized hcarleman F hq₁ hq₂ hb hR hT hTU hloss hf₀
    (fun p => χ (phaseEquiv.symm p)) (fun p => χ' (phaseEquiv.symm p))
    (fun p => hχ _) (fun p => hχ' _) (fun p => hdχ _)
  have hp := phaseEquiv_measurePreserving.quasiMeasurePreserving.ae h
  filter_upwards [hp] with p hpp
  simp only [phaseEquiv.symm_apply_apply,phaseEquiv_snd] at hpp
  simpa only [density_along,source_along] using hpp

/-- A smooth kinetic cutoff, with its derivative actually computed along the
transport field, gives the local source required by velocity averaging. -/
theorem smooth_localized (hcarleman : Published.GPV2009CarlemanInput)
    {q b L T U R : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    (F : WeightedLocalControl.PeriodicMildState q b L U R f₀)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hb : 0 ≤ b) (hR : 0 ≤ R) (hT : 0 ≤ T) (hTU : T ≤ U)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L) (hf₀ : Measurable f₀)
    {χ : Published.KineticPhase → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hzero : ∀ p : Velocity × Velocity, χ (TransportCutoff.characteristic p 0) = 0) :
    ∀ᵐ p ∂(volume : Measure (Velocity × Velocity)),
      χ (TransportCutoff.characteristic p T)*density q F.value (TransportCutoff.characteristic p T) =
        ∫ t in 0..T, Real.exp (-(T-t)) *
          (χ (TransportCutoff.characteristic p t)*source b q F.value (TransportCutoff.characteristic p t) +
            (TransportCutoff.transportDerivative χ (TransportCutoff.characteristic p t)+
              χ (TransportCutoff.characteristic p t))*density q F.value (TransportCutoff.characteristic p t)) := by
  have hd : Differentiable ℝ χ := hχ.differentiable (by simp)
  have H := localized hcarleman F hq₁ hq₂ hb hR hT hTU hloss hf₀
    (fun p t => χ (TransportCutoff.characteristic p t))
    (fun p t => TransportCutoff.transportDerivative χ (TransportCutoff.characteristic p t))
    (fun p => (hχ.continuous.comp (TransportCutoff.characteristic_continuous p)).continuousOn)
    (fun p => ((TransportCutoff.transportDerivative_continuous hχ).comp
      (TransportCutoff.characteristic_continuous p)).continuousOn)
    (fun p t _ => TransportCutoff.hasDerivAt_along hd p t)
  filter_upwards [H] with p hp
  rw [hzero p] at hp
  simpa only [mul_zero,zero_mul,zero_add,TransportCutoff.characteristic,flight] using hp

end BoltzmannNonuniqueness.EuclideanFlight

end

end

section

/-! # The physical integral equation in ordinary Euclidean coordinates -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.EuclideanFlight

theorem characteristic (hcarleman : Published.GPV2009CarlemanInput)
    {q b L T U R : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    (F : WeightedLocalControl.PeriodicMildState q b L U R f₀)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hb : 0 ≤ b) (hR : 0 ≤ R) (hT : 0 ≤ T) (hTU : T ≤ U)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L) (hf₀ : Measurable f₀) :
    ∀ᵐ p : Velocity × Velocity ∂volume,
      density q F.value ((T,p.1+T • p.2),p.2) = H q p.2*f₀ (phaseEquiv p) +
        ∫ t in 0..T, source b q F.value ((t,p.1+t • p.2),p.2) := by
  have h := phaseEquiv_measurePreserving.quasiMeasurePreserving.ae
    (PhysicalLocalization.characteristic hcarleman F hq₁ hq₂ hb hR hT hTU hloss hf₀)
  filter_upwards [h] with p hp
  have he (t : ℝ) : phaseEquiv (p.1+t • p.2,p.2) = JetBarrier.flight t (phaseEquiv p) :=
    phaseEquiv_flight t p
  have hv : (phaseEquiv p).2 = p.2 := rfl
  simpa only [density,source,he,hv] using hp

end BoltzmannNonuniqueness.EuclideanFlight

end

end

section

/-! # The measure-preserving map from Euclidean to jet kinetic coordinates -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.EuclideanFlight

def kineticMap (z : Published.KineticPhase) : ℝ × JetPrototype.Phase :=
  (z.1.1,phaseEquiv (z.1.2,z.2))

theorem kineticMap_measurePreserving : MeasurePreserving kineticMap volume
    WeightedLocal.spacetimeVolume := by
  have h := (MeasurePreserving.id (volume : Measure ℝ)).prod phaseEquiv_measurePreserving
  have hp := measurePreserving_prodAssoc (volume : Measure ℝ) (volume : Measure Velocity)
    (volume : Measure Velocity)
  have hc := h.comp hp
  change MeasurePreserving kineticMap
    (((volume : Measure ℝ).prod (volume : Measure Velocity)).prod volume)
    WeightedLocal.spacetimeVolume at hc
  simpa only [Measure.volume_eq_prod] using hc

end BoltzmannNonuniqueness.EuclideanFlight

end

end

end OAI
