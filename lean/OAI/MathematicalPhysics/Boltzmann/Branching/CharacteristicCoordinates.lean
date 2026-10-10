import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveIntegralBound
import OAI.MathematicalPhysics.Boltzmann.Branching.EuclideanKineticMap

namespace OAI

section

/-! # Almost-everywhere velocity-fiber bounds along almost every free path -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

theorem measurableSet_ae_velocity_bound {X : Type*} [MeasurableSpace X]
    {f : X × Velocity → ℝ} {A : X → ℝ} (hf : Measurable f) (hA : Measurable A) :
    MeasurableSet {x | ∀ᵐ w : Velocity, f (x,w) ≤ A x} := by
  let B : Set (X × Velocity) := {z | A z.1 < f z}
  have hB : MeasurableSet B := measurableSet_lt (hA.comp measurable_fst) hf
  have hm : Measurable (fun x : X => (volume : Measure Velocity) (Prod.mk x ⁻¹' B)) :=
    measurable_measure_prodMk_left hB
  have he : {x | ∀ᵐ w : Velocity, f (x,w) ≤ A x} =
      {x | (volume : Measure Velocity) (Prod.mk x ⁻¹' B) = 0} := by
    ext x
    simp only [mem_ofPred_eq,ae_iff,not_le]
    rfl
  rw [he]
  exact measurableSet_eq_fun hm measurable_const

theorem ae_velocity_bound_along_paths {T : ℝ} {F : ℝ × JetPrototype.Phase → ℝ}
    {A : ℝ → ℝ} (hFm : Measurable F) (hAm : Measurable A)
    (hbound : ∀ t ∈ Icc 0 T, ∀ᵐ p ∂FlightMeasure.phaseVolume, F (t,p) ≤ A t) :
    ∀ᵐ p ∂FlightMeasure.phaseVolume, ∀ᵐ t ∂volume.restrict (Icc (0:ℝ) T),
      ∀ᵐ w : Velocity, F (t,((JetBarrier.flight t p).1,w)) ≤ A t := by
  have hm : Measurable (fun z : (ℝ × JetPrototype.Phase) × Velocity =>
      F (z.1.1,((JetBarrier.flight z.1.1 z.1.2).1,z.2))) := by
    apply hFm.comp
    exact measurable_fst.fst.prodMk
      ((GaussianLocal.measurable_flight.comp measurable_fst).fst.prodMk measurable_snd)
  have hP := measurableSet_ae_velocity_bound hm (hAm.comp measurable_fst)
  have hall : ∀ᵐ z ∂(volume.restrict (Icc (0:ℝ) T)).prod FlightMeasure.phaseVolume,
      ∀ᵐ w : Velocity, F (z.1,((JetBarrier.flight z.1 z.2).1,w)) ≤ A z.1 := by
    apply (Measure.ae_prod_iff_ae_ae hP).mpr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hs : ∀ᵐ x ∂JetPrototype.spaceVolume, ∀ᵐ w : Velocity, F (t,(x,w)) ≤ A t :=
      Measure.ae_ae_of_ae_prod (hbound t ht)
    have hl : ∀ᵐ p ∂FlightMeasure.phaseVolume, ∀ᵐ w : Velocity, F (t,(p.1,w)) ≤ A t :=
      Measure.quasiMeasurePreserving_fst.ae hs
    exact (FlightMeasure.flight_measurePreserving t).quasiMeasurePreserving.ae hl
  exact Measure.ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ := FlightMeasure.phaseVolume)
      (ν := volume.restrict (Icc 0 T))).quasiMeasurePreserving.ae hall)

end BoltzmannNonuniqueness

end

end

section

/-! # Integrating characteristic test identities in physical spacetime -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.EuclideanFlight

def characteristicEquiv : (ℝ × (Velocity × Velocity)) ≃ᵐ Published.KineticPhase where
  toFun z := TransportCutoff.characteristic z.2 z.1
  invFun z := (z.1.1,(z.1.2-z.1.1 • z.2,z.2))
  left_inv z := by
    dsimp only [TransportCutoff.characteristic]
    simp
  right_inv z := by
    dsimp only [TransportCutoff.characteristic]
    simp
  measurable_toFun := by
    change Measurable (fun z : ℝ × (Velocity × Velocity) => TransportCutoff.characteristic z.2 z.1)
    unfold TransportCutoff.characteristic
    fun_prop
  measurable_invFun := by
    change Measurable (fun z : Published.KineticPhase => (z.1.1,(z.1.2-z.1.1 • z.2,z.2)))
    fun_prop

theorem characteristic_measurePreserving (μ : Measure ℝ) [SFinite μ] :
    MeasurePreserving characteristicEquiv
      (μ.prod (volume : Measure (Velocity × Velocity)))
      ((μ.prod (volume : Measure Velocity)).prod volume) := by
  have hs : MeasurePreserving (fun z : ℝ × (Velocity × Velocity) => (z.1,flight z.1 z.2))
      (μ.prod (volume : Measure (Velocity × Velocity))) (μ.prod volume) :=
    (MeasurePreserving.id μ).skew_product (μc := (volume : Measure (Velocity × Velocity)))
      (μd := (volume : Measure (Velocity × Velocity)))
      (by unfold flight; fun_prop) (ae_of_all _ (fun t => (flight_measurePreserving t).map_eq))
  convert (measurePreserving_prodAssoc μ (volume : Measure Velocity)
    (volume : Measure Velocity)).symm.comp hs using 1
  funext z
  rfl

theorem integral_eq_zero_of_characteristics {T : ℝ} (hT : 0 ≤ T)
    {f : Published.KineticPhase → ℝ}
    (hi : Integrable f (((volume.restrict (Ioc 0 T)).prod (volume : Measure Velocity)).prod volume))
    (hpath : ∀ᵐ p ∂(volume : Measure (Velocity × Velocity)),
      (∫ t in 0..T, f (TransportCutoff.characteristic p t)) = 0) :
    (∫ z, f z ∂((volume.restrict (Ioc 0 T)).prod (volume : Measure Velocity)).prod volume) = 0 := by
  have hm := characteristic_measurePreserving (volume.restrict (Ioc 0 T))
  have hc := hm.integrable_comp_of_integrable hi
  calc
    _ = ∫ z : ℝ × (Velocity × Velocity), f (characteristicEquiv z)
        ∂(volume.restrict (Ioc 0 T)).prod volume := (hm.integral_comp' f).symm
    _ = ∫ p : Velocity × Velocity, (∫ t in Ioc 0 T, f (TransportCutoff.characteristic p t) ∂volume) ∂volume :=
      integral_prod_symm _ hc
    _ = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hpath] with p hp
      simpa only [Pi.zero_apply,intervalIntegral.integral_of_le hT] using hp

end BoltzmannNonuniqueness.EuclideanFlight

end

end

end OAI
