import OAI.MathematicalPhysics.Boltzmann.Collision.GaussianLocalExistence
import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionMeasure

namespace OAI

/-! # Free-flight measure preservation and representative invariance -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace BoltzmannNonuniqueness.FlightMeasure

abbrev phaseVolume : Measure JetPrototype.Phase := JetPrototype.spaceVolume.prod volume

theorem flight_measurePreserving (t : ℝ) :
    MeasurePreserving (JetBarrier.flight t) phaseVolume phaseVolume := by
  have hm : Measurable (Function.uncurry (fun (v : Velocity) (x : JetPrototype.Space) =>
      x + (t • VelocityWeight.transverse v,t * VelocityWeight.axial v))) := by
    unfold Function.uncurry VelocityWeight.transverse VelocityWeight.axial
    fun_prop
  have hskew := (MeasurePreserving.id (volume : Measure Velocity)).skew_product hm
    (ae_of_all _ (fun v => (measurePreserving_add_right JetPrototype.spaceVolume
      (t • VelocityWeight.transverse v,t * VelocityWeight.axial v)).map_eq))
  have hswap₁ : MeasurePreserving Prod.swap phaseVolume
      ((volume : Measure Velocity).prod JetPrototype.spaceVolume) := Measure.measurePreserving_swap
  have hswap₂ : MeasurePreserving Prod.swap
      ((volume : Measure Velocity).prod JetPrototype.spaceVolume) phaseVolume := Measure.measurePreserving_swap
  convert hswap₂.comp (hskew.comp hswap₁) using 1
  funext p
  rfl

theorem spacetime_measurePreserving (s : ℝ) :
    MeasurePreserving (fun z : ℝ × JetPrototype.Phase => (z.1,JetBarrier.flight (z.1-s) z.2))
      ((volume : Measure ℝ).prod phaseVolume) ((volume : Measure ℝ).prod phaseVolume) := by
  exact (MeasurePreserving.id (volume : Measure ℝ)).skew_product
    (μc := phaseVolume) (μd := phaseVolume)
    (g := fun r p => JetBarrier.flight (r-s) p)
    (GaussianLocal.measurable_flight.comp
      ((measurable_fst.sub measurable_const).prodMk measurable_snd))
    (ae_of_all _ (fun r => (flight_measurePreserving (r-s)).map_eq))

theorem value_congr_at_time {f₀ k₀ : JetPrototype.Phase → ℝ}
    {g h : ℝ × JetPrototype.Phase → ℝ}
    (hinit : f₀ =ᵐ[phaseVolume] k₀) (hsource : g =ᵐ[(volume : Measure ℝ).prod phaseVolume] h)
    (T L t : ℝ) :
    (fun p => PositiveIntegral.value T L JetBarrier.flight f₀ g (t,p)) =ᵐ[phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight k₀ h (t,p)) := by
  let τ := PositiveIntegral.time T t
  have hi := (flight_measurePreserving (-τ)).quasiMeasurePreserving.ae hinit
  have hs := (spacetime_measurePreserving τ).quasiMeasurePreserving.ae hsource
  have hsp := (Measure.measurePreserving_swap (μ := phaseVolume) (ν := volume)).quasiMeasurePreserving.ae hs
  have hr := ae_ae_of_ae_prod hsp
  filter_upwards [hi,hr] with p hip hrp
  unfold PositiveIntegral.value
  change Real.exp (-L*τ)*f₀ (JetBarrier.flight (-τ) p) + _ =
    Real.exp (-L*τ)*k₀ (JetBarrier.flight (-τ) p) + _
  rw [hip]
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hrp] with r hr _
  change g (r,JetBarrier.flight (r-PositiveIntegral.time T t) p) =
    h (r,JetBarrier.flight (r-PositiveIntegral.time T t) p) at hr
  rw [hr]

end BoltzmannNonuniqueness.FlightMeasure

end

end OAI
