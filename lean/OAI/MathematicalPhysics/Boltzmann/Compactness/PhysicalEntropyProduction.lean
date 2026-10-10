import OAI.MathematicalPhysics.Boltzmann.Approximation.RegularizedEntropyIntegrability
import OAI.MathematicalPhysics.Boltzmann.Compactness.KineticDensityMeasurable

namespace OAI

/-! # The regularized entropy estimate in physical time-phase coordinates -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

def cutoffPhysicalSource (b : ℝ) (F : Evolution) (z : ℝ × Phase) : ℝ :=
  CutoffLipschitz.collision b (fun v => F z.1 (z.2.1,v)) z.2.2

theorem physical_regularized_entropy_integrable (hcarleman : Published.GPV2009CarlemanInput)
    {T q A δ b : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hA : 0 ≤ A)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hb : 0 ≤ b)
    {F : Evolution} (hFm : Measurable (fun z : ℝ × Phase => F z.1 z.2))
    (hFn : ∀ t p, 0 ≤ F t p) (hFb : ∀ t p, F t p ≤ A*H q p.2) :
    Integrable (fun z : ℝ × Phase =>
      Real.log ((F z.1 z.2+δ*Real.exp (-2*‖z.2.2‖^2))/maxwellian z.2.2)*cutoffPhysicalSource b F z)
      ((volume.restrict (Icc 0 T)).prod volume) := by
  let g := kineticDensity F
  have hgm : Measurable g := hFm.comp MeasurableEquiv.prodAssoc.measurable
  have hgn : ∀ z, 0 ≤ g z := fun z => hFn _ _
  have hgb : ∀ z, g z ≤ A*H q z.2 := fun z => hFb _ _
  have hum := gaussianRegularizedDensity_measurable δ hgm
  have hul : ∀ z, δ*Real.exp (-2*‖z.2‖^2) ≤ gaussianRegularizedDensity δ g z := by
    intro z
    dsimp [gaussianRegularizedDensity]
    linarith [hgn z]
  have hub : ∀ z, gaussianRegularizedDensity δ g z ≤ (A+tiltConstant)*H q z.2 := fun z =>
    gaussianRegularization_bound hδ.le hδone (fun v => hgb (z.1,v)) z.2
  have hi := CollisionCompactness.bounded_log_source_integrable
    (μ := AnnularEnvelope.timePositionVolume T) hcarleman hq₁ hq₂ hA
    (add_nonneg hA tiltConstant_pos.le) hδ hb hgm hum hgn hgb hul hub
  exact (kineticGrouping_measurePreserving (volume.restrict (Icc 0 T))).symm.integrable_comp_of_integrable hi

theorem physical_regularized_entropy_production_bound (hcarleman : Published.GPV2009CarlemanInput)
    {T q A δ b p : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hA : 0 ≤ A)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hb : 0 ≤ b)
    (hp : 1 < p) (hpi : Integrable (fun v : Velocity => H q v^p))
    {F : Evolution} (hFm : Measurable (fun z : ℝ × Phase => F z.1 z.2))
    (hFn : ∀ t z, 0 ≤ F t z) (hFb : ∀ t z, F t z ≤ A*H q z.2) :
    (∫ z : ℝ × Phase,
      Real.log ((F z.1 z.2+δ*Real.exp (-2*‖z.2.2‖^2))/maxwellian z.2.2)*cutoffPhysicalSource b F z
      ∂(volume.restrict (Icc 0 T)).prod volume) ≤
      (δ*entropyErrorCoefficient q A b)*∫ z : (ℝ × Position) × Velocity,
        logarithmicMajorant q (A+tiltConstant) p δ z.2
        ∂(AnnularEnvelope.timePositionVolume T).prod volume := by
  have hbnd := CollisionCompactness.regularized_entropy_production_bound
    (μ := AnnularEnvelope.timePositionVolume T) hcarleman hq₁ hq₂ hA hδ hδone hb hp hpi
    (hFm.comp MeasurableEquiv.prodAssoc.measurable) (fun z => hFn _ _) (fun z => hFb _ _)
  have he := (kineticGrouping_measurePreserving (volume.restrict (Icc 0 T))).symm.integral_comp
    MeasurableEquiv.prodAssoc.symm.measurableEmbedding
    (fun z : (ℝ × Position) × Velocity =>
      Real.log (gaussianRegularizedDensity δ (kineticDensity F) z/maxwellian z.2)*
        CollisionCompactness.collisionSource b (kineticDensity F) z)
  exact he.trans_le hbnd

end BoltzmannNonuniqueness

end

end OAI
