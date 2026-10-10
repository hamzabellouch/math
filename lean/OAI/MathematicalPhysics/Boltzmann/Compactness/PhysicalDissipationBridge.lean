import OAI.MathematicalPhysics.Boltzmann.Approximation.RegularizedDissipationBound
import OAI.MathematicalPhysics.Boltzmann.Compactness.EntropyDissipationCoordinates
import OAI.MathematicalPhysics.Boltzmann.Compactness.PhysicalEntropyProduction

namespace OAI

section

/-! # The regularized entropy-dissipation estimate in time-phase coordinates -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

def regularizedKineticDissipation (T b δ : ℝ) (F : Evolution) : ℝ :=
  ∫ z, CollisionCompactness.positiveCutoffProduction b
    (gaussianRegularizedDensity δ (kineticDensity F)) z
    ∂((AnnularEnvelope.timePositionVolume T).prod (volume : Measure (Velocity × Velocity))).prod sphereArea

theorem regularizedKineticDissipation_nonneg {T b δ : ℝ} {F : Evolution}
    (hδ : 0 < δ) (hFn : ∀ t z, 0 ≤ F t z) : 0 ≤ regularizedKineticDissipation T b δ F := by
  apply integral_nonneg
  intro z
  apply CollisionCompactness.positiveCutoffProduction_nonneg
  intro p
  exact add_pos_of_nonneg_of_pos (hFn _ _) (mul_pos hδ (Real.exp_pos _))

theorem physical_regularized_entropy_dissipation_bound (hcarleman : Published.GPV2009CarlemanInput)
    {T q A δ b p : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hA : 0 ≤ A)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hb : 0 ≤ b)
    (hp : 1 < p) (hpi : Integrable (fun v : Velocity => H q v^p))
    {F : Evolution} (hFm : Measurable (fun z : ℝ × Phase => F z.1 z.2))
    (hFn : ∀ t z, 0 ≤ F t z) (hFb : ∀ t z, F t z ≤ A*H q z.2) :
    (∫ z : ℝ × Phase,
      Real.log ((F z.1 z.2+δ*Real.exp (-2*‖z.2.2‖^2))/maxwellian z.2.2)*cutoffPhysicalSource b F z
      ∂(volume.restrict (Icc 0 T)).prod volume) + regularizedKineticDissipation T b δ F ≤
      (δ*entropyErrorCoefficient q A b)*∫ z : (ℝ × Position) × Velocity,
        logarithmicMajorant q (A+tiltConstant) p δ z.2
        ∂(AnnularEnvelope.timePositionVolume T).prod volume := by
  have hbnd := (CollisionCompactness.regularized_entropy_dissipation_bound
    (μ := AnnularEnvelope.timePositionVolume T) hcarleman hq₁ hq₂ hA hδ hδone hb hp hpi
    (hFm.comp MeasurableEquiv.prodAssoc.measurable) (fun z => hFn _ _) (fun z => hFb _ _)).2
  have he := (kineticGrouping_measurePreserving (volume.restrict (Icc 0 T))).symm.integral_comp
    MeasurableEquiv.prodAssoc.symm.measurableEmbedding
    (fun z : (ℝ × Position) × Velocity =>
      Real.log (gaussianRegularizedDensity δ (kineticDensity F) z/maxwellian z.2)*
        CollisionCompactness.collisionSource b (kineticDensity F) z)
  exact (congrArg (fun x => x+regularizedKineticDissipation T b δ F) he).trans_le hbnd

end BoltzmannNonuniqueness

end

end

section

/-! # Physical dissipation depends only on the spacetime density class -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness

theorem physical_dissipation_eq_rate {F : Evolution}
    {g : (ℝ × Position) × Velocity → ℝ} {T : ℝ}
    (hFm : Measurable (fun z : ℝ × Phase => F z.1 z.2)) (hFn : ∀ t p, 0 ≤ F t p)
    (hgm : Measurable g)
    (he : ∀ᵐ z ∂(volume.restrict (Icc 0 T)).prod (volume : Measure Phase),
      F z.1 z.2 = g ((z.1,z.2.1),z.2.2)) :
    (∫⁻ t in Icc (0:ℝ) T, entropyDissipation (F t)) =
      CollisionCompactness.rateDissipation
        ((volume.restrict (Icc 0 T)).prod (volume : Measure Position)) g := by
  have hkin : Measurable (kineticDensity F) := hFm.comp MeasurableEquiv.prodAssoc.measurable
  have hekin : kineticDensity F =ᵐ[
      (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod volume)] g :=
    (kineticGrouping_measurePreserving (volume.restrict (Icc 0 T))).quasiMeasurePreserving.ae he
  rw [← kineticDensity_rateDissipation hFm hFn T]
  exact CollisionCompactness.rateDissipation_congr hkin hgm hekin

end BoltzmannNonuniqueness

end

end

end OAI
