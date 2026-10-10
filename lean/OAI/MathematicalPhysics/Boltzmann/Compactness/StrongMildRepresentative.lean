import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveMildRepresentative
import OAI.MathematicalPhysics.Boltzmann.Compactness.KineticDensityMeasurable
import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionDissipation

namespace OAI

/-! # Collision integrability for the strong nonnegative mild representative -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

theorem kineticDensity_gain (F : Evolution) (z : ℝ × Phase) :
    TorusFlight.regroup (CollisionCompactness.gainDensity (kineticDensity F)) z =
      gain (F z.1) z.2.1 z.2.2 := by
  rw [TorusFlight.regroup,CollisionCompactness.gainDensity_formula]
  rfl

theorem kineticDensity_loss (F : Evolution) (z : ℝ × Phase) :
    TorusFlight.regroup (CollisionCompactness.lossDensity (kineticDensity F)) z =
      loss (F z.1) z.2.1 z.2.2 := rfl

theorem kineticDensity_collision (F : Evolution) (z : ℝ × Phase) :
    TorusFlight.regroup (MildCollisionSolution.source (kineticDensity F)) z =
      collision (F z.1) z.2.1 z.2.2 := by
  change TorusFlight.regroup (CollisionCompactness.gainDensity (kineticDensity F)) z -
    TorusFlight.regroup (CollisionCompactness.lossDensity (kineticDensity F)) z = _
  rw [kineticDensity_gain,kineticDensity_loss]
  rfl

namespace MildCollisionSolution

variable {T : ℝ} {f₀ : Density} {g : (ℝ × Position) × Velocity → ℝ}

theorem positiveDensity_measurable (S : MildCollisionSolution T f₀ g)
    (hf₀ : Measurable f₀) : Measurable (kineticDensity (positiveEvolution T f₀ g)) :=
  (S.positiveEvolution_measurable hf₀).comp MeasurableEquiv.prodAssoc.measurable

theorem positiveDensity_eq_ae (S : MildCollisionSolution T f₀ g) :
    g =ᵐ[(AnnularEnvelope.timePositionVolume T).prod volume]
      kineticDensity (positiveEvolution T f₀ g) :=
  (kineticGrouping_measurePreserving (volume.restrict (Icc 0 T))).quasiMeasurePreserving.ae
    S.positiveEvolution_eq_ae

theorem positiveDensity_pair_integrable (S : MildCollisionSolution T f₀ g)
    (hf₀ : Measurable f₀) :
    Integrable (CollisionCompactness.pairDensity (kineticDensity (positiveEvolution T f₀ g)))
      ((AnnularEnvelope.timePositionVolume T).prod volume) :=
  S.pair_integrable.congr (CollisionCompactness.pairDensity_congr
    S.measurable (S.positiveDensity_measurable hf₀) S.positiveDensity_eq_ae)

theorem positiveEvolution_strongEarly (S : MildCollisionSolution T f₀ g)
    (hT : 0 < T) (hf₀m : Measurable f₀) (hf₀i : Integrable f₀) :
    StrongEarly T (positiveEvolution T f₀ g) := by
  let F := positiveEvolution T f₀ g
  have hm := S.positiveDensity_measurable hf₀m
  have hn : ∀ z, 0 ≤ kineticDensity F z := fun z => positiveEvolution_nonnegative _ _
  have hi := CollisionCompactness.gainLoss_integrable hm hn (S.positiveDensity_pair_integrable hf₀m)
  have hgain := (kineticGrouping_measurePreserving (volume.restrict (Icc 0 T))).symm.integrable_comp_of_integrable hi.1
  have hloss := (kineticGrouping_measurePreserving (volume.restrict (Icc 0 T))).symm.integrable_comp_of_integrable hi.2
  refine ⟨hT,fun _ ht => S.positiveEvolution_strong_continuity hT.le hf₀m hf₀i ht,?_,?_⟩
  · change Integrable _ _
    rw [← phaseInterval_measure]
    have he : (CollisionCompactness.gainDensity (kineticDensity (positiveEvolution T f₀ g)) ∘
        MeasurableEquiv.prodAssoc.symm) =
        (fun z : ℝ × Phase => gain (positiveEvolution T f₀ g z.1) z.2.1 z.2.2) := by
      funext z
      exact kineticDensity_gain _ z
    rw [he] at hgain
    exact hgain
  · change Integrable _ _
    rw [← phaseInterval_measure]
    exact hloss

theorem positiveEvolution_collision_fibers (S : MildCollisionSolution T f₀ g)
    (hf₀m : Measurable f₀) :
    ∀ᵐ p ∂volume.restrict (boundedTimes T),
      Integrable (fun q : Velocity × Sphere =>
        collisionKernel p.2.2 q.1 q.2 *
          positiveEvolution T f₀ g p.1 (p.2.1,scatterLeft p.2.2 q.1 q.2) *
          positiveEvolution T f₀ g p.1 (p.2.1,scatterRight p.2.2 q.1 q.2))
        ((volume : Measure Velocity).prod sphereArea) ∧
      Integrable (fun q : Velocity × Sphere =>
        collisionKernel p.2.2 q.1 q.2 * positiveEvolution T f₀ g p.1 p.2 *
          positiveEvolution T f₀ g p.1 (p.2.1,q.1))
        ((volume : Measure Velocity).prod sphereArea) := by
  have h := CollisionCompactness.collision_fibers (S.positiveDensity_measurable hf₀m)
    (fun z => positiveEvolution_nonnegative z.1.1 (z.1.2,z.2))
    (S.positiveDensity_pair_integrable hf₀m)
  rw [← phaseInterval_measure]
  exact (kineticGrouping_measurePreserving (volume.restrict (Icc 0 T))).symm.quasiMeasurePreserving.ae h

end MildCollisionSolution
end BoltzmannNonuniqueness

end

end OAI
