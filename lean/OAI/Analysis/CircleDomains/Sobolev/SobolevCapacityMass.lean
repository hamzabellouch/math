import OAI.Analysis.CircleDomains.Sobolev.SobolevEnergyMeasure

namespace OAI

/-! The mass in the capacity estimate equals the integral of the actual
scalar and two-coordinate gradient densities on the physical plane. -/
open Set Function Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma sobolev_capacity_mass {u : EuclideanPlane → ℝ} (hu : Continuous u)
    (huL2 : MemLp (fun p => u (euclideanPlaneCoordinates.symm p)) 2 volume)
    (V : EuclideanPlane → EuclideanPlane) :
    ENNReal.ofReal (∫ p, (u (euclideanPlaneCoordinates.symm p))^2) +
        coordinateSobolevEnergy V univ =
      ∫⁻ x, ENNReal.ofReal ((u x)^2+(|V x 0|+|V x 1|)^2) := by
  have hi := ofReal_integral_eq_lintegral_ofReal huL2.integrable_sq
    (Eventually.of_forall fun p => sq_nonneg (u (euclideanPlaneCoordinates.symm p)))
  rw [hi, coordinateSobolevEnergy, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← euclideanPlaneCoordinates_symm_measurePreserving.lintegral_comp_emb
    euclideanPlaneCoordinates.symm.toHomeomorph.measurableEmbedding
    (fun x => ENNReal.ofReal ((u x)^2+(|V x 0|+|V x 1|)^2))]
  simp only [ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  exact (lintegral_add_left
    (ENNReal.measurable_ofReal.comp ((hu.comp euclideanPlaneCoordinates.symm.continuous).pow 2).measurable)
    _).symm

end CircleDomainRigidity

end

end OAI
