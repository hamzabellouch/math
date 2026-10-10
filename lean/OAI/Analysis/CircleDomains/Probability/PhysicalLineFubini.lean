import OAI.Analysis.CircleDomains.Sobolev.PhysicalCoordinateLines
import Mathlib.MeasureTheory.Function.LocallyIntegrable

namespace OAI

/-! Fubini on the two physical coordinate line families. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem physicalCoordinatePlane_measurePreserving (i : Fin 2) :
    MeasurePreserving (fun p : ℝ × ℝ => physicalCoordinateLine i p.1 p.2)
      (volume.prod volume) volume := by
  have he : MeasurePreserving euclideanPlaneCoordinates.symm (volume.prod volume) volume := by
    simpa only [← Measure.volume_eq_prod] using euclideanPlaneCoordinates_symm_measurePreserving
  fin_cases i
  · simpa [physicalCoordinateLine,Function.comp_def,Prod.swap] using
      he.comp (Measure.measurePreserving_swap (μ := volume) (ν := volume))
  · simpa [physicalCoordinateLine] using he

 theorem ae_ae_physicalCoordinateLine {p : EuclideanPlane → Prop}
    (hp : ∀ᵐ z ∂volume, p z) (i : Fin 2) :
    ∀ᵐ y ∂volume, ∀ᵐ x ∂volume, p (physicalCoordinateLine i y x) := by
  exact Measure.ae_ae_of_ae_prod ((physicalCoordinatePlane_measurePreserving i).quasiMeasurePreserving.ae hp)

 theorem memLp_physicalCoordinateLine_ae {P : EuclideanPlane → ℝ}
    (hP : Measurable P) (hL : MemLp P 2 volume) (i : Fin 2) :
    ∀ᵐ y ∂volume, MemLp (fun x => P (physicalCoordinateLine i y x)) 2 volume := by
  have hs := (physicalCoordinatePlane_measurePreserving i).integrable_comp_of_integrable hL.integrable_sq
  filter_upwards [hs.prod_right_ae] with y hy
  exact (memLp_two_iff_integrable_sq (hP.comp (physicalCoordinateLine_contDiff i y).continuous.measurable).aestronglyMeasurable).mpr hy

end CircleDomainRigidity

end

end OAI
