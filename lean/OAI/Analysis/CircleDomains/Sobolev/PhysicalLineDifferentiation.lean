import OAI.Analysis.CircleDomains.Probability.PhysicalLineFubini

namespace OAI

/-! Differentiating along either coordinate family and the measurable reverse Fubini bridge. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma hasDerivAt_physicalCoordinate_comp {g : EuclideanPlane → ℝ}
    {i : Fin 2} {y t : ℝ} (hg : DifferentiableAt ℝ g (physicalCoordinateLine i y t)) :
    HasDerivAt (fun s => g (physicalCoordinateLine i y s))
      (fderiv ℝ g (physicalCoordinateLine i y t) (EuclideanSpace.single i 1)) t := by
  have h0 := euclideanPlaneCoordinates.symm.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))
  have h1 := euclideanPlaneCoordinates.symm.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t y).prodMk (hasDerivAt_id t))
  fin_cases i
  · simpa [physicalCoordinateLine, Function.comp_def,
      show euclideanPlaneCoordinates.symm (1,0) = EuclideanSpace.single (0:Fin 2) 1 from
        euclideanPlaneCoordinates_symm_axis 0] using hg.hasFDerivAt.comp_hasDerivAt t h0
  · simpa [physicalCoordinateLine, Function.comp_def,
      show euclideanPlaneCoordinates.symm (0,1) = EuclideanSpace.single (1:Fin 2) 1 from
        euclideanPlaneCoordinates_symm_axis 1] using hg.hasFDerivAt.comp_hasDerivAt t h1

lemma ae_of_ae_ae_physicalCoordinateLine {P : EuclideanPlane → Prop}
    (hP : MeasurableSet {p | P p}) (i : Fin 2)
    (h : ∀ᵐ y ∂volume, ∀ᵐ t ∂volume, P (physicalCoordinateLine i y t)) :
    ∀ᵐ p ∂volume, P p := by
  have hm := physicalCoordinatePlane_measurePreserving i
  rw [← hm.map_eq, ae_map_iff hm.measurable.aemeasurable hP]
  exact (Measure.ae_prod_iff_ae_ae (hP.preimage hm.measurable)).mpr h

end CircleDomainRigidity

end

end OAI
