import OAI.Analysis.CircleDomains.Sobolev.LocallySobolevCoordinateFTC

namespace OAI

/-! Integrability of the actual local weak partials on compact coordinate sets. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma local_partial_integrableOn_compact {V : EuclideanPlane → EuclideanPlane}
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R)))
    {K : Set EuclideanPlane} (hK : IsCompact K) (i : Fin 2) :
    IntegrableOn (fun p => V p i) K volume := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_ball 0
  let : IsFiniteMeasure (volume.restrict (ball (0 : EuclideanPlane) R)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hi : IntegrableOn (fun p => V p i) (ball 0 R) volume :=
    (hLp R i).integrable (by norm_num)
  exact hi.mono_set hR

lemma local_partial_coordinate_integrableOn {V : EuclideanPlane → EuclideanPlane}
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R)))
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (i : Fin 2) :
    IntegrableOn (fun p => V (euclideanPlaneCoordinates.symm p) i) K volume := by
  have hKC := hK.image euclideanPlaneCoordinates.symm.continuous
  have hI := local_partial_integrableOn_compact hLp hKC i
  have hP := euclideanPlaneCoordinates_symm_measurePreserving.restrict_preimage
    hKC.measurableSet
  have hpre : euclideanPlaneCoordinates.symm ⁻¹' (euclideanPlaneCoordinates.symm '' K) = K :=
    Set.preimage_image_eq K euclideanPlaneCoordinates.symm.injective
  rw [hpre] at hP
  exact hP.integrable_comp_of_integrable hI

end CircleDomainRigidity

end

end OAI
