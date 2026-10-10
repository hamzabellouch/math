import OAI.Analysis.CircleDomains.Sobolev.RealGradientTransport
import OAI.Analysis.CircleDomains.Topology.OpenDomainRepresentative

namespace OAI

/-! Exact L² preservation for each derivative component under the planar
coordinate change used by finite transfer. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace CircleDomainRigidity

theorem real_chart_partial_eLpNorm {D : Set (ℝ × ℝ)} (hD : IsOpen D)
    {w : EuclideanPlane → ℝ}
    (hw : ContDiffOn ℝ (⊤ : ℕ∞) w (euclideanPlaneCoordinates ⁻¹' D))
    (i : Fin 2)
    (hi : MemLp (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1))
      2 (volume.restrict (euclideanPlaneCoordinates ⁻¹' D))) :
    eLpNorm (fun p => (fderiv ℝ (w ∘ euclideanPlaneCoordinates.symm) p)
        (if i = 0 then (1, 0) else (0, 1))) 2 (volume.restrict D) =
      eLpNorm (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1))
        2 (volume.restrict (euclideanPlaneCoordinates ⁻¹' D)) := by
  have hmp : MeasurePreserving euclideanPlaneCoordinates.symm (volume.restrict D)
      (volume.restrict (euclideanPlaneCoordinates ⁻¹' D)) := by
    convert euclideanPlaneCoordinates_symm_measurePreserving.restrict_preimage
      (hD.preimage euclideanPlaneCoordinates.continuous).measurableSet using 1
    congr 1
  have heq : (fun p => (fderiv ℝ (w ∘ euclideanPlaneCoordinates.symm) p)
        (if i = 0 then (1, 0) else (0, 1))) =ᵐ[volume.restrict D]
      (fun p => (fderiv ℝ w (euclideanPlaneCoordinates.symm p)) (EuclideanSpace.single i 1)) := by
    filter_upwards [ae_restrict_mem hD.measurableSet] with p hp
    exact real_chart_partial_derivative hD hw hp i
  rw [eLpNorm_congr_ae heq]
  exact eLpNorm_comp_measurePreserving hi.aestronglyMeasurable hmp

theorem real_chart_zeroExtension_partial_eLpNorm {D : Set (ℝ × ℝ)} (hD : IsOpen D)
    {w : EuclideanPlane → ℝ}
    (hw : ContDiffOn ℝ (⊤ : ℕ∞) w (euclideanPlaneCoordinates ⁻¹' D))
    (i : Fin 2)
    (hi : MemLp (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1))
      2 (volume.restrict (euclideanPlaneCoordinates ⁻¹' D))) :
    eLpNorm (fun p =>
        (fderiv ℝ ((openZeroExtension (euclideanPlaneCoordinates ⁻¹' D) w) ∘
          euclideanPlaneCoordinates.symm) p) (if i = 0 then (1, 0) else (0, 1)))
        2 (volume.restrict D) =
      eLpNorm (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1))
        2 (volume.restrict (euclideanPlaneCoordinates ⁻¹' D)) := by
  have hΩ := hD.preimage euclideanPlaneCoordinates.continuous
  rw [real_chart_partial_eLpNorm hD (openZeroExtension_contDiffOn hw) i
    (openZeroExtension_gradient_memLp hΩ hi)]
  apply eLpNorm_congr_ae
  filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
  rw [openZeroExtension_fderiv hΩ w hx]

end CircleDomainRigidity

end

end OAI
