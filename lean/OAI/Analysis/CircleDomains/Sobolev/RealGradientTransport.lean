import OAI.Analysis.CircleDomains.Topology.EuclideanPlaneCoordinates
import OAI.Analysis.CircleDomains.Transfer.RankOneFilling
import Mathlib.MeasureTheory.SpecificCodomains.Pi

namespace OAI

/-! Transport the smooth global energy conclusion to the real coordinates
used by the finite transfer construction. -/

open Set Function MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace CircleDomainRigidity

theorem euclideanPlaneCoordinates_symm_axis (i : Fin 2) :
    euclideanPlaneCoordinates.symm (if i = 0 then (1, 0) else (0, 1)) =
      EuclideanSpace.single i 1 := by
  apply euclideanPlaneCoordinates.injective
  fin_cases i <;> simp

theorem real_chart_partial_derivative {D : Set (ℝ × ℝ)} (hD : IsOpen D)
    {w : EuclideanPlane → ℝ}
    (hw : ContDiffOn ℝ (⊤ : ℕ∞) w (euclideanPlaneCoordinates ⁻¹' D))
    {p : ℝ × ℝ} (hp : p ∈ D) (i : Fin 2) :
    (fderiv ℝ (w ∘ euclideanPlaneCoordinates.symm) p) (if i = 0 then (1, 0) else (0, 1)) =
      (fderiv ℝ w (euclideanPlaneCoordinates.symm p)) (EuclideanSpace.single i 1) := by
  have hΩ : IsOpen (euclideanPlaneCoordinates ⁻¹' D) :=
    hD.preimage euclideanPlaneCoordinates.continuous
  have hx : euclideanPlaneCoordinates.symm p ∈ euclideanPlaneCoordinates ⁻¹' D := by
    simpa only [mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using hp
  have hd : DifferentiableAt ℝ w (euclideanPlaneCoordinates.symm p) :=
    (hw.differentiableOn (by simp) _ hx).differentiableAt (hΩ.mem_nhds hx)
  rw [fderiv_comp p hd euclideanPlaneCoordinates.symm.differentiableAt,
    euclideanPlaneCoordinates.symm.fderiv]
  change (fderiv ℝ w (euclideanPlaneCoordinates.symm p))
    (euclideanPlaneCoordinates.symm (if i = 0 then (1, 0) else (0, 1))) = _
  rw [euclideanPlaneCoordinates_symm_axis]

theorem real_chart_gradient_memLp {D : Set (ℝ × ℝ)} (hD : IsOpen D)
    {w : EuclideanPlane → ℝ}
    (hw : ContDiffOn ℝ (⊤ : ℕ∞) w (euclideanPlaneCoordinates ⁻¹' D))
    (henergy : ∀i : Fin 2, MemLp (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1))
      2 (volume.restrict (euclideanPlaneCoordinates ⁻¹' D))) :
    MemLp (FiniteTransfer.planarGradient (w ∘ euclideanPlaneCoordinates.symm))
      2 (volume.restrict D) := by
  have hmp : MeasurePreserving euclideanPlaneCoordinates.symm (volume.restrict D)
      (volume.restrict (euclideanPlaneCoordinates ⁻¹' D)) := by
    convert euclideanPlaneCoordinates_symm_measurePreserving.restrict_preimage
      (hD.preimage euclideanPlaneCoordinates.continuous).measurableSet using 1
    congr 1
  have hi (i : Fin 2) : MemLp
      (fun p => (fderiv ℝ w (euclideanPlaneCoordinates.symm p)) (EuclideanSpace.single i 1))
      2 (volume.restrict D) := (henergy i).comp_measurePreserving hmp
  have hj (i : Fin 2) : MemLp
      (fun p => (fderiv ℝ (w ∘ euclideanPlaneCoordinates.symm) p)
        (if i = 0 then (1, 0) else (0, 1))) 2 (volume.restrict D) := by
    apply (hi i).ae_eq
    filter_upwards [ae_restrict_mem hD.measurableSet] with p hp
    exact (real_chart_partial_derivative hD hw hp i).symm
  apply memLp_prod_iff.mpr
  exact ⟨hj 0, hj 1⟩

end CircleDomainRigidity

end

end OAI
