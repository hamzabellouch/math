import OAI.Analysis.CircleDomains.Sobolev.SmoothCurveImage
import OAI.Analysis.CircleDomains.Sobolev.SmoothPathIntersections
import OAI.Analysis.CircleDomains.Probability.PathImageOccupation

namespace OAI

/-! Actual arclength occupation pays both the scalar image and distinct
smooth level intersections. Retracing is allowed. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

private theorem restricted_curve_image_hausdorff_le_occupation
    (γ : RectifiablePath ℂ) {D : Set ℂ} (hD : MeasurableSet D) :
    (μH[1] : Measure ℂ).restrict (range γ.val ∩ D) ≤ (pathOccupation γ).restrict D := by
  have h := Measure.restrict_mono_measure (path_image_hausdorff_le_occupation γ) D
  rw [Measure.restrict_restrict hD, inter_comm D] at h
  exact h

theorem smooth_path_image_le_occupation
    (γ : RectifiablePath ℂ) {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D) :
    volume (f '' (range γ.val ∩ D)) ≤
      ∫⁻ z in D, ENNReal.ofReal ‖fderiv ℝ f z‖ ∂pathOccupation γ := by
  have hfin : (μH[1] : Measure ℂ) (range γ.val ∩ D) < ∞ :=
    (measure_mono inter_subset_left).trans_lt
      ((path_hausdorff_length_le_variation γ.val).trans_lt (lt_top_iff_ne_top.mpr γ.property))
  exact (smooth_curve_image_bound hD
    ((isCompact_range γ.val.continuous).isClosed.measurableSet.inter hD.measurableSet)
    inter_subset_right hfin hf).trans
      (lintegral_mono' (restricted_curve_image_hausdorff_le_occupation γ hD.measurableSet)
        (fun _ => le_rfl))

theorem smooth_path_circle_intersections_le_occupation
    (hcoarea : PlanarLipschitzFiberCoarea)
    (γ : RectifiablePath ℂ) {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D) :
    (∫⁻ t in Ico (0 : ℝ) 1,
      pathImageCount (D ∩ {z | (f z : UnitAddCircle) = (t : UnitAddCircle)}) γ.val) ≤
      ∫⁻ z in D, ENNReal.ofReal ‖fderiv ℝ f z‖ ∂pathOccupation γ := by
  have hfin : (μH[1] : Measure ℂ) (range γ.val ∩ D) < ∞ :=
    (measure_mono inter_subset_left).trans_lt
      ((path_hausdorff_length_le_variation γ.val).trans_lt (lt_top_iff_ne_top.mpr γ.property))
  exact (integrated_smooth_circle_pathImageCount_le_differential hcoarea γ.val
    hD hD.measurableSet Subset.rfl hfin hf).trans
      (lintegral_mono' (restricted_curve_image_hausdorff_le_occupation γ hD.measurableSet)
        (fun _ => le_rfl))

end CircleDomainRigidity

end

end OAI
