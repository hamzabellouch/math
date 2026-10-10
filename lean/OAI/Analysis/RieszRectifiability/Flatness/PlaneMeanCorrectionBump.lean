import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.BoundedRegionTests
import OAI.Analysis.RieszRectifiability.Rigidity.PlaneHeightDistribution

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter

theorem radialUnitCutoff_affine_restrict {n d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (R : ℝ) (u : Ambient n) :
    radialUnitCutoff a R (a + L u) = radialUnitCutoff (0 : Ambient n) R u := by
  simp only [radialUnitCutoff, dist_eq_norm, add_sub_cancel_left, sub_zero, L.norm_map]

theorem radialUnitCutoff_integrable_on_plane {n d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (R : ℝ) :
    Integrable (radialUnitCutoff a R) (coordinatePlaneMeasure (affinePlaneSection a L)) := by
  rw [coordinatePlaneMeasure_affine_eq_map]
  apply (integrable_map_measure (μ := (volume : Measure (Ambient n)))
    (radialUnitCutoff_lipschitz a R).continuous.aestronglyMeasurable
    (show AEMeasurable (fun u : Ambient n => a + L u) volume from (by fun_prop))).mpr
  have hI : Integrable (radialUnitCutoff (0 : Ambient n) R) volume :=
    (radialUnitCutoff_lipschitz (0 : Ambient n) R).continuous.integrable_of_hasCompactSupport
      (radialUnitCutoff_hasCompactSupport 0 R)
  simpa only [Function.comp_def, radialUnitCutoff_affine_restrict] using! hI

theorem radialUnitCutoff_plane_integral_pos {n d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) :
    0 < ∫ x, radialUnitCutoff a 1 x ∂coordinatePlaneMeasure (affinePlaneSection a L) := by
  have hcont := (radialUnitCutoff_lipschitz (0 : Ambient n) 1).continuous
  have hI : Integrable (radialUnitCutoff (0 : Ambient n) 1) volume :=
    hcont.integrable_of_hasCompactSupport (radialUnitCutoff_hasCompactSupport 0 1)
  have hpos : 0 < ∫ u : Ambient n, radialUnitCutoff 0 1 u :=
    integral_pos_of_integrable_nonneg_nonzero hcont hI
      (fun u => (radialUnitCutoff_bounds 0 1 u).1)
      (show radialUnitCutoff (0 : Ambient n) 1 0 ≠ 0 by norm_num [radialUnitCutoff])
  rw [coordinatePlaneMeasure_affine_eq_map,
    integral_map (show AEMeasurable (fun u : Ambient n => a + L u) volume from (by fun_prop))
      (radialUnitCutoff_lipschitz a 1).continuous.aestronglyMeasurable]
  simpa only [radialUnitCutoff_affine_restrict] using! hpos

end

end RieszRectifiability

end OAI
