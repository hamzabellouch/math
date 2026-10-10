import Mathlib
import OAI.Analysis.CoulombIonization.Localization.PacketDensityRadius

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology

namespace CoulombAtom

instance rotationMeasureHaar : Measure.IsHaarMeasure rotationMeasure :=
  inferInstanceAs (Measure.haarMeasure (⊤ : PositiveCompacts SpatialRotation)).IsHaarMeasure

lemma rotation_integral_inverse {f : SpatialRotation → ℝ} (hf : Continuous f) :
    (∫ g, f g⁻¹ ∂rotationMeasure) = ∫ g, f g ∂rotationMeasure := by
  have hi : Integrable (fun q : SpatialRotation × SpatialRotation => f (q.1⁻¹*q.2))
      (rotationMeasure.prod rotationMeasure) :=
    (hf.comp (continuous_fst.inv.mul continuous_snd)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact isCompact_univ (subset_univ _))
  have hx (x : SpatialRotation) : (∫ y, f (x⁻¹*y) ∂rotationMeasure) = ∫ y, f y ∂rotationMeasure :=
    rotation_integral_left f x⁻¹
  have hy (y : SpatialRotation) : (∫ x, f (x⁻¹*y) ∂rotationMeasure) = ∫ x, f x⁻¹ ∂rotationMeasure := by
    rw [←rotation_integral_left (fun x => f (x⁻¹*y)) y]
    simp only [mul_inv_rev,inv_mul_cancel_right]
  calc
    _ = ∫ y, ∫ x, f (x⁻¹*y) ∂rotationMeasure ∂rotationMeasure := by
      simp only [hy,integral_const,probReal_univ,smul_eq_mul,one_mul]
    _ = ∫ x, ∫ y, f (x⁻¹*y) ∂rotationMeasure ∂rotationMeasure := integral_integral_swap hi.swap
    _ = _ := by simp only [hx,integral_const,probReal_univ,smul_eq_mul,one_mul]

lemma rotate_inv_rotate (g : SpatialRotation) (p : Space) :
    rotate g⁻¹ (rotate g p) = p := by
  rw [←rotate_mul,inv_mul_cancel,rotate_one]

lemma rotate_kernel_inverse (g : SpatialRotation) (p z : Space) :
    ‖rotate g p-z‖ = ‖p-rotate g⁻¹ z‖ := by
  rw [←(rotate g⁻¹).norm_map (rotate g p-z),(rotate g⁻¹).map_sub,rotate_inv_rotate]

lemma rotation_kernel_inner (p z : Space) (hz : ‖z‖ < ‖p‖) :
    (∫ g : SpatialRotation, 1/‖rotate g p-z‖ ∂rotationMeasure) = 1/‖p‖ := by
  simp_rw [rotate_kernel_inverse]
  have hc : Continuous (fun g : SpatialRotation => rotate g z) :=
    continuous_subtype_val.clm_apply continuous_const
  have hn (g : SpatialRotation) : ‖p-rotate g z‖ ≠ 0 := by
    intro he
    have he' := sub_eq_zero.mp (norm_eq_zero.mp he)
    have hh : ‖p‖ = ‖z‖ := by rw [he',(rotate g).norm_map]
    linarith
  have hfi : Continuous (fun g : SpatialRotation => (1:ℝ)/‖p-rotate g z‖) :=
    continuous_const.div (continuous_const.sub hc).norm hn
  rw [rotation_integral_inverse hfi]
  exact rotation_kernel_newton z p hz

theorem rotation_kernel_shell (p z : Space) (h : ‖z‖ ≠ ‖p‖) :
    (∫ g : SpatialRotation, 1/‖rotate g p-z‖ ∂rotationMeasure) =
      1/max ‖p‖ ‖z‖ := by
  rcases lt_or_gt_of_ne h with hz | hz
  · rw [max_eq_left hz.le]
    exact rotation_kernel_inner p z hz
  · rw [max_eq_right hz.le]
    simp_rw [norm_sub_rev (rotate _ p) z]
    exact rotation_kernel_newton p z hz

end CoulombAtom

end

end OAI
